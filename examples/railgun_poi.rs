use clap::Parser;
use halo2_base::{
    gates::{GateChip, GateInstructions},
    utils::ScalarField,
    AssignedValue, Context,
};

use halo2_scaffold::scaffold::{cmd::Cli, run};
use poseidon::PoseidonChip;
use serde::{Deserialize, Serialize};

const R_P: [usize; 16] = [56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68];

const MERKLE_TREE_DEPTH: usize = 16;
const N_INPUTS: usize = 2;
const N_OUTPUTS: usize = 2;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[allow(non_snake_case)]
pub struct CircuitInput {
    // Public inputs:
    pub allowListRoot: String,
    pub messageHashesRoot: String, // TODO: Add messageHashes history accumulator to recieved transactions.
    // TODO: If this is a aggregation from our own inputs, prove that messageHashesRoot's are the same, allowList's are the same, and recieve the aggAllowList,
    // TOOD: If this is a aggregation from other people's inputs, prove that messageHashesRoot's are in the massageHashes histort accumulator, allowList's are the same(object to change), add the output to the aggAllowList,

    // Other way around would be, recieved transactions will be merkle tree'd first to aggAllowList

    // Private inputs:
    pub merkleRoot: String,
    pub boundParamsHash: String,
    pub nullifiers: [String; N_INPUTS],
    pub commitmentsOut: [String; N_OUTPUTS],

    // 1. Current transaction is in messageHashesRoot (Proving that this is a valid transaction.)
    pub messageHashPathElements: [String; MERKLE_TREE_DEPTH],
    pub messageHashPathIndices: [String; MERKLE_TREE_DEPTH],

    // 2. All the inputs are in previous proof's AggAllowList (This is a currently private input)
    pub aggAllowListRoot: String, // This is the aggregated allow list root from the previous proofs
    //  2.1 we need to compute commitments of the inputs
    pub mpkOut: String,               // This is the master public key
    pub randomIn: [String; N_INPUTS], // This is the random value used to generate the commitment npkIn.out = Poseidon(mpkOut, randomIn[i])

    pub token: String,               // This is the token that is being transferred
    pub valueIn: [String; N_INPUTS], // This is the value of the token being transferred, commitment = Poseidon(npkIn.out, token, valueIn[i])

    // 2.2 We need to prove that these inputs are in aggAllowListRoot
    pub aggAllowListPathElements: [[String; MERKLE_TREE_DEPTH]; N_INPUTS],
    pub aggAllowListPathIndices: [[String; MERKLE_TREE_DEPTH]; N_INPUTS],

    // 3. Adds the selected commitment output to the aggAllowListRoot
    //  3.1 Proves that with empty leaf value, the root is aggAllowListRoot
    pub emptyLeafPathElements: [String; MERKLE_TREE_DEPTH],
    pub emptyLeafPathIndices: [String; MERKLE_TREE_DEPTH],

    // 3.2 selects the commitment output
    pub selectedCommitmentIndex: String,

    //  3.2 Proves that with the commitment output, the root is newAggAllowListRoot
    pub newAggAllowListRoot: String,
}

fn cond_swap<F: ScalarField>(
    ctx: &mut Context<F>,
    gate: &impl GateInstructions<F>,
    a: AssignedValue<F>,
    b: AssignedValue<F>,
    swap: AssignedValue<F>,
) -> (AssignedValue<F>, AssignedValue<F>) {
    // Compute (1 - swap) * a and (1 - swap) * b
    let swap_a = gate.mul_not(ctx, swap.clone(), a.clone());
    let swap_b = gate.mul_not(ctx, swap.clone(), b.clone());

    // Compute (1 - swap) * a + swap * b and (1 - swap) * b + swap * a
    let l = gate.mul_add(ctx, swap.clone(), b, swap_a);
    let r = gate.mul_add(ctx, swap, a, swap_b);

    return (l, r);
}

fn poseidon_hash_two<F: ScalarField>(
    ctx: &mut Context<F>,
    gate: &impl GateInstructions<F>,
    inputs: &[AssignedValue<F>; 2],
) -> AssignedValue<F> {
    let zero = ctx.load_constant(F::zero()); // circomlib's poseidon hash requires zero constant at the beginning
    let mut hasher = PoseidonChip::<F, 3, 2>::new(ctx, 8, R_P[1]).unwrap();
    hasher.update(&[zero, inputs[0], inputs[1]]);
    return hasher.squeeze(ctx, gate).unwrap();
}

fn poseidon_hash_three<F: ScalarField>(
    ctx: &mut Context<F>,
    gate: &impl GateInstructions<F>,
    inputs: &[AssignedValue<F>; 3],
) -> AssignedValue<F> {
    let zero = ctx.load_constant(F::zero()); // circomlib's poseidon hash requires zero constant at the beginning
    let mut hasher = PoseidonChip::<F, 4, 3>::new(ctx, 8, R_P[2]).unwrap();
    hasher.update(&[zero, inputs[0], inputs[1], inputs[2]]);
    return hasher.squeeze(ctx, gate).unwrap();
}

fn merkle_proof<F: ScalarField>(
    ctx: &mut Context<F>,
    gate: &impl GateInstructions<F>,
    path_elements: &[AssignedValue<F>; MERKLE_TREE_DEPTH],
    path_indices: &[AssignedValue<F>; MERKLE_TREE_DEPTH],
    leaf: AssignedValue<F>,
    root: AssignedValue<F>,
) {
    let mut cur_leaf = leaf.clone();
    for i in 0..MERKLE_TREE_DEPTH {
        let (l, r) = cond_swap(ctx, gate, cur_leaf, path_elements[i], path_indices[i]);
        cur_leaf = poseidon_hash_two(ctx, gate, &[l, r]);
    }
    ctx.constrain_equal(&cur_leaf, &root);
}

fn proof_of_innocence<F: ScalarField>(
    ctx: &mut Context<F>,
    input: CircuitInput,
    make_public: &mut Vec<AssignedValue<F>>,
) {
    macro_rules! load_witness_from_str {
        ($x: expr) => {
            ctx.load_witness(
                F::from_str_vartime(&$x).expect("deserialize field element should not fail"),
            )
        };
    }

    macro_rules! load_witness_from_str_arr {
        ($x: expr) => {
            $x.map(|x| {
                ctx.load_witness(
                    F::from_str_vartime(&x).expect("deserialize field element should not fail"),
                )
            })
        };
    }
    // STEP 0: Load the inputs
    let allow_list_root = load_witness_from_str!(input.allowListRoot);
    let message_hashes_root = load_witness_from_str!(input.messageHashesRoot);
    let bound_params_hash = load_witness_from_str!(input.boundParamsHash);
    let agg_allow_list_root = load_witness_from_str!(input.aggAllowListRoot);
    let new_agg_allow_list_root = load_witness_from_str!(input.newAggAllowListRoot);
    let empty_leaf_path_elements = load_witness_from_str_arr!(input.emptyLeafPathElements);
    let empty_leaf_path_indices = load_witness_from_str_arr!(input.emptyLeafPathIndices);
    let selected_commitment_index = load_witness_from_str!(input.selectedCommitmentIndex);
    let mpk_out = load_witness_from_str!(input.mpkOut);
    let token = load_witness_from_str!(input.token);
    let random_in = load_witness_from_str_arr!(input.randomIn);
    let value_in = load_witness_from_str_arr!(input.valueIn);
    let agg_allow_list_path_elements =
        input.aggAllowListPathElements.map(|x| load_witness_from_str_arr!(x));
    let agg_allow_list_path_indices =
        input.aggAllowListPathIndices.map(|x| load_witness_from_str_arr!(x));
    let message_hash_path_elements = load_witness_from_str_arr!(input.messageHashPathElements);
    let message_hash_path_indices = load_witness_from_str_arr!(input.messageHashPathIndices);
    let commitments_out = load_witness_from_str_arr!(input.commitmentsOut);
    let nullifiers = load_witness_from_str_arr!(input.nullifiers);

    // STEP 0: make public inputs
    make_public.extend([
        allow_list_root,
        message_hashes_root,
        agg_allow_list_root, // TODO: Make this private on recursion, or add blinding factor
    ]);
    // create a new gate
    let gate: GateChip<F> = GateChip::<F>::default();

    // STEP 1: Current transaction is in messageHashesRoot (Proving that this is a valid transaction.)
    let zero = ctx.load_constant(F::zero());
    const RATE: usize = N_INPUTS + N_OUTPUTS + 2;
    const T: usize = RATE + 1;
    let mut message_hasher = PoseidonChip::<F, T, RATE>::new(ctx, 8, R_P[T - 2]).unwrap();
    let mut inputs = [zero; RATE];
    inputs[0] = zero;
    inputs[1] = message_hashes_root;
    inputs[2] = bound_params_hash;
    for i in 0..N_INPUTS {
        inputs[3 + i] = nullifiers[i];
    }
    for i in 0..N_OUTPUTS {
        inputs[3 + N_INPUTS + i] = commitments_out[i];
    }
    message_hasher.update(&inputs);
    let message_hash = message_hasher.squeeze(ctx, &GateChip::<F>::default()).unwrap();

    merkle_proof(ctx, &gate, &message_hash_path_elements, &message_hash_path_indices, message_hash, message_hashes_root);

    // STEP 2: Check that the nullifiers are in the allow list
    let note_commitments_in: Vec<AssignedValue<F>> = (0..N_INPUTS)
        .map(|i|
            {
                let npk = poseidon_hash_two(ctx, &gate, &[mpk_out, random_in[i]]);
                poseidon_hash_three(ctx, &gate, &[npk, token, value_in[i]])
            }
        )
        .collect();
    
    for i in 0..N_INPUTS {
        merkle_proof(ctx, &gate, &agg_allow_list_path_elements[i], &agg_allow_list_path_indices[i], note_commitments_in[i], allow_list_root);
    }

    // STEP 3
    // let outCommitment = commitment_selector(ctx, &gate, &commitments_out, selected_commitment_index);
    let out_commitment = gate.select_from_idx(ctx, commitments_out, selected_commitment_index);
    let zero_leaf = ctx.load_constant(F::from_str_vartime("2051258411002736885948763699317990061539314419500486054347250703186609807356").expect("deserialize field element should not fail")); // bytes32(uint256(keccak256("Railgun")) % SNARK_SCALAR_FIELD);

    merkle_proof(ctx, &gate, &empty_leaf_path_elements, &empty_leaf_path_indices, zero_leaf, agg_allow_list_root);
    merkle_proof(ctx, &gate, &empty_leaf_path_elements, &empty_leaf_path_indices, out_commitment, new_agg_allow_list_root);

    // make public
    make_public.extend([
        new_agg_allow_list_root,
    ]);

}

fn main() {
    env_logger::init();

    let args = Cli::parse();
    run(proof_of_innocence, args);
}
