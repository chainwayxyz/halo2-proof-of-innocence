use clap::Parser;
use halo2_base::{
    gates::{GateChip, GateInstructions},
    utils::ScalarField,
    AssignedValue, Context,
};

use halo2_scaffold::scaffold::{cmd::Cli, run};
use poseidon::PoseidonChip;
use serde::{Deserialize, Serialize};

// const T: usize = 2;
// const RATE: usize = 1;
// const R_F: usize = 8;
const R_P: [usize; 16] = [56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68];

const MERKLE_TREE_DEPTH: usize = 16;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[allow(non_snake_case)]
pub struct CircuitInput {
    pub root: String,
    pub allowListRoot: String,
    pub nullifier: String,
    pub nullifierHash: String,
    pub secret: String,
    pub pathElements: [String; MERKLE_TREE_DEPTH],
    pub pathIndices: [String; MERKLE_TREE_DEPTH],
    pub allowListPathElements: [String; MERKLE_TREE_DEPTH],
    pub allowListPathIndices: [String; MERKLE_TREE_DEPTH],
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

fn merkle_proof<F:ScalarField>(
    ctx: &mut Context<F>,
    gate: &impl GateInstructions<F>,
    path_elements: &[AssignedValue<F>; MERKLE_TREE_DEPTH],
    path_indices: &[AssignedValue<F>; MERKLE_TREE_DEPTH],
    leaf: AssignedValue<F>,
    root: AssignedValue<F>,
) {
    let zero = ctx.load_constant(F::zero());
    let mut cur_leaf = leaf.clone();
    for i in 0..MERKLE_TREE_DEPTH {
        let mut hasher = PoseidonChip::<F, 3, 2>::new(ctx, 8, R_P[1]).unwrap();
        let (l, r) = cond_swap(ctx, gate, cur_leaf, path_elements[i], path_indices[i]);
        hasher.update(&[zero, l, r]);
        cur_leaf = hasher.squeeze(ctx, gate).unwrap();
    }
    ctx.constrain_equal(&cur_leaf, &root);
}

fn proof_of_innocence<F: ScalarField>(
    ctx: &mut Context<F>,
    input: CircuitInput,
    make_public: &mut Vec<AssignedValue<F>>,
) {
    let root = ctx.load_witness(
        F::from_str_vartime(&input.root).expect("deserialize field element should not fail"),
    );

    let nullifier = ctx.load_witness(
        F::from_str_vartime(&input.nullifier).expect("deserialize field element should not fail"),
    );
    let nullifier_hash = ctx.load_witness(
        F::from_str_vartime(&input.nullifierHash)
            .expect("deserialize field element should not fail"),
    );
    let secret = ctx.load_witness(
        F::from_str_vartime(&input.secret).expect("deserialize field element should not fail"),
    );

    let path_elements = input.pathElements.map(|x| {
        ctx.load_witness(
            F::from_str_vartime(&x).expect("deserialize field element should not fail"),
        )
    });

    let path_indices = input.pathIndices.map(|x| {
        ctx.load_witness(
            F::from_str_vartime(&x).expect("deserialize field element should not fail"),
        )
    });

    let allow_list_path_elements = input.allowListPathElements.map(|x| {
        ctx.load_witness(
            F::from_str_vartime(&x).expect("deserialize field element should not fail"),
        )
    });

    let allow_list_path_indices = input.allowListPathIndices.map(|x| {
        ctx.load_witness(
            F::from_str_vartime(&x).expect("deserialize field element should not fail"),
        )
    });

    let allow_list_root = ctx.load_witness(
        F::from_str_vartime(&input.allowListRoot)
            .expect("deserialize field element should not fail"),
    );

    make_public.push(nullifier_hash);
    make_public.push(root);
    make_public.push(allow_list_root);

    let gate = GateChip::<F>::default();
    let zero = ctx.load_constant(F::zero());

    let mut poseidon = PoseidonChip::<F, 2, 1>::new(ctx, 8, R_P[0]).unwrap();
    poseidon.update(&[zero, nullifier]);
    let hash = poseidon.squeeze(ctx, &gate).unwrap();

    ctx.constrain_equal(&hash, &nullifier_hash);

    let mut commitment_hasher = PoseidonChip::<F, 3, 2>::new(ctx, 8, R_P[1]).unwrap();
    commitment_hasher.update(&[zero, nullifier, secret]);
    let commitment = commitment_hasher.squeeze(ctx, &gate).unwrap();

    merkle_proof(ctx, &gate, &path_elements, &path_indices, commitment, root);
    merkle_proof(ctx, &gate, &allow_list_path_elements, &allow_list_path_indices, commitment, allow_list_root);
}

fn main() {
    env_logger::init();

    let args = Cli::parse();
    run(proof_of_innocence, args);
}
