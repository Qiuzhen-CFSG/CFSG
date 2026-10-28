/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/IcosianGlueMonomial.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Codes.IcosianGlueStabilizer
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# IcosianGlueMonomial

Coordinate permutations extend the block stabilizer to the monomial glue
stabilizer. A semidirect-product description gives its order, 288 over a
field with four elements.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/IcosianGlueMonomial.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports, public module boundaries, and
proof syntax updated for the local APIs and linters.
-/

@[expose] public section


noncomputable section
namespace Atlas.Codes
open Matrix
open scoped BigOperators

/-- Reindexing the three actual blocks, with their internal coordinates retained. -/
def icosianGluePermute {F : Type*} (p : Equiv.Perm (Fin 3)) (x : IcosianGlueWord F) :
    IcosianGlueWord F := fun i => x (p.symm i)

theorem icosianGlue_uniform {F : Type*} [Field F] (x : IcosianGlueWord F) :
    x ∈ icosianGlue F ↔ (∀ i,x i 1=x 2 1) ∧ (∑ i : Fin 3,x i 0)=0 := by
  constructor
  · rintro ⟨h0,h1,h2⟩
    refine ⟨?_,?_⟩
    · intro i; fin_cases i
      · exact h0.trans h1
      · exact h1
      · rfl
    · simpa only [Fin.sum_univ_three] using h2
  · rintro ⟨h0,h1⟩
    exact ⟨(h0 0).trans (h0 1).symm,h0 1,by simpa only [Fin.sum_univ_three] using h1⟩

theorem icosianGluePermute_mem {F : Type*} [Field F] (p : Equiv.Perm (Fin 3))
    (x : IcosianGlueWord F) (hx : x ∈ icosianGlue F) :
    icosianGluePermute p x ∈ icosianGlue F := by
  rw [icosianGlue_uniform] at hx ⊢
  refine ⟨fun i => (hx.1 (p.symm i)).trans (hx.1 (p.symm 2)).symm,?_⟩
  change (∑ i : Fin 3,x (p.symm i) 0)=0
  rw [show (∑ i : Fin 3,x (p.symm i) 0)=(∑ i : Fin 3,x i 0) from
    Equiv.sum_comp p.symm (fun i => x i 0)]
  exact hx.2

@[simp] theorem icosianGluePermute_mem_iff {F : Type*} [Field F]
    (p : Equiv.Perm (Fin 3)) (x : IcosianGlueWord F) :
    icosianGluePermute p x ∈ icosianGlue F ↔ x ∈ icosianGlue F := by
  constructor
  · intro h
    have hh := icosianGluePermute_mem p.symm _ h
    simpa [icosianGluePermute] using hh
  · exact icosianGluePermute_mem p x

def icosianGlueBlockPermutations {F : Type*} [Field F] :
    Equiv.Perm (Fin 3) →* MulAut (IcosianGlueBlocks F) where
  toFun p :=
    { toFun := fun g i => g (p.symm i)
      invFun := fun g i => g (p i)
      left_inv := by intro g; funext i; simp
      right_inv := by intro g; funext i; simp
      map_mul' := by intros; rfl }
  map_one' := by ext g i; rfl
  map_mul' p q := by ext g i; rfl

abbrev IcosianGlueMonomialGroup (F : Type*) [Field F] :=
  SemidirectProduct (IcosianGlueBlocks F) (Equiv.Perm (Fin 3)) icosianGlueBlockPermutations

instance icosianGlueMonomialAction {F : Type*} [Field F] :
    MulAction (IcosianGlueMonomialGroup F) (IcosianGlueWord F) where
  smul g x := g.left • icosianGluePermute g.right x
  one_smul x := by
    funext i
    change (1 : SpecialLinearGroup (Fin 2) F) • x i=x i
    exact one_smul _ _
  mul_smul g h x := by
    funext i
    change (g.left i * h.left (g.right.symm i)) • x (h.right.symm (g.right.symm i))=
      g.left i • (h.left (g.right.symm i) • x (h.right.symm (g.right.symm i)))
    exact mul_smul _ _ _

theorem icosianGlueMonomial_smul {F : Type*} [Field F]
    (g : IcosianGlueMonomialGroup F) (x : IcosianGlueWord F) :
    g • x=g.left • icosianGluePermute g.right x := rfl

/-- The full stabilizer inside SL2(F)^3 semidirect S3, acting on the actual glue. -/
def icosianGlueMonomialStabilizer (F : Type*) [Field F] :
    Subgroup (IcosianGlueMonomialGroup F) where
  carrier := {g | ∀ x : IcosianGlueWord F,g • x ∈ icosianGlue F ↔ x ∈ icosianGlue F}
  one_mem' := by intro x; simp
  mul_mem' := by intro g h hg hh x; rw [mul_smul,hg,hh]
  inv_mem' := by
    intro g hg x
    have h := hg (g⁻¹ • x)
    simpa only [smul_inv_smul] using h.symm

theorem icosianGlueMonomialStabilizer_iff {F : Type*} [Field F] [Finite F]
    (g : IcosianGlueMonomialGroup F) :
    g ∈ icosianGlueMonomialStabilizer F ↔ g.left ∈ icosianGlueBlockStabilizer F := by
  constructor
  · intro hg x hx
    have h := (hg (icosianGluePermute g.right.symm x)).mpr
      (icosianGluePermute_mem g.right.symm x hx)
    simpa [icosianGlueMonomial_smul,icosianGluePermute] using h
  · intro hg x
    rw [icosianGlueMonomial_smul,icosianGlue_preserves_iff_mem g.left hg,
      icosianGluePermute_mem_iff]

def icosianGlueMonomialStabilizerEquiv {F : Type*} [Field F] [Finite F] :
    icosianGlueMonomialStabilizer F ≃
      icosianGlueBlockStabilizer F × Equiv.Perm (Fin 3) where
  toFun g := (⟨g.val.left,(icosianGlueMonomialStabilizer_iff g.val).mp g.property⟩,g.val.right)
  invFun p := ⟨⟨p.1.val,p.2⟩,(icosianGlueMonomialStabilizer_iff _).mpr p.1.property⟩
  left_inv g := by apply Subtype.ext; rfl
  right_inv p := rfl

theorem icosianGlueMonomialStabilizer_card {F : Type*} [Field F] [Finite F] :
    Nat.card (icosianGlueMonomialStabilizer F)=6*(Nat.card F-1)*Nat.card F^2 := by
  rw [Nat.card_congr (icosianGlueMonomialStabilizerEquiv (F := F)),Nat.card_prod,
    icosianGlueBlockStabilizer_card]
  have h : Nat.card (Equiv.Perm (Fin 3))=6 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    norm_num
  rw [h]
  ring

theorem icosianGlueMonomialStabilizer_card_four {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F=4) : Nat.card (icosianGlueMonomialStabilizer F)=288 := by
  rw [icosianGlueMonomialStabilizer_card,hF]
  norm_num

end Atlas.Codes
