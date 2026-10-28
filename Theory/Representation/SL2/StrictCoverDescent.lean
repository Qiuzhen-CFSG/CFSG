module
public import Theory.Representation.NormalSylowSeed
public import Theory.Representation.SL2.ExtensionFieldDegree

/-!
# Strict field-square descent through a normal two-group kernel

For a cover of SL₂(2ⁿ), n > 1, every residual-moving section contributes
at least n to the fixed codimension of an actor with nonzero two-group
image. Below 2n, a simple submodule therefore has residual-fixed quotient.
The normal Sylow seed criterion makes that submodule the whole module.
The normal two-group kernel consequently acts trivially, giving descent
on the original vectors, without assuming descent in the comparison.

Source application: DGS, Groups and Graphs (1985), the lower comparisons
in 8.6--8.7, printed p.140; the constituent bound is Niles (1979), Lemma 4.3.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups
namespace Representation.SL2
variable {H F W : Type*} [Group H] [Finite H]
  [Field F] [Finite F] [CharP F 2]
  [AddCommGroup W] [Module (ZMod 2) W] [Finite W] [Nontrivial W]

private theorem strict_cover_irreducible
    (ρ : Representation (ZMod 2) H W) (q : H →* SL(2,F))
    (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (B : Subgroup H) (S : Sylow 2 H)
    (hS : q.ker ⊔ B = S) (hnormal : (S : Subgroup H) ≤ normalizer (B : Set H))
    (hB : B.map q ≠ ⊥)
    (hzero : fixedSpace ρ (pResidual 2 H) = ⊥)
    (hgen : GeneratedByFixedSpace ρ B)
    (A : Subgroup H) (hA : IsPGroup 2 (A.map q)) (hne : A.map q ≠ ⊥)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (hstrict : fixedCodim ρ A < 2*n) : ρ.IsIrreducible := by
  obtain ⟨I,hI⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρ
  let : I.toRepresentation.IsIrreducible := hI
  let : Nontrivial I.toSubmodule := Subrepresentation.irreducible_module_nontrivial I.toRepresentation
  have hIzero : fixedSpace I.toRepresentation (pResidual 2 H) = ⊥ := by
    apply bot_unique
    intro w hw
    apply Subtype.ext
    exact hzero.le (fun a => congrArg Subtype.val (hw a))
  have hImove : fixedSpace I.toRepresentation (pResidual 2 H) ≠ ⊤ := by
    rw [hIzero]
    exact bot_ne_top
  have hlow := extension_fixedCodim_lower q hq hp I.toRepresentation hImove A hA hne hn hF
  have hquot : pResidual 2 H ≤ I.quotientRepresentation.ker := by
    by_contra hh
    let : Finite (W ⧸ I.toSubmodule) := Finite.of_surjective _ I.toSubmodule.mkQ_surjective
    have hmove : fixedSpace I.quotientRepresentation (pResidual 2 H) ≠ ⊤ := by
      intro he
      apply hh
      intro k hk
      apply LinearMap.ext
      intro w
      exact (show w ∈ fixedSpace I.quotientRepresentation (pResidual 2 H) from
        he.symm ▸ Submodule.mem_top) ⟨k,hk⟩
    have hlowQ := extension_fixedCodim_lower q hq hp I.quotientRepresentation hmove A hA hne hn hF
    have hsum := fixedCodim_quotient_add_subrepresentation_le ρ I A
    omega
  have hk : q.ker ≤ I.toRepresentation.ker := normal_p_subgroup_le_ker I.toRepresentation q.ker hp
  have hBp : IsPGroup 2 (B.map q) := by
    have hBS : B ≤ (S : Subgroup H) := hS ▸ le_sup_right
    exact (S.isPGroup'.of_injective (Subgroup.inclusion hBS) (Subgroup.inclusion_injective hBS)).map q
  have hBn : ¬ I.toSubmodule ≤ fixedSpace ρ B := by
    intro he
    have hf : fixedSpace I.toRepresentation B = ⊤ := by
      apply top_unique
      intro w _ b
      exact Subtype.ext (he w.property b)
    have hl := extension_fixedCodim_lower q hq hp I.toRepresentation hImove B hBp hB hn hF
    rw [fixedCodim,hf] at hl
    have hz : Module.finrank (ZMod 2) (I.toSubmodule ⧸ (⊤ : Submodule (ZMod 2) I.toSubmodule)) = 0 := Module.finrank_zero_of_subsingleton
    rw [hz] at hl
    omega
  have htop := constituent_eq_top_of_normal_sylow_seed ρ I q.ker B S hS hnormal hk hBn
    hquot hzero hgen
  subst I
  let e : (⊤ : Subrepresentation ρ).toRepresentation ≃ₗ ρ :=
    { Submodule.topEquiv with isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }
  exact e.irreducible_euqiv.mp hI
/-- A strict field-square displacement bound constructs an irreducible
quotient action on the original vectors. The actor may be smaller than a
Sylow; the separate normal Sylow seed prevents a residual-trivial quotient. -/
theorem strict_cover_descent
    (ρ : Representation (ZMod 2) H W) (q : H →* SL(2,F))
    (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (B : Subgroup H) (S : Sylow 2 H)
    (hS : q.ker ⊔ B = S) (hnormal : (S : Subgroup H) ≤ normalizer (B : Set H))
    (hB : B.map q ≠ ⊥)
    (hzero : fixedSpace ρ (pResidual 2 H) = ⊥)
    (hgen : GeneratedByFixedSpace ρ B)
    (A : Subgroup H) (hA : IsPGroup 2 (A.map q)) (hne : A.map q ≠ ⊥)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (hstrict : Nat.card (W ⧸ fixedSpace ρ A) < Nat.card F ^ 2) :
    ∃ σ : Representation (ZMod 2) SL(2,F) W,
      (∀ l, σ (q l) = ρ l) ∧ σ.IsIrreducible := by
  let : Finite (W ⧸ fixedSpace ρ A) := Finite.of_surjective _ (fixedSpace ρ A).mkQ_surjective
  have hd : fixedCodim ρ A < 2*n := by
    rw [hF,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,←pow_mul] at hstrict
    have hh := (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hstrict
    change fixedCodim ρ A < _ at hh
    omega
  let : ρ.IsIrreducible := strict_cover_irreducible ρ q hq hp B S hS hnormal hB
    hzero hgen A hA hne hn hF hd
  exact exists_irreducible_descent_of_pGroup_kernel ρ q hq hp

end Representation.SL2
