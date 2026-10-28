module
public import Theory.Representation.RankOne.QuadraticRecognition.SL2Sylow
public import Theory.SpecificGroups.SL2.Affine.Action

/-!+# Natural-module consequences with unchanged matrix actors

The coordinates obtained in the full-Sylow branch give transitivity on
nonzero vectors and hence irreducibility over GF(2), not just over the
defining field. Complementary Sylow fixed spaces give the source fixed
orders, including fixed spaces of individual nonidentity Sylow elements.
These are the properties used after DGS85 (5.12), printed p.113.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.RankOne.QuadraticRecognition
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The three clauses in DGS85's definition on p.112. The action is already
on the actual SL₂ field model; noncentrality concerns its derived subgroup. -/
@[expose] def IsSourceNatural (ρ : Representation (ZMod 2) SL(2,F) V)
    (S : Subgroup SL(2,F)) (n : ℕ) : Prop :=
  Nat.card V = 2^(2*n) ∧ ¬ commutator SL(2,F) ≤ ρ.ker ∧ IsQuadratic ρ S

omit [Finite V] in
/-- The coordinates produced by recognition imply the precise source
definition, including nontrivial derived-group action at field order two. -/
theorem sourceNatural_of_coordinates (ρ : Representation (ZMod 2) SL(2,F) V)
    (hfaith : Function.Injective ρ) (S : Sylow 2 SL(2,F)) (hq : IsQuadratic ρ S)
    (E : V ≃ₗ[ZMod 2] (Fin 2 → F)) {n : ℕ} (hF : Nat.card F = 2^n) :
    IsSourceNatural ρ S n := by
  refine ⟨?_,?_,hq⟩
  · rw [Nat.card_congr E.toEquiv,Nat.card_fun,Nat.card_fin,hF,← pow_mul,Nat.mul_comm n 2]
  · intro h
    have hk : ρ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff ρ).mpr hfaith
    have hc : commutator SL(2,F) = ⊥ := bot_unique (h.trans hk.le)
    have hz : Subgroup.center SL(2,F) = ⊤ := (commutator_eq_bot_iff_center_eq_top SL(2,F)).mp hc
    apply Matrix.SpecialLinearGroup.no_normal_sylow F 2 S
    constructor
    intro x hx g
    have hxZ : x ∈ Subgroup.center SL(2,F) := hz.symm ▸ mem_top x
    rw [Subgroup.mem_center_iff.mp hxZ g,mul_inv_cancel_right]
    exact hx

omit [Finite F] [Finite V] in
/-- The original actors are transitive on the nonzero vectors. -/
theorem transitive_of_natural_coordinates (ρ : Representation (ZMod 2) SL(2,F) V)
    (E : V ≃ₗ[ZMod 2] (Fin 2 → F))
    (he : ∀ g v, E (ρ g v) = Matrix.mulVec g.val (E v))
    {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) : ∃ g, ρ g v = w := by
  obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq F (E v) (E w)
    (fun h => hv (E.injective (h.trans E.map_zero.symm)))
    (fun h => hw (E.injective (h.trans E.map_zero.symm)))
  exact ⟨g,E.injective ((he g v).trans hg)⟩

omit [Finite F] [Finite V] in
/-- Natural coordinates imply irreducibility over the prime field. -/
theorem irreducible_of_natural_coordinates (ρ : Representation (ZMod 2) SL(2,F) V)
    (E : V ≃ₗ[ZMod 2] (Fin 2 → F))
    (he : ∀ g v, E (ρ g v) = Matrix.mulVec g.val (E v)) : ρ.IsIrreducible := by
  let : Nontrivial V := E.toEquiv.nontrivial
  refine ⟨?_⟩
  intro U
  by_cases hU : U = ⊥
  · exact Or.inl hU
  · right
    have hUb : U.toSubmodule ≠ ⊥ := fun h => hU (Subrepresentation.toSubmodule_injective h)
    obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUb
    apply top_unique
    intro w _
    by_cases hw : w = 0
    · change w ∈ U.toSubmodule
      rw [hw]
      exact U.toSubmodule.zero_mem
    · obtain ⟨g,hg⟩ := transitive_of_natural_coordinates ρ E he hv0 hw
      exact hg ▸ U.apply_mem_toSubmodule g hv

omit [Finite F] [Finite V] in
/-- The order marking retains the original finite field. -/
theorem card_of_natural_coordinates (E : V ≃ₗ[ZMod 2] (Fin 2 → F)) :
    Nat.card V = Nat.card F ^ 2 := by
  rw [Nat.card_congr E.toEquiv,Nat.card_fun,Nat.card_fin]

/-- The fixed order and individual fixed spaces in DGS p.113.
The same statement includes all positive binary field degrees. -/
theorem sl2_natural_fixed_spaces (ρ : Representation (ZMod 2) SL(2,F) V)
    (S : Sylow 2 SL(2,F)) (hq : IsQuadratic ρ S)
    (hgen : GeneratedByFixedSpace ρ S) (hfix : fixedSpace ρ ⊤ = ⊥)
    (E : V ≃ₗ[ZMod 2] (Fin 2 → F)) :
    Nat.card (fixedSpace ρ S) = Nat.card F ∧
      ∀ t ∈ (S : Subgroup SL(2,F)), t ≠ 1 →
        fixedSpace ρ (zpowers t) = fixedSpace ρ S := by
  obtain ⟨g,hg⟩ := SetLike.exists_not_mem_of_ne_top (normalizer (S : Set SL(2,F)))
    (Matrix.SpecialLinearGroup.sylow_normalizer_ne_top S)
  have hST : S ≠ g • S := by
    intro h
    exact hg (Sylow.smul_eq_iff_mem_normalizer.mp h.symm)
  have h := sl2_sylow_fixed_isCompl ρ S (g • S) hST hq hgen hfix
  have hunif := (SL2SylowFixedRecognition.fixedSpaceHypotheses_of_isCompl ρ S (g • S) h).uniform
  refine ⟨?_,hunif⟩
  have hd := (fixedSpace ρ S).finrank_sup_add_finrank_inf_eq (fixedSpace ρ (g • S : Sylow 2 SL(2,F)))
  rw [h.sup_eq_top,h.inf_eq_bot,finrank_top,finrank_bot,add_zero] at hd
  have heq := (fixedSpaceConjEquiv ρ S g).finrank_eq
  have hE := E.finrank_eq
  simp only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul] at hE
  have hf : Module.finrank (ZMod 2) (fixedSpace ρ S) = Module.finrank (ZMod 2) F := by
    change Module.finrank (ZMod 2) (fixedSpace ρ S) =
      Module.finrank (ZMod 2) (fixedSpace ρ (g • S : Sylow 2 SL(2,F))) at heq
    omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),hf,
    ← Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)]

end Representation.RankOne.QuadraticRecognition
