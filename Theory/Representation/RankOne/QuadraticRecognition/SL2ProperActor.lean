module
public import Theory.Representation.RankOne.QuadraticRecognition.SL2Strict
public import Theory.Representation.RankOne.QuadraticRecognition.NaturalConsequences
public import Theory.Representation.BinaryOffender.QuadraticFixedDimension

/-!
# Natural recognition for proper binary SL₂ actors

In the strict corrected DGS inequality, fixed-space generation excludes
trivial quotients and forces irreducibility. Every involution in a nontrivial
irreducible binary SL₂ module moves half the dimension. Quadraticity therefore
makes the actor's fixed space equal to each of its nonidentity element fixed
spaces. The actor is larger than the square root of the Sylow order, so it
meets every normalizer conjugate nontrivially. Involution fusion inside the
Sylow then extends the common fixed space and quadraticity to the full Sylow.
The existing root-coordinate reconstruction supplies the natural module.

The field of order two is treated directly: a nontrivial actor is already the
whole Sylow. The action, defining field, and fixed quotient are unchanged.
Source: DGS85, *Groups and Graphs*, (5.12), printed pp.113–114, with the published
correction V=⟨C_V(S)^G⟩. This completes the SL₂ branch for arbitrary actors;
CriticalNaturalRecognition applies it to the original DGS critical quotient.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.RankOne.QuadraticRecognition
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

private theorem sylow_square (S : Sylow 2 SL(2,F)) (a : SL(2,F)) (ha : a ∈ S) :
    a ^ 2 = 1 := by
  let e := (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 S).symm
  have hp : (⟨a,ha⟩ : S) ^ 2 = 1 := by
    apply e.injective
    rw [map_pow,map_one,pow_two]
    change (e ⟨a,ha⟩).toAdd + (e ⟨a,ha⟩).toAdd = 0
    exact CharTwo.add_self_eq_zero _
  exact congrArg Subtype.val hp

private theorem irreducible_quadratic_fixed (ρ : Representation (ZMod 2) SL(2,F) V)
    [ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1)
    (S : Sylow 2 SL(2,F)) (A : Subgroup SL(2,F)) (hAS : A ≤ S)
    (hq : IsQuadratic ρ A) (a : SL(2,F)) (ha : a ∈ A) (ha1 : a ≠ 1) :
    fixedSpace ρ A = fixedSpace ρ (zpowers a) := by
  have hlo := SL2.binary_involution_displacement ρ hnt a ha1 (sylow_square S a (hAS ha))
  have hr : LinearMap.range (ρ a - LinearMap.id) ≤ fixedSpace ρ A := by
    rintro v ⟨w,rfl⟩ b
    exact hq b b.property a ha w
  have hrd := Submodule.finrank_mono hr
  have hsum := fixedCodim_add_finrank ρ (zpowers a)
  rw [fixedCodim_zpowers_eq_displacement_rank] at hsum
  have hle := fixedSpace_antitone ρ (zpowers_le.mpr ha)
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hh := Submodule.finrank_mono hle
  change Module.finrank (ZMod 2) V ≤
    2 * Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) at hlo
  omega

private theorem large_inf_ne_bot {G : Type*} [Group G] [Finite G]
    (S A B : Subgroup G) (hAS : A ≤ S) (hBS : B ≤ S)
    (hc : Nat.card S < Nat.card A * Nat.card B) : A ⊓ B ≠ ⊥ := by
  intro h
  have hd : Disjoint A B := disjoint_iff.mpr h
  let f : A × B → S := fun x => ⟨x.1.val * x.2.val, S.mul_mem (hAS x.1.property) (hBS x.2.property)⟩
  have hf : Function.Injective f := fun _ _ hh =>
    mul_injective_of_disjoint hd (congrArg Subtype.val hh)
  have hh := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at hh
  omega

/-- A quadratic actor larger than the square root of the Sylow order forces
quadratic Sylow action on every nontrivial irreducible binary SL₂ module. -/
theorem sl2_sylow_quadratic_of_large_irreducible_actor
    (ρ : Representation (ZMod 2) SL(2,F) V) [ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) (S : Sylow 2 SL(2,F))
    (A : Subgroup SL(2,F)) (hAS : A ≤ S) (hq : IsQuadratic ρ A)
    (hlarge : Nat.card S < Nat.card A ^ 2) : IsQuadratic ρ S := by
  have hA : A ≠ ⊥ := by
    intro h
    rw [h,card_bot,one_pow] at hlarge
    have hp : 0 < Nat.card S := Nat.card_pos
    omega
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA
  have hunif (b : SL(2,F)) (hb : b ∈ S) (hb1 : b ≠ 1) :
      fixedSpace ρ A = fixedSpace ρ (zpowers b) := by
    let e := Theory.PSL2.sl2QuotientEquiv F
    have hconj := Theory.PSL2.involutions_isConj (e a) (e b)
      ((e.orderOf_eq a).trans (orderOf_eq_prime (sylow_square S a (hAS ha)) ha1))
      ((e.orderOf_eq b).trans (orderOf_eq_prime (sylow_square S b hb) hb1))
    have hh : IsConj a b := by simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using e.symm.toMonoidHom.map_isConj hconj
    obtain ⟨g,hg⟩ := isConj_iff.mp hh
    have hgN := Matrix.SpecialLinearGroup.mem_sylow_normalizer_of_conjugate_mem S a g
      (hAS ha) ha1 (hg.symm ▸ S.toSubgroup.le_normalizer hb)
    let B := A.map (MulAut.conj g).toMonoidHom
    have hBS : B ≤ S := by
      apply (Subgroup.map_mono hAS).trans
      exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN).le
    have hBcard : Nat.card B = Nat.card A := card_map_of_injective (MulAut.conj g).injective
    have hi : A ⊓ B ≠ ⊥ := large_inf_ne_bot S A B hAS hBS (by rwa [hBcard,←pow_two])
    obtain ⟨x,hx,hx1⟩ := (A ⊓ B).bot_or_exists_ne_one.resolve_left hi
    have hqB : IsQuadratic ρ B := SL2SylowFixedRecognition.quadratic_conjugate ρ hq g
    have hfixed := (irreducible_quadratic_fixed ρ hnt S A hAS hq x hx.1 hx1).trans
      (irreducible_quadratic_fixed ρ hnt S B hBS hqB x hx.2 hx1).symm
    exact hfixed.trans (irreducible_quadratic_fixed ρ hnt S B hBS hqB b
      ⟨a,ha,hg⟩ hb1)
  have hfix : fixedSpace ρ S = fixedSpace ρ A := by
    apply le_antisymm (fixedSpace_antitone ρ hAS)
    intro v hv b
    by_cases hb1 : b.val = 1
    · simp [hb1]
    exact (mem_fixedSpace_zpowers_iff ρ b.val v).mp (hunif b b.property hb1 ▸ hv)
  apply isQuadratic_of_fixedDimension_bound ρ S (sylow_square S)
    (Module.finrank (ZMod 2) (fixedSpace ρ A))
  · intro b hb hb1
    rw [←hunif b hb hb1]
  · rw [hfix]

local instance finiteProperActorQuotient (C : Submodule (ZMod 2) V) : Finite (V ⧸ C) :=
  Finite.of_surjective _ C.mkQ_surjective

/-- The strict corrected DGS inequality upgrades every actor to quadratic
Sylow action, including the field of order two. -/
theorem sl2_strict_actor_sylow_quadratic
    (ρ : Representation (ZMod 2) SL(2,F) V) (hf : Function.Injective ρ)
    (S : Sylow 2 SL(2,F)) (A : Subgroup SL(2,F)) (hAS : A ≤ S)
    (hq : IsQuadratic ρ A) (hgen : GeneratedByFixedSpace ρ S)
    (hfix : fixedSpace ρ ⊤ = ⊥) {n : ℕ} (hF : Nat.card F = 2^n)
    (hstrict : Nat.card (V ⧸ fixedSpace ρ A) < Nat.card A ^ 2) :
    IsQuadratic ρ S := by
  have hA : A ≠ ⊥ := by
    intro h
    rw [h,card_bot,one_pow] at hstrict
    have hp : 0 < Nat.card (V ⧸ fixedSpace ρ ⊥) := Nat.card_pos
    omega
  have hSc : Nat.card S = Nat.card F := Nat.card_congr
    (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 S).symm.toEquiv
  by_cases hn : 1 < n
  · let : ρ.IsIrreducible := sl2_strict_actor_irreducible ρ hf S A hAS hgen hfix hn hF hstrict
    obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA
    have hnt : ∃ g, ρ g ≠ 1 := ⟨a,fun he => ha1 (hf (he.trans ρ.map_one.symm))⟩
    exact sl2_sylow_quadratic_of_large_irreducible_actor ρ hnt S A hAS hq
      (hSc ▸ sl2_strict_actor_large ρ hf S A hAS hF hstrict)
  · have hAc : 1 < Nat.card A := (one_lt_card_iff_ne_bot A).mpr hA
    have hsmall : Nat.card S ≤ 2 := by
      rw [hSc,hF]
      exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : n ≤ 1)
    have he : A = (S : Subgroup SL(2,F)) := eq_of_le_of_card_ge hAS (by omega)
    exact he ▸ hq

/-- Corrected DGS (5.12)(b) for every binary SL₂ field and every subgroup
of its prescribed Sylow. The output includes the exact source definition
and equivariant coordinates over the unchanged defining field. -/
theorem sl2_strict_actor_natural
    (ρ : Representation (ZMod 2) SL(2,F) V) (hf : Function.Injective ρ)
    (S : Sylow 2 SL(2,F)) (A : Subgroup SL(2,F)) (hAS : A ≤ S)
    (hq : IsQuadratic ρ A) (hgen : GeneratedByFixedSpace ρ S)
    (hfix : fixedSpace ρ ⊤ = ⊥) {n : ℕ} (hF : Nat.card F = 2^n)
    (hstrict : Nat.card (V ⧸ fixedSpace ρ A) < Nat.card A ^ 2) :
    IsSourceNatural ρ S n ∧ ∃ E : V ≃ₗ[ZMod 2] (Fin 2 → F),
      ∀ g v, E (ρ g v) = Matrix.mulVec g.val (E v) := by
  have hqS := sl2_strict_actor_sylow_quadratic ρ hf S A hAS hq hgen hfix hF hstrict
  have hA : A ≠ ⊥ := by
    intro h
    rw [h,card_bot,one_pow] at hstrict
    have hp : 0 < Nat.card (V ⧸ fixedSpace ρ ⊥) := Nat.card_pos
    omega
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA
  obtain ⟨g,hg⟩ := SetLike.exists_not_mem_of_ne_top (normalizer (S : Set SL(2,F)))
    (Matrix.SpecialLinearGroup.sylow_normalizer_ne_top S)
  have hST : S ≠ g • S := fun h => hg (Sylow.smul_eq_iff_mem_normalizer.mp h.symm)
  have hcompl := sl2_sylow_fixed_isCompl ρ S (g • S) hST hqS hgen hfix
  have hu := (SL2SylowFixedRecognition.fixedSpaceHypotheses_of_isCompl ρ S (g • S) hcompl).uniform
  have hfixed : fixedSpace ρ A = fixedSpace ρ S := le_antisymm
    ((fixedSpace_antitone ρ (zpowers_le.mpr ha)).trans (hu a (hAS ha) ha1).le)
    (fixedSpace_antitone ρ hAS)
  have hcard : Nat.card A ≤ Nat.card S :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hAS)
  have hstrictS : Nat.card (V ⧸ fixedSpace ρ S) < Nat.card S ^ 2 := by
    rw [hfixed] at hstrict
    exact hstrict.trans_le (Nat.pow_le_pow_left hcard 2)
  obtain ⟨E,he⟩ := (sl2_sylow_bound_and_recognition ρ hf S hqS hgen hfix hF).2 hstrictS
  exact ⟨sourceNatural_of_coordinates ρ hf S hqS E hF,E,he⟩

end Representation.RankOne.QuadraticRecognition
