module
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorPermutation
public import Theory.SpecificGroups.SymmetricFive.AutomorphismRank

/-!
The adequate-classification alternative for a group marked as S₅ × S₃ is the
source two-factor alternative. Cardinalities exclude the symmetric, outer and
hyperplane cases; the normal C₃ excludes a quasisimple generalized Fitting group.
Normal-factor rigidity then identifies the two factors with the marked coordinates.

This is the group comparison used in the B.5.6 application on printed p.812 of
Aschbacher–Smith, *The Classification of Quasithin Groups*, volume II.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction
namespace SymmetricFiveThree
abbrev Model := Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)

private theorem card_model : Nat.card Model = 720 := by
  simp [Model, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

variable {Q : Type*} [Group Q] [Finite Q] (e : Q ≃* Model)
include e

private theorem not_quasisimple_fitting (h : IsQuasisimple (generalizedFitting Q)) : False := by
  let N₀ : Subgroup Model := (⊥ : Subgroup (Equiv.Perm (Fin 5))).prod
    (alternatingGroup (Fin 3))
  let N : Subgroup Q := N₀.map e.symm.toMonoidHom
  let : N.Normal := (inferInstance : N₀.Normal).map _ e.symm.surjective
  have hcard : Nat.card N = 3 := by
    rw [card_map_of_injective e.symm.injective]
    rw [Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod, Nat.card_unique, one_mul,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hN : N ≤ generalizedFitting Q :=
    (show N ≤ pCore 3 Q from le_sSup ⟨inferInstance,
      IsPGroup.of_card (n := 1) (by simpa using hcard)⟩).trans
      ((pCore_le_fitting Q 3).trans (fitting_le_generalizedFitting Q))
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
    apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  let f : generalizedFitting Q →* Equiv.Perm (Fin 3) :=
    ((MonoidHom.snd _ _).comp e.toMonoidHom).comp (generalizedFitting Q).subtype
  let : Group.IsPerfect (generalizedFitting Q) := h.toIsPerfect
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  have hbot : N = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    have hsecond : (e x).2 = 1 := congrArg Subtype.val
      (Subsingleton.elim (f.rangeRestrict ⟨x,hN hx⟩) 1)
    obtain ⟨y,hy,rfl⟩ := hx
    apply e.injective
    change e (e.symm y) = e 1
    rw [e.apply_symm_apply, map_one]
    apply Prod.ext
    · exact hy.1
    · change y.2 = 1
      simpa only [e.apply_symm_apply] using (show (e (e.symm y)).2 = 1 from hsecond)
  rw [hbot, Nat.card_unique] at hcard
  omega

/-- For the literal S₅ × S₃ actor, only the two-factor row of B.5.6 survives. -/
theorem twoFactors {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) Q W) (h : NontrivialAdequateAlternative ρ) :
    Nonempty (SourceTwoFactorCase ρ) := by
  have hcard : Nat.card Q = 720 := (Nat.card_congr e.toEquiv).trans card_model
  cases h with
  | quasisimple hq _ => exact (not_quasisimple_fitting e hq).elim
  | symmetricThree c =>
    have he : Nat.card Q = 6 := by
      rw [Nat.card_congr c.equiv.toEquiv]
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    omega
  | twoFactors c => exact ⟨c⟩
  | outerSixThree c =>
    have hc : Nat.card (c.first ⊔ c.second : Subgroup Q) = 1080 := by
      rw [← Nat.card_congr c.product.toEquiv, Nat.card_prod,
        Nat.card_congr c.firstEquiv.toEquiv, Nat.card_congr c.secondEquiv.toEquiv,
        nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hb := Nat.card_le_card_of_injective (c.first ⊔ c.second).subtype
      (c.first ⊔ c.second).subtype_injective
    rw [hc, hcard] at hb
    omega
  | hyperplane c =>
    have hd := c.first.card_subgroup_dvd_card
    rw [Nat.card_congr c.firstEquiv.toEquiv, Matrix.PSL3Two.card_SL, hcard] at hd
    norm_num at hd

omit [Finite Q] in
private theorem coordinate_images {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) Q W} (d : SourceTwoFactorCase ρ)
    (ha : ∀ a : d.first, (e (a : Q)).2 = 1)
    (hb : ∀ b : d.second, (e (b : Q)).1 = 1) :
    d.first.map e.toMonoidHom = (⊤ : Subgroup (Equiv.Perm (Fin 5))).prod ⊥ ∧
    d.second.map e.toMonoidHom = (⊥ : Subgroup (Equiv.Perm (Fin 5))).prod ⊤ := by
  constructor
  · apply le_antisymm
    · rintro _ ⟨a,ha',rfl⟩
      exact ⟨mem_top _,ha ⟨a,ha'⟩⟩
    · intro p hp
      obtain ⟨g,hg⟩ := e.surjective p
      obtain ⟨a,b,h⟩ := d.product.exists_mul g
      have he : p = e (a : Q) * e (b : Q) := by rw [←hg,h,map_mul]
      refine ⟨a,a.property,?_⟩
      change e _ = p
      apply Prod.ext
      · have hh := congrArg Prod.fst he
        simpa only [Prod.fst_mul,hb,mul_one] using hh.symm
      · exact (ha a).trans hp.2.symm
  · apply le_antisymm
    · rintro _ ⟨b,hb',rfl⟩
      exact ⟨hb ⟨b,hb'⟩,mem_top _⟩
    · intro p hp
      obtain ⟨g,hg⟩ := e.surjective p
      obtain ⟨a,b,h⟩ := d.product.exists_mul g
      have he : p = e (a : Q) * e (b : Q) := by rw [←hg,h,map_mul]
      refine ⟨b,b.property,?_⟩
      change e _ = p
      apply Prod.ext
      · exact (hb b).trans hp.1.symm
      · have hh := congrArg Prod.snd he
        simpa only [Prod.snd_mul,ha,one_mul] using hh.symm

/-- The source factors can be ordered to match the original two coordinates. -/
theorem marked_twoFactors {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) Q W) (h : NontrivialAdequateAlternative ρ) :
    ∃ d : SourceTwoFactorCase ρ,
      d.first.map e.toMonoidHom = (⊤ : Subgroup (Equiv.Perm (Fin 5))).prod ⊥ ∧
      d.second.map e.toMonoidHom = (⊥ : Subgroup (Equiv.Perm (Fin 5))).prod ⊤ := by
  obtain ⟨d⟩ := twoFactors e ρ h
  have coordinates (A : Subgroup Q) (U : Subrepresentation ρ) [A.Normal]
      (hA : SourceFactorCase ρ A U) :
      (∀ a : A, (e (a : Q)).2 = 1) ∨ (∀ a : A, (e (a : Q)).1 = 1) := by
    let f := e.toMonoidHom.comp A.subtype
    let : f.range.Normal := by
      rw [MonoidHom.range_comp,range_subtype]
      exact (inferInstance : A.Normal).map _ e.surjective
    exact normal_product_embedding_coordinate hA.normal_quotient_two
      Theory.SpecificGroups.SymmetricFive.pCore_two_eq_bot
      (show center (Equiv.Perm (Fin 3)) = ⊥ from by
        apply (eq_bot_iff_forall _).mpr
        exact by decide) f
  let : d.first.Normal := d.product.swap.second_normal
  let : d.second.Normal := d.product.second_normal
  rcases coordinates d.first d.firstSpace d.firstCase with ha | ha <;>
    rcases coordinates d.second d.secondSpace d.secondCase with hb | hb
  · have hall (g : Q) : (e g).2 = 1 := by
      obtain ⟨a,b,rfl⟩ := d.product.exists_mul g
      rw [map_mul]
      change (e (a : Q)).2 * (e (b : Q)).2 = 1
      rw [ha,hb,one_mul]
    obtain ⟨b,hbne⟩ := exists_ne (1 : Equiv.Perm (Fin 3))
    have he := hall (e.symm (1,b))
    exact (hbne (by simpa only [e.apply_symm_apply] using he)).elim
  · exact ⟨d,coordinate_images e d ha hb⟩
  · let d' : SourceTwoFactorCase ρ := {
      first := d.second
      second := d.first
      product := d.product.swap
      firstSpace := d.secondSpace
      secondSpace := d.firstSpace
      decomposition := d.decomposition.symm
      firstCase := d.secondCase
      secondCase := d.firstCase }
    exact ⟨d',coordinate_images e d' hb ha⟩
  · have hall (g : Q) : (e g).1 = 1 := by
      obtain ⟨a,b,rfl⟩ := d.product.exists_mul g
      rw [map_mul]
      change (e (a : Q)).1 * (e (b : Q)).1 = 1
      rw [ha,hb,one_mul]
    obtain ⟨a,hane⟩ := exists_ne (1 : Equiv.Perm (Fin 5))
    have he := hall (e.symm (a,1))
    exact (hane (by simpa only [e.apply_symm_apply] using he)).elim

end SymmetricFiveThree
end CFSG.Quasithin.ChapterB.SourceInduction
