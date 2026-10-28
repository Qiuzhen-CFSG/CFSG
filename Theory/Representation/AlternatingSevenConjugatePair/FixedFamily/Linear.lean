module

public import Theory.Representation.AlternatingSevenConjugatePair.Model.FixedSpaces

/-!
# Fixed planes for commuting cubic and elementary actors

A nontrivial cubic element commuting with a binary two-group forces the
common fixed space to have dimension at least two. Its displacement image
is invariant under the two-group and contains a nonzero fixed vector. If
the entire fixed space were a binary line, the cubic would fix this vector,
contradicting its zero cubic norm on the displacement image.

The remaining lemmas give the square-zero displacement bound for involutions,
the commutation test for equal involution fixed spaces, and fixed-space
transport between the actual summands and their ambient intersections.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.8,
printed p.389/PDF p.400.
-/

@[expose] public section

open Representation Representation.BinaryOffender
namespace Representation.AlternatingSevenConjugatePair.FixedFamily
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem cubic_centralizer_fixed_dimension
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (A : Subgroup G) (hA : IsPGroup 2 A) (c : G) (hc : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hcomm : ∀ a ∈ A, a * c = c * a) :
    2 ≤ Module.finrank (ZMod 2) (fixedSpace ρ A) := by
  classical
  let W : Subrepresentation (ρ.comp A.subtype) := {
    toSubmodule := LinearMap.range (ρ c - LinearMap.id)
    apply_mem_toSubmodule := by
      rintro a _ ⟨v, rfl⟩
      refine ⟨ρ a v, ?_⟩
      change ρ c (ρ a v) - ρ a v = ρ a (ρ c v - v)
      rw [map_sub, ← Module.End.mul_apply, ← map_mul,
        ← hcomm a a.property, map_mul]
      rfl }
  have hW : W.toSubmodule ≠ ⊥ := by
    intro hz
    apply hc1
    apply hρ
    ext v
    have hv : ρ c v - v ∈ W.toSubmodule := ⟨v, rfl⟩
    rw [hz, Submodule.mem_bot] at hv
    simpa using sub_eq_zero.mp hv
  let _ : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  obtain ⟨u, hu0, huf⟩ :=
    BinaryLinearThree.IrreducibleCatalogue.binary_pGroup_fixed_vector W.toRepresentation hA
  have hu : (u : V) ∈ fixedSpace ρ A := fun a => congrArg Subtype.val (huf a)
  have hu0' : (u : V) ≠ 0 := fun h => hu0 (Subtype.ext h)
  have hcu : ρ c u ∈ fixedSpace ρ A := by
    intro a
    change ρ a (ρ c u) = ρ c u
    rw [← Module.End.mul_apply, ← map_mul, hcomm a a.property, map_mul]
    exact congrArg (ρ c) (hu a)
  have hcu0 : ρ c u ≠ 0 := by
    intro h
    exact hu0' ((ρ.apply_bijective c).injective (h.trans (map_zero _).symm))
  by_contra hn
  have hpos : 0 < Module.finrank (ZMod 2) (fixedSpace ρ A) := by
    let _ : Nontrivial (fixedSpace ρ A) := ⟨⟨⟨u, hu⟩, 0, fun h =>
      hu0' (congrArg Subtype.val h)⟩⟩
    exact Module.finrank_pos
  have hdim : Module.finrank (ZMod 2) (fixedSpace ρ A) = 1 := by omega
  have hs := eq_span_singleton_of_mem_of_finrank_eq_one hdim hu hu0'
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp (hs ▸ hcu)
  have hk0 : k ≠ 0 := by intro h; simp [h] at hk; exact hcu0 hk.symm
  have hk1 : k = 1 := (by decide : ∀ k : ZMod 2, k ≠ 0 → k = 1) k hk0
  have hfix : ρ c u = u := by simpa [hk1] using hk.symm
  obtain ⟨v, hv⟩ := u.property
  have hcube (v : V) : ρ c (ρ c (ρ c v)) = v := by
    change (ρ c * ρ c * ρ c) v = v
    rw [← map_mul, ← map_mul, ← pow_two, ← pow_succ, hc, map_one]
    rfl
  have hnorm : (u : V) + ρ c u + ρ c (ρ c u) = 0 := by
    rw [← hv]
    change (ρ c v - v) + ρ c (ρ c v - v) + ρ c (ρ c (ρ c v - v)) = 0
    simp only [map_sub, hcube]
    abel
  rw [hfix, hfix, ZModModule.add_self, zero_add] at hnorm
  exact hu0' hnorm

omit [FiniteDimensional (ZMod 2) V] in
theorem involution_range_le_fixed (ρ : Representation (ZMod 2) G V)
    (t : G) (ht : t ^ 2 = 1) :
    LinearMap.range (ρ t - LinearMap.id) ≤ fixedSpace ρ (Subgroup.zpowers t) := by
  rintro _ ⟨v, rfl⟩
  rw [mem_fixedSpace_zpowers_iff]
  change ρ t (ρ t v - v) = ρ t v - v
  have hs : ρ t (ρ t v) = v := by
    change (ρ t * ρ t) v = v
    rw [← map_mul, ← pow_two, ht, map_one]
    rfl
  rw [map_sub, hs]
  simp only [sub_eq_add_neg, ZModModule.neg_eq_self, add_comm]

theorem involution_codim_le_two (ρ : Representation (ZMod 2) G V)
    (hdim : Module.finrank (ZMod 2) V = 4) (t : G) (ht : t ^ 2 = 1) :
    fixedCodim ρ (Subgroup.zpowers t) ≤ 2 := by
  have hle := Submodule.finrank_mono (involution_range_le_fixed ρ t ht)
  rw [← fixedCodim_zpowers_eq_displacement_rank] at hle
  have h := fixedCodim_add_finrank ρ (Subgroup.zpowers t)
  omega

omit [FiniteDimensional (ZMod 2) V] in
theorem commute_of_same_involution_fixedSpace (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (s t : G) (hs : s ^ 2 = 1) (ht : t ^ 2 = 1)
    (hf : fixedSpace ρ (Subgroup.zpowers s) = fixedSpace ρ (Subgroup.zpowers t)) :
    s * t = t * s := by
  apply hρ
  ext v
  have htv : ρ t v - v ∈ fixedSpace ρ (Subgroup.zpowers s) :=
    hf ▸ involution_range_le_fixed ρ t ht ⟨v, rfl⟩
  have hsv : ρ s v - v ∈ fixedSpace ρ (Subgroup.zpowers t) :=
    hf ▸ involution_range_le_fixed ρ s hs ⟨v, rfl⟩
  rw [mem_fixedSpace_zpowers_iff, map_sub] at htv hsv
  simp only [map_mul, Module.End.mul_apply]
  calc
    ρ s (ρ t v) = (ρ t v - v) + ρ s v := (sub_eq_iff_eq_add.mp htv)
    _ = (ρ s v - v) + ρ t v := by abel
    _ = ρ t (ρ s v) := (sub_eq_iff_eq_add.mp hsv).symm

end Representation.AlternatingSevenConjugatePair.FixedFamily

namespace Representation.AlternatingSevenConjugatePair.FixedFamily
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

noncomputable def summandFixedEquiv
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 7)) V)
    (U : Subrepresentation (ρ.comp (alternatingGroup (Fin 7)).subtype))
    (A : Subgroup (Equiv.Perm (Fin 7))) (hA : A ≤ alternatingGroup (Fin 7)) :
    fixedSpace U.toRepresentation (A.subgroupOf (alternatingGroup (Fin 7))) ≃ₗ[ZMod 2]
      (U.toSubmodule ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) where
  toFun v := ⟨v.val, v.val.property, fun a =>
    congrArg Subtype.val (v.property ⟨⟨a, hA a.property⟩, a.property⟩)⟩
  invFun v := ⟨⟨v, v.property.1⟩, fun a =>
    Subtype.ext (v.property.2 ⟨a.val, a.property⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem summand_involution_dimensions (D : Pair V)
    (hinv : ∀ t : Equiv.Perm (Fin 7), orderOf t = 2 →
      fixedCodim D.representation (Subgroup.zpowers t) = 4)
    (t : Equiv.Perm (Fin 7)) (ht : orderOf t = 2) (he : t ∈ alternatingGroup (Fin 7)) :
    Module.finrank (ZMod 2) (D.firstFixedSpace (Subgroup.zpowers t)) = 2 ∧
    Module.finrank (ZMod 2) (D.secondFixedSpace (Subgroup.zpowers t)) = 2 := by
  let a : alternatingGroup (Fin 7) := ⟨t, he⟩
  have ha : a ^ 2 = 1 := Subtype.ext (by simpa [ht] using pow_orderOf_eq_one t)
  have hU := involution_codim_le_two D.first.toRepresentation D.first_dim a ha
  have hW := involution_codim_le_two D.second.toRepresentation D.second_dim a ha
  have hsum := D.inner_fixedCodim a
  rw [hinv t ht] at hsum
  have hfU := (cyclicSummandFixedEquiv D.representation D.first a).finrank_eq
  have hfW := (cyclicSummandFixedEquiv D.representation D.second a).finrank_eq
  have hdU := fixedCodim_add_finrank D.first.toRepresentation (Subgroup.zpowers a)
  have hdW := fixedCodim_add_finrank D.second.toRepresentation (Subgroup.zpowers a)
  rw [D.first_dim] at hdU
  rw [D.second_dim] at hdW
  change _ = Module.finrank (ZMod 2) (D.firstFixedSpace (Subgroup.zpowers t)) at hfU
  change _ = Module.finrank (ZMod 2) (D.secondFixedSpace (Subgroup.zpowers t)) at hfW
  omega

theorem summand_fixed_dimensions_le_two (D : Pair V)
    (hinv : ∀ t : Equiv.Perm (Fin 7), orderOf t = 2 →
      fixedCodim D.representation (Subgroup.zpowers t) = 4)
    (A : Subgroup (Equiv.Perm (Fin 7))) (hA : IsElementaryTwo A)
    (hAL : A ≤ alternatingGroup (Fin 7)) :
    Module.finrank (ZMod 2) (D.firstFixedSpace A) ≤ 2 ∧
    Module.finrank (ZMod 2) (D.secondFixedSpace A) ≤ 2 := by
  let _ := hA.2
  obtain ⟨t, htA, ht⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ht2 : orderOf t = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t htA) ht
  obtain ⟨hU, hW⟩ := summand_involution_dimensions D hinv t ht2 (hAL htA)
  have hle := fixedSpace_antitone D.representation (Subgroup.zpowers_le.mpr htA)
  exact ⟨(Submodule.finrank_mono (inf_le_inf_left D.first.toSubmodule hle)).trans_eq hU,
    (Submodule.finrank_mono (inf_le_inf_left D.second.toSubmodule hle)).trans_eq hW⟩

theorem codim_four_iff_summand_dimensions (D : Pair V)
    (hinv : ∀ t : Equiv.Perm (Fin 7), orderOf t = 2 →
      fixedCodim D.representation (Subgroup.zpowers t) = 4)
    (A : Subgroup (Equiv.Perm (Fin 7))) (hA : IsElementaryTwo A)
    (hAL : A ≤ alternatingGroup (Fin 7)) :
    fixedCodim D.representation A = 4 ↔
      Module.finrank (ZMod 2) (D.firstFixedSpace A) = 2 ∧
      Module.finrank (ZMod 2) (D.secondFixedSpace A) = 2 := by
  have hsum := D.finrank_fixedSpace A hAL
  have hdim := fixedCodim_add_finrank D.representation A
  rw [D.finrank_eq_eight] at hdim
  have hle := summand_fixed_dimensions_le_two D hinv A hA hAL
  omega

end Representation.AlternatingSevenConjugatePair.FixedFamily
