module

public import Theory.Representation.GoldschmidtONan.Consequences
public import Theory.SpecificGroups.Frobenius21.BinaryOvergroups
public import Mathlib.GroupTheory.Transfer

/-!
# Induction after the cyclic Sylow reduction

For a transitive Goldschmidt–O'Nan pair, a cyclic Sylow two-subgroup
forces odd group order under proper-subgroup induction. Burnside transfer
produces a normal two-complement H. A Sylow fixed vector shows that H is
still transitive on the nonzero vectors, and the original pair restricts
to H. Induction then forces the exceptional order-21 case. Its actual
faithful image in GL₃(2) is self-normalizing, which excludes a proper H.

This proves the second paragraph of GLS, Number 2, Chapter C, Proposition
14.2, Step 3 (`refs/KGroup/GLS2/ChapterC.tex`). Cyclicity of a Sylow
two-subgroup remains an explicit premise here; the preceding geometric
kernel argument is a separate part of that step.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open Representation.RegularCyclicNormalClosure
namespace Representation.GoldschmidtONan.OddReduction
variable {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Y : Subgroup X}

/-- Restricting the ambient group to an overgroup of Y preserves its fixed space. -/
theorem fixedSpace_restrict (H : Subgroup X) (hYH : Y ≤ H) :
    fixedSpace (ρ.comp H.subtype) (Y.subgroupOf H) = fixedSpace ρ Y := by
  ext v
  constructor
  · intro hv y
    exact hv ⟨⟨y, hYH y.property⟩, y.property⟩
  · intro hv y
    exact hv ⟨y.val.val, y.property⟩

/-- Restricting the ambient group to an overgroup of Y preserves its moved space. -/
theorem movedSpace_restrict (H : Subgroup X) (hYH : Y ≤ H) :
    displacementSpan (ρ.comp H.subtype) (Y.subgroupOf H) ⊤ = displacementSpan ρ Y ⊤ := by
  apply congrArg (Submodule.span (ZMod 2))
  ext v
  constructor
  · rintro ⟨y, hy, w, hw, rfl⟩
    exact ⟨y.val, hy, w, hw, rfl⟩
  · rintro ⟨y, hy, w, hw, rfl⟩
    exact ⟨⟨y, hYH hy⟩, hy, w, hw, rfl⟩

/-- Every overgroup of Y inherits the Goldschmidt–O'Nan input for the restricted action. -/
theorem input_restrict (h : Input ρ Y) (H : Subgroup X) (hYH : Y ≤ H) :
    Input (ρ.comp H.subtype) (Y.subgroupOf H) := by
  have hF := fixedSpace_restrict (ρ := ρ) H hYH
  have hD := movedSpace_restrict (ρ := ρ) H hYH
  have hOrbit : fixedOrbit (ρ.comp H.subtype) (Y.subgroupOf H) ⊆ fixedOrbit ρ Y := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, by rw [hF]; rfl⟩
  refine ⟨h.faithful.comp H.subtype_injective, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro he
    apply h.nontrivial
    rw [← Subgroup.map_subgroupOf_eq_of_le hYH, he, Subgroup.map_bot]
  · let : IsCyclic Y := h.cyclic
    exact isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hYH).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hYH).injective
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv]
    exact h.odd
  · rw [hD]
    intro v hv hv0 w hw hw0
    obtain ⟨y, hy⟩ := h.transitive v hv hv0 w hw hw0
    exact ⟨⟨⟨y, hYH y.property⟩, y.property⟩, hy⟩
  · rw [hF]
    exact h.fixed_nontrivial
  · intro U hU W hW hne
    exact h.ti U (hOrbit hU) W (hOrbit hW) hne
  · intro x hx
    rw [hF] at hx
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    apply Subgroup.le_normalizer_comap H.subtype
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (h.normal_in_stabilizer x hx)

/-- Transitivity on nonzero vectors excludes a nonzero proper invariant subspace. -/
theorem invariant_eq_bot_or_top_of_transitive (ht : NonzeroTransitive ρ)
    (W : Submodule (ZMod 2) V) (hW : Invariant ρ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  apply top_unique
  intro w _
  by_cases hw : w = 0
  · exact hw ▸ W.zero_mem
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hbot
  obtain ⟨v, hv0⟩ := exists_ne (0 : W)
  have hv : (v : V) ∈ W := v.property
  have hv0' : (v : V) ≠ 0 := fun he => hv0 (Subtype.ext he)
  obtain ⟨x, hx⟩ := ht v hv0' w hw
  rw [← hW x]
  exact ⟨v, hv, hx⟩

/-- For an odd transitive pair, the four alternatives force the exceptional case. -/
theorem exceptional_of_odd_of_transitive [Finite X] (h : Input ρ Y)
    (ht : NonzeroTransitive ρ) (hodd : Odd (Nat.card X)) (ha : Alternatives ρ Y) :
    ExceptionalCase ρ Y := by
  rcases ha with hs | hs | hs | he
  · rcases invariant_eq_bot_or_top_of_transitive ht _ hs.2 with he | he
    · exact False.elim (h.fixed_nontrivial he)
    · exact False.elim (h.fixed_ne_top he)
  · obtain ⟨H, _, hindex⟩ := h.normal_index_two_of_swapped hs
    have hdiv : 2 ∣ Nat.card X := hindex ▸ H.index_dvd_card
    exact False.elim (hodd.not_two_dvd_nat hdiv)
  · rcases invariant_eq_bot_or_top_of_transitive ht _ hs.2.2 with he | he
    · exact False.elim (h.moved_ne_bot he)
    · exact False.elim (h.moved_ne_top he)
  · exact he

/-- A normal subgroup of order 21 in a faithful three-dimensional binary action is the whole group. -/
theorem normal_card_twenty_one_eq_top [Finite X] [Finite V]
    (hfaith : Function.Injective ρ) (H : Subgroup X) [H.Normal]
    (hdim : Module.finrank (ZMod 2) V = 3) (hcard : Nat.card H = 21) : H = ⊤ := by
  have hf : Function.Injective ρ.asGroupHom := by
    intro x y he
    exact hfaith (congrArg Units.val he)
  have hN := Frobenius21.binary_normalizer_of_card V hdim (H.map ρ.asGroupHom)
    ((Subgroup.card_map_of_injective hf).trans hcard)
  apply top_unique
  intro x _
  have hx : ρ.asGroupHom x ∈ Subgroup.normalizer (H.map ρ.asGroupHom : Set _) := by
    apply Subgroup.le_normalizer_map ρ.asGroupHom
    exact ⟨x, by rw [H.normalizer_eq_top]; trivial, rfl⟩
  rw [hN] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  exact hf hxy ▸ hy

/-- A two-complement remains transitive: a Sylow two-subgroup fixes a nonzero vector. -/
theorem transitive_of_two_complement [Finite X] [Finite V]
    (hV : 0 < Module.finrank (ZMod 2) V) (ht : NonzeroTransitive ρ)
    (S : Sylow 2 X) (H : Subgroup X) (hHS : H.IsComplement' S) :
    NonzeroTransitive (ρ.comp H.subtype) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulAction S V := {
    smul s v := ρ s v
    one_smul v := by change ρ 1 v = v; simp
    mul_smul s t v := by
      change ρ ((s : X) * t) v = ρ s (ρ t v)
      rw [map_mul]; rfl }
  have hcard : 2 ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact dvd_pow_self _ (Nat.ne_zero_of_lt hV)
  obtain ⟨v, hv, hv0⟩ := S.2.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    V hcard (a := 0) (by intro s; exact map_zero (ρ s))
  have hbase : ∀ w : V, w ≠ 0 → ∃ a : H, ρ a v = w := by
    intro w hw
    obtain ⟨x, hx⟩ := ht v (Ne.symm hv0) w hw
    obtain ⟨⟨a, b⟩, hab⟩ := hHS.2 x
    refine ⟨a, ?_⟩
    have hab' : (a : X) * b = x := hab
    rw [← hab', map_mul, Module.End.mul_apply] at hx
    exact (congrArg (ρ a) (hv b)).symm.trans hx
  intro u hu w hw
  obtain ⟨a, ha⟩ := hbase u hu
  obtain ⟨b, hb⟩ := hbase w hw
  refine ⟨b * a⁻¹, ?_⟩
  change ρ ((b : X) * (a : X)⁻¹) u = w
  rw [← ha, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, hb]

/-- Burnside transfer and proper-subgroup induction exclude a nontrivial cyclic Sylow two-subgroup. -/
theorem odd_of_cyclic_sylow [Finite X] [Finite V] (h : Input ρ Y)
    (ht : NonzeroTransitive ρ) (hIH : ProperSubgroupCases ρ)
    (S : Sylow 2 X) (hS : IsCyclic S) : Odd (Nat.card X) := by
  by_contra hnot
  have htwo : 2 ∣ Nat.card X := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnot)
  have hp : (Nat.card X).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr htwo
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f := MonoidHom.transferSylow S (hS.normalizer_le_centralizer hp)
  let H := f.ker
  have hHS : H.IsComplement' S := hS.isComplement' hp
  have hodd : Odd (Nat.card H) := Nat.not_even_iff_odd.mp (fun he =>
    MonoidHom.not_dvd_card_ker_transferSylow S (hS.normalizer_le_centralizer hp)
      (even_iff_two_dvd.mp he))
  have hproper : H ≠ ⊤ := by
    intro he
    apply hnot
    simpa [he] using hodd
  have hYH : Y ≤ H := by
    intro y hy
    change f y = 1
    apply orderOf_eq_one_iff.mp
    have hd : orderOf (f y) ∣ Nat.card Y :=
      (orderOf_map_dvd (f.comp Y.subtype) (⟨y, hy⟩ : Y)).trans (orderOf_dvd_natCard _)
    have hc := S.2.orderOf_coprime h.odd.coprime_two_left (f y)
    exact Nat.eq_one_of_dvd_coprimes hc dvd_rfl hd
  have hH := input_restrict h H hYH
  have htH := transitive_of_two_complement
    (lt_of_lt_of_le (by decide : 0 < 3) h.dimension_ge_three) ht S H hHS
  have he := exceptional_of_odd_of_transitive hH htH hodd (hIH H hproper _ hH)
  exact hproper (normal_card_twenty_one_eq_top h.faithful H he.2.1 he.2.2.1)

end Representation.GoldschmidtONan.OddReduction
