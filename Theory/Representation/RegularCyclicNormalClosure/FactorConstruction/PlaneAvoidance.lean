module

public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.SupportRigidity
public import Theory.Representation.GoldschmidtONan.ExceptionalOrbit
public import Theory.SpecificGroups.Frobenius21.ConjugateActors

/-!
# Cubic planes avoiding a line in the exceptional three-space

An exceptional factor is transitive on its seven nonzero moved vectors.
A vector with nonzero fixed and moved components for its cubic subgroup
has a cubic orbit spanning the three-space. Consequently two distinct
conjugate cubic planes can be chosen to avoid any specified nonzero vector.
This proves the required seven-plane incidence statement without imposing
an enumeration or a global commutation condition.

Source: the exceptional compatibility step in Aschbacher–Smith E.6.24,
printed p.255, citing Aschbacher (1981), 10.4.
-/

public section
open Module Subgroup Representation.BinaryOffender
namespace Representation.RegularCyclicNormalClosure
open FactorConstruction
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

/-- A mixed fixed/moved vector has an orbit escaping every plane. -/
theorem Input.mixed_orbit_not_contained [FiniteDimensional (ZMod 2) W]
    (h : Input ρ C) (hS : finrank (ZMod 2) (displacementSpan ρ C ⊤) = 2)
    {u s : W} (hu : u ∈ fixedSpace ρ C) (hu0 : u ≠ 0)
    (hs : s ∈ displacementSpan ρ C ⊤) (hs0 : s ≠ 0)
    (R : Submodule (ZMod 2) W) (hR : finrank (ZMod 2) R ≤ 2) :
    ∃ c : C, ρ c (u+s) ∉ R := by
  classical
  by_contra! hall
  obtain ⟨c, hc⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.nontrivial
  have hx : u+s ∈ R := by simpa using hall 1
  let δ := ρ c s - s
  have hδS : δ ∈ displacementSpan ρ C ⊤ :=
    Submodule.subset_span ⟨c, c.property, s, Submodule.mem_top, rfl⟩
  have hδ0 : δ ≠ 0 := by
    intro he
    exact hs0 (h.eq_zero_of_mem_moved_of_fixed hc hs (sub_eq_zero.mp he))
  have hSR : displacementSpan ρ C ⊤ ≤ R := by
    intro w hw
    by_cases hw0 : w = 0
    · exact hw0 ▸ R.zero_mem
    obtain ⟨d, hd, _⟩ := h.regular δ hδS hδ0 w hw hw0
    have hh := R.sub_mem (hall (d*c)) (hall d)
    have he : ρ (d*c : C) (u+s) - ρ d (u+s) = ρ d δ := by
      change ρ ((d : A)*(c : A)) (u+s) - ρ d (u+s) = _
      rw [map_mul, Module.End.mul_apply, ← map_sub]
      congr 1
      simp only [map_add, show ρ (c : A) u = u from hu c, add_sub_add_left_eq_sub, δ]
    rw [he, hd] at hh
    exact hh
  have he : displacementSpan ρ C ⊤ = R :=
    Submodule.eq_of_le_of_finrank_eq hSR (by
      have hh := Submodule.finrank_mono hSR
      omega)
  have huR : u ∈ R := by
    have hh := R.sub_mem hx (hSR hs)
    simpa only [add_sub_cancel_right] using hh
  exact hu0 (Submodule.disjoint_def.mp h.split.disjoint u hu (he ▸ huR))

variable [Finite A] [Finite W]

/-- The actual exceptional factor is transitive on its seven moved nonzero vectors. -/
theorem ExceptionalCandidate.transitive_moved {B : Subgroup A}
    (hB : ExceptionalCandidate ρ C B) (h : Input ρ C) :
    ∀ v ∈ displacementSpan ρ B ⊤, v ≠ 0 →
      ∀ w ∈ displacementSpan ρ B ⊤, w ≠ 0 → ∃ b ∈ B, ρ b v = w := by
  let T := displacementSpan ρ B ⊤
  have hST : displacementSpan ρ C ⊤ ≤ T := displacementSpan_mono ρ hB.contained le_rfl
  have hd := h.moved_finrank_eq_two_of_card_three hB.cyclic_card
  have hT : finrank (ZMod 2) T = 3 := hB.moved_dimension
  have hf := h.onQuotientFixer_faithful T hST (by omega)
  have hc : 7 ∣ Nat.card (quotientFixer ρ T) := by
    rw [hB.quotientFixer_moved_eq h, hB.factor_card]
    decide
  have ht := GoldschmidtONan.nonzeroTransitive_of_finrank_three_of_seven_dvd hf hT hc
  intro v hv hv0 w hw hw0
  obtain ⟨b, hb⟩ := ht ⟨v, hv⟩ (fun he => hv0 (congrArg Subtype.val he))
    ⟨w, hw⟩ (fun he => hw0 (congrArg Subtype.val he))
  exact ⟨b, hB.quotientFixer_moved_eq h ▸ b.property, congrArg Subtype.val hb⟩

omit [Finite A] in
/-- The exceptional three-space contains a vector with both components nonzero. -/
theorem ExceptionalCandidate.exists_mixed {B : Subgroup A}
    (hB : ExceptionalCandidate ρ C B) (h : Input ρ C) :
    ∃ u ∈ fixedSpace ρ C, u ∈ displacementSpan ρ B ⊤ ∧ u ≠ 0 ∧
      ∃ s ∈ displacementSpan ρ C ⊤, s ≠ 0 := by
  have hST := displacementSpan_mono ρ hB.contained (le_rfl : (⊤ : Submodule (ZMod 2) W) ≤ ⊤)
  have hd := h.moved_finrank_eq_two_of_card_three hB.cyclic_card
  have hnot : ¬ displacementSpan ρ B ⊤ ≤ displacementSpan ρ C ⊤ := by
    intro hh
    have hh' := Submodule.finrank_mono hh
    rw [hB.moved_dimension, hd] at hh'
    omega
  obtain ⟨x, hx, hxS⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨u, hu, s, hs, he⟩ := Submodule.mem_sup.mp
    (show x ∈ fixedSpace ρ C ⊔ displacementSpan ρ C ⊤ by rw [h.split.sup_eq_top]; trivial)
  have huT : u ∈ displacementSpan ρ B ⊤ := by
    have hh := (displacementSpan ρ B ⊤).sub_mem hx (hST hs)
    rw [← he, add_sub_cancel_right] at hh
    exact hh
  have hu0 : u ≠ 0 := by
    intro hu0
    rw [hu0, zero_add] at he
    exact hxS (he ▸ hs)
  let : Nontrivial (displacementSpan ρ C ⊤) :=
    Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨s', hs'⟩ := exists_ne (0 : displacementSpan ρ C ⊤)
  exact ⟨u, hu, huT, hu0, s', s'.property, fun he => hs' (Subtype.ext he)⟩

/-- Two distinct actual cubic conjugates have planes avoiding any prescribed
nonzero vector of the exceptional three-space. -/
theorem ExceptionalCandidate.two_planes_avoiding {B : Subgroup A}
    (hB : ExceptionalCandidate ρ C B) (h : Input ρ C)
    (v : W) (hv : v ∈ displacementSpan ρ B ⊤) (hv0 : v ≠ 0) :
    ∃ b k : B,
      C.map (MulAut.conj (b : A)).toMonoidHom ≠ C.map (MulAut.conj (k : A)).toMonoidHom ∧
      v ∉ (displacementSpan ρ C ⊤).map (ρ b) ∧
      v ∉ (displacementSpan ρ C ⊤).map (ρ k) := by
  obtain ⟨u, hu, huT, hu0, s, hs, hs0⟩ := hB.exists_mixed h
  let x := u+s
  have hxS : x ∉ displacementSpan ρ C ⊤ := by
    intro hx
    have huS := (displacementSpan ρ C ⊤).sub_mem hx hs
    rw [add_sub_cancel_right] at huS
    exact hu0 (Submodule.disjoint_def.mp h.split.disjoint u hu huS)
  have hx0 : x ≠ 0 := fun he => hxS (he ▸ Submodule.zero_mem _)
  have hxT : x ∈ displacementSpan ρ B ⊤ :=
    (displacementSpan ρ B ⊤).add_mem huT (displacementSpan_mono ρ hB.contained le_rfl hs)
  obtain ⟨b, hb, hbx⟩ := hB.transitive_moved h x hxT hx0 v hv hv0
  obtain ⟨k, hk⟩ := Frobenius21.exists_distinct_cubic_conjugate
    hB.contained hB.cyclic_card hB.factor_card hB.nonabelian
  have hd := h.moved_finrank_eq_two_of_card_three hB.cyclic_card
  have hR : finrank (ZMod 2) ((displacementSpan ρ C ⊤).map (ρ k)) ≤ 2 := by
    rw [← (Submodule.equivMapOfInjective (ρ k) (ρ.apply_bijective k).injective
      (displacementSpan ρ C ⊤)).finrank_eq, hd]
  obtain ⟨c, hc⟩ := h.mixed_orbit_not_contained hd hu hu0 hs hs0 _ hR
  let q : B := ⟨b * (c : A)⁻¹ * (k : A),
    B.mul_mem (B.mul_mem hb (B.inv_mem (hB.contained c.property))) k.property⟩
  refine ⟨⟨b, hb⟩, q, ?_, ?_, ?_⟩
  · intro he
    have he' := congrArg (fun D : Subgroup A => D.map (MulAut.conj (b⁻¹)).toMonoidHom) he
    rw [Frobenius21.conjugate_map_mul, Frobenius21.conjugate_map_mul] at he'
    have hp : b⁻¹ * (q : A) = (c : A)⁻¹ * k := by dsimp [q]; group
    simp only [hp, inv_mul_cancel] at he'
    have h1 : C.map (MulAut.conj (1 : A)).toMonoidHom = C :=
      mem_normalizer_iff_map_conj_eq.mp (Subgroup.one_mem _)
    rw [h1] at he'
    have he'' := congrArg (fun D : Subgroup A => D.map (MulAut.conj (c : A)).toMonoidHom) he'
    rw [Frobenius21.conjugate_map_mul] at he''
    have hp' : (c : A) * ((c : A)⁻¹ * k) = k := by group
    have hn : C.map (MulAut.conj (c : A)).toMonoidHom = C :=
      mem_normalizer_iff_map_conj_eq.mp (C.le_normalizer c.property)
    rw [hp', hn] at he''
    exact hk he''.symm
  · rintro ⟨w, hw, hwv⟩
    have he : w = x := (ρ.apply_bijective b).injective (hwv.trans hbx.symm)
    exact hxS (he ▸ hw)
  · rintro ⟨w, hw, hwv⟩
    apply hc
    refine ⟨w, hw, ?_⟩
    have hh := congrArg (ρ ((c : A)*b⁻¹)) (hwv.trans hbx.symm)
    have hp : (c : A)*b⁻¹*(q : A) = k := by dsimp [q]; group
    have hp' : (c : A)*b⁻¹*b = c := by group
    simpa only [← Module.End.mul_apply, ← map_mul, hp, hp'] using hh

end Representation.RegularCyclicNormalClosure
