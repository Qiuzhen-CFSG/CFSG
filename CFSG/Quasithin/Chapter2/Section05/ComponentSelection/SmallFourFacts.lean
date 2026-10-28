module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallModelFacts
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearPrimeFourNormalizerSource
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.FourFixerSylow
public import Theory.SpecificGroups.PSL3Two.FourNormalizers
public import Theory.SpecificGroups.PSL3Three.FourFixerSylow
public import Theory.Mathieu.M11.Properties.FourNormalizer
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import Theory.SpecificGroups.PSL2.PrimeFourFixers
public import Theory.GroupAction.FourFixerSylowTransport

/-!
# Four-group normalizers and automorphism fixers for the exact source catalogue

Each surviving model has an actual S₄ four-group normalizer. Its full
pointwise automorphism fixer lies in every full automorphism Sylow subgroup
containing the inner four-group. Sylow images transfer the latter statement
to each literal source action. The prime branch retains precisely p > 7,
p Fermat or Mersenne, as in 2.5.2(4).

Source: Aschbacher--Smith 2.5.8(5), printed pp.556--557.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup
open scoped MatrixGroups

private theorem four_normalizer_transport {K L : Type*} [Group K] [Group L]
    (e : K ≃* L) (h : ∀ F : Subgroup L, IsKleinFour F →
      Nonempty (normalizer (F : Set L) ≃* Equiv.Perm (Fin 4)))
    (F : Subgroup K) [IsKleinFour F] :
    Nonempty (normalizer (F : Set K) ≃* Equiv.Perm (Fin 4)) := by
  let eF := F.equivMapOfInjective e.toMonoidHom e.injective
  have hF : IsKleinFour (F.map e.toMonoidHom) := {
    card_four := (Nat.card_congr eF.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eF).symm.trans IsKleinFour.exponent_two }
  obtain ⟨f⟩ := h (F.map e.toMonoidHom) hF
  exact ⟨((e.subgroupMap (normalizer (F : Set K))).trans
    (MulEquiv.subgroupCongr (map_equiv_normalizer_eq F e))).trans f⟩

/-- The actual S₄ normalizer in every surviving component model. -/
theorem IsSmallRemainingComponent.four_normalizer {K : Type*} [Group K]
    (h : IsSmallRemainingComponent K) (F : Subgroup K) [IsKleinFour F] :
    Nonempty (normalizer (F : Set K) ≃* Equiv.Perm (Fin 4)) := by
  unfold IsSmallRemainingComponent at h
  rcases h with h | h | h | h | h
  · obtain ⟨e⟩ := h
    exact four_normalizer_transport e (fun E hE => by
      let := hE; exact AlternatingSix.ShadowLocal.four_normalizer_equiv_symmetric E) F
  · obtain ⟨e⟩ := h
    exact four_normalizer_transport e (fun E hE => by
      let := hE; exact Matrix.PSL3Two.four_normalizer E) F
  · obtain ⟨e⟩ := h
    exact four_normalizer_transport e (fun E hE => by
      let := hE
      let : IsElementaryAbelian 2 E := {
        toIsMulCommutative := IsKleinFour.isMulCommutative
        exponent_dvd_p := by simp }
      exact Matrix.PSL3Three.normalizer_four_nonempty_equiv E inferInstance IsKleinFour.card_four) F
  · obtain ⟨e⟩ := h
    exact (Sporadic.Mathieu.m11_four_structure_of_equiv e F).2
  · obtain ⟨p, hp, hb, ⟨e⟩⟩ := h
    let : Fact p.Prime := ⟨hp.1⟩
    exact four_normalizer_transport e (fun E hE => by
      let := hE; exact linear_prime_four_normalizer p hp hb E) F

/-- Full automorphism containment for a specified inner four-group and Sylow. -/
theorem IsSmallRemainingComponent.four_fixed_mem_sylow {K : Type*} [Group K] [Finite K]
    (h : IsSmallRemainingComponent K) (P : Sylow 2 (MulAut K))
    (F : Subgroup K) [IsKleinFour F] (hFP : F.map MulAut.conj ≤ P)
    (a : MulAut K) (ha : ∀ x ∈ F, a x = x) : a ∈ P := by
  unfold IsSmallRemainingComponent at h
  rcases h with h | h | h | h | h
  · obtain ⟨e⟩ := h
    exact Theory.GroupAction.four_fixer_mem_sylow_of_equiv e (fun Q E hE hEQ b hb => by
      let := hE; exact AlternatingSix.ShadowLocal.four_fixed_mem_sylow Q E hEQ b hb) P F hFP a ha
  · obtain ⟨e⟩ := h
    apply Theory.GroupAction.four_fixer_mem_sylow_of_equiv e _ P F hFP a ha
    intro Q E hE hEQ b hb
    let := hE
    obtain ⟨x, hx, rfl⟩ := Matrix.PSL3Two.four_fixed_inner E b hb
    exact hEQ (mem_map_of_mem MulAut.conj hx)
  · obtain ⟨e⟩ := h
    exact Theory.GroupAction.four_fixer_mem_sylow_of_equiv e (fun Q E hE hEQ b hb => by
      let := hE; exact Matrix.PSL3Three.four_fixed_mem_sylow Q E hEQ b hb) P F hFP a ha
  · obtain ⟨e⟩ := h
    apply Theory.GroupAction.four_fixer_mem_sylow_of_equiv e _ P F hFP a ha
    intro Q E hE hEQ b hb
    let := hE
    obtain ⟨x, rfl⟩ := Sporadic.Mathieu.automorphism_inner_of_equiv_m11 (MulEquiv.refl _) b
    have hx : x ∈ centralizer (E : Set Sporadic.Mathieu.M11) := by
      intro y hy
      exact (mul_inv_eq_iff_eq_mul.mp (hb y hy)).symm
    rw [Sporadic.Mathieu.m11_four_centralizer E] at hx
    exact hEQ (mem_map_of_mem MulAut.conj hx)
  · obtain ⟨p, hp, hb, ⟨e⟩⟩ := h
    let : Fact p.Prime := ⟨hp.1⟩
    apply Theory.GroupAction.four_fixer_mem_sylow_of_equiv e _ P F hFP a ha
    intro Q E hE hEQ b hbfix
    let := hE
    obtain ⟨x, hx, rfl⟩ := Theory.PSL2.primeField_four_fixed_inner
      (hp.1.odd_of_ne_two (by omega)) (by omega) E b hbfix
    exact hEQ (mem_map_of_mem MulAut.conj hx)

/-- The source image form of 2.5.8(5), for the specified action homomorphism. -/
theorem IsSmallRemainingComponent.four_fixed_mem_sylow_image
    {K H : Type*} [Group K] [Finite K] [Group H] [Finite H]
    (h : IsSmallRemainingComponent K) (α : H →* MulAut K) (S : Sylow 2 H)
    (F : Subgroup K) [IsKleinFour F]
    (hFS : F.map MulAut.conj ≤ (S : Subgroup H).map α)
    (a : MulAut K) (ha : a ∈ α.range) (hfix : ∀ x ∈ F, a x = x) :
    a ∈ (S : Subgroup H).map α := by
  apply Theory.GroupAction.mem_sylow_image_of_full_sylow α S a ha
  intro P hSP
  exact h.four_fixed_mem_sylow P F (hFS.trans hSP) a hfix

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
