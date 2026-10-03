module

public import Stellmacher.Recognition.Parrott.CentralizerStructure

/-!
# Candidate orders of Parrott's derived-subgroup normalizer

Under the original centralizer hypotheses, let `H = C_G(z)`, `J = O₂(H)`,
and let `E` be the actual ambient image of `J'`. The normalizer of `E`
has order `10240 * n` for `n` equal to 1, 11, 21, or 31. This counting
step needs no simplicity or local-solvability hypothesis on the ambient
group.

The subgroup `H` normalizes `E` by characteristic transfer. The actual
normalizer acts on `E` by conjugation, and the stabilizer of `z` is exactly
`H`. Hence the orbit of `z` has size `[N_G(E):H]` and is contained in the
31 nonidentity elements of `E`. Restricting this orbit action along the
original Sylow five-subgroup of `H` fixes exactly `z`: the original
centralizer condition places every fixed orbit element in `Z(J) = ⟨z⟩`.
Orbit counting therefore gives size congruent to one modulo five.

The first lemma promotes a Sylow two-subgroup of `H` to an ambient Sylow,
so `H` has odd index in the ambient group and consequently in `N_G(E)`.
The positive odd sizes at most 31 congruent to one modulo five are exactly
the four displayed values. All actions and subgroup maps use the supplied
centralizer, core, and Sylow subgroup.

Source: David Parrott, *A characterization of the Tits' simple group*
(1972), Lemma 2, p. 673. This proves the candidate-order step without
requiring the full classification of the nontrivial `H`-orbits in `E`.
-/

open Subgroup

namespace Stellmacher.Recognition

/-- The four possible orders of the actual normalizer of Parrott's derived subgroup. -/
public theorem parrott_derived_normalizer_card {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∃ n ∈ ({1, 11, 21, 31} : Finset ℕ),
      Nat.card (normalizer (E : Set G)) = 10240 * n := by
  classical
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let DH := D.map J.subtype
  let E := D.map (H.subtype.comp J.subtype)
  let N := normalizer (E : Set G)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨hZmap, _, _, _, hUpper, _, hDcard, hSylow⟩ := parrott_centralizer_structure z h
  change D = Subgroup.upperCentralSeries J 2 at hUpper
  change Nat.card D = 32 at hDcard
  have hEcard : Nat.card E = 32 := by
    exact (card_map_of_injective (K := D) (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)).trans hDcard
  have hZD : center J ≤ D := by
    rw [hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using
      (Subgroup.upperCentralSeries_mono J (show 1 ≤ 2 by decide))
  have hzE : z ∈ E := by
    apply (map_mono hZD (f := H.subtype.comp J.subtype))
    rw [hZmap]
    exact mem_zpowers z
  have hz : z ≠ 1 := by
    intro hz
    have := h.involution
    simp [hz] at this
  have hEH : DH.map H.subtype = E := by
    simp only [DH, E, Subgroup.map_map]
  let : DH.Characteristic := inferInstance
  have hHN : H ≤ N := by
    have hh := Subgroup.le_normalizer_map (H := DH) H.subtype
    rw [Subgroup.normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, H.range_subtype, hEH] using hh
  obtain ⟨hHcard, _⟩ := h.card_and_solvable z
  change Nat.card H = 10240 at hHcard
  let : MulDistribMulAction N E :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer N E le_rfl
  let zE : E := ⟨z, hzE⟩
  have hzEne : zE ≠ 1 := fun heq => hz (congrArg Subtype.val heq)
  let X := MulAction.orbit N zE
  let x0 : X := ⟨zE, MulAction.mem_orbit_self zE⟩
  have hsub : MulAction.orbit N zE ⊆ ({1} : Set E)ᶜ := by
    intro x hx
    obtain ⟨a, rfl⟩ := MulAction.mem_orbit_iff.mp hx
    change a • zE ≠ 1
    intro heq
    apply hzEne
    simpa using congrArg (fun y : E => a⁻¹ • y) heq
  have hXbound : Nat.card X ≤ 31 := by
    have hc : (({1} : Set E)ᶜ).ncard = 31 := by
      rw [Set.ncard_compl, hEcard, Set.ncard_singleton]
    exact (Set.ncard_le_ncard hsub).trans_eq hc
  have hstab : MulAction.stabilizer N zE = H.subgroupOf N := by
    ext a
    rw [MulAction.mem_stabilizer_iff]
    change a • zE = zE ↔ (a : G) ∈ H
    rw [Subtype.ext_iff]
    change (a : G) * z * (a : G)⁻¹ = z ↔ (a : G) ∈ H
    exact mul_inv_eq_iff_eq_mul.trans mem_centralizer_singleton_iff.symm
  have hindex : H.relIndex N = Nat.card X := by
    rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, Nat.card_coe_set_eq]
  have hNcard : Nat.card N = 10240 * H.relIndex N := by
    have hc := (H.subgroupOf N).index_mul_card
    have hHsubcard : Nat.card (H.subgroupOf N) = 10240 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv, hHcard]
    rw [hHsubcard] at hc
    change H.relIndex N * 10240 = Nat.card N at hc
    simpa only [Nat.mul_comm] using hc.symm
  have hnot2 : ¬ 2 ∣ H.relIndex N := by
    let T : Sylow 2 H := Classical.choice inferInstance
    obtain ⟨S, hS⟩ := hSylow T
    have hSH : (S : Subgroup G) ≤ H := by
      rw [hS]
      exact map_subtype_le _
    intro hdiv
    exact S.not_dvd_index (hdiv.trans
      ((Subgroup.relIndex_dvd_index_of_le hHN).trans (Subgroup.index_dvd_of_le hSH)))
  obtain ⟨P, hP⟩ := h.five_centralizer
  have hPcard : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, hHcard]
    decide +kernel
  let iPN : P →* N := (Subgroup.inclusion hHN).comp (P : Subgroup H).subtype
  let : MulAction P X := MulAction.compHom X iPN
  have hx0fixed : x0 ∈ MulAction.fixedPoints P X := by
    rw [MulAction.mem_fixedPoints]
    intro p
    apply Subtype.ext
    apply Subtype.ext
    change ((p : H) : G) * z * ((p : H) : G)⁻¹ = z
    rw [mem_centralizer_singleton_iff.mp (p : H).property]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hfixed : MulAction.fixedPoints P X = {x0} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨hx0fixed, ?_⟩
    intro x hx
    obtain ⟨d, hd, hdx⟩ := (x : E).property
    have hdcenter : d ∈ center J := by
      apply hP
      change (d : H) ∈ centralizer (P : Set H)
      intro a ha
      apply Subtype.ext
      have hfix := congrArg (fun y : X => ((y : E) : G))
        (MulAction.mem_fixedPoints.mp hx ⟨a, ha⟩)
      change (a : G) * ((x : E) : G) * (a : G)⁻¹ = ((x : E) : G) at hfix
      rw [← hdx] at hfix
      exact mul_inv_eq_iff_eq_mul.mp hfix
    have hxcyclic : ((x : E) : G) ∈ zpowers z := by
      rw [← hdx, ← hZmap]
      exact mem_map_of_mem (H.subtype.comp J.subtype) hdcenter
    have hxne : ((x : E) : G) ≠ 1 := by
      intro heq
      exact hsub x.property (Subtype.ext heq)
    rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hxcyclic
    obtain ⟨n, hn, hne⟩ := Finset.mem_image.mp hxcyclic
    have hnlt : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · exact (hxne (by simpa using hne.symm)).elim
    · apply Subtype.ext
      change (x : E) = zE
      apply Subtype.ext
      change ((x : E) : G) = z
      simpa using hne.symm
  have hmod : Nat.card X % 5 = 1 := by
    have hfive : IsPGroup 5 P := IsPGroup.of_card (p := 5) (n := 1) (by simpa using hPcard)
    have hm := hfive.card_modEq_card_fixedPoints X
    rw [hfixed] at hm
    simpa only [Nat.card_unique, Nat.ModEq] using hm
  refine ⟨H.relIndex N, ?_, hNcard⟩
  have hbound : H.relIndex N ≤ 31 := hindex ▸ hXbound
  have hmod5 : H.relIndex N % 5 = 1 := hindex ▸ hmod
  have hmod2 : H.relIndex N % 2 ≠ 0 := by
    intro heq
    exact hnot2 (Nat.dvd_of_mod_eq_zero heq)
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

end Stellmacher.Recognition
