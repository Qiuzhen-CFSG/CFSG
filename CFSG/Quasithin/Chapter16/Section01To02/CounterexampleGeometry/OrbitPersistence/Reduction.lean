module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.Basic
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# The two-component orbit and the persistence reduction

Nonnormality supplies a moved component. A.1.34(2) bounds its orbit by two;
Sylow index arithmetic finds a swapping element in T. The persistence proof
uses conjugation by the swapped factor, which fixes L and z. In particular,
the printed phrase “conjugating in L” cannot supply this reduction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
pp.1174–1175, the construction preceding 16.2.5 and Lemma 16.2.6.
The earlier-source and model hypotheses of the conditional deductions remain
obligations of the source-theorem assembly.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry
universe v
variable {G : Type v} [Group G] {T : Sylow 2 G} {z : G} {L : Subgroup G} {u : G}

private theorem normalizer_index_of_pair {M : Subgroup G} {g : G}
    (hg : g ∈ M) (hm : conjugate L g ≠ L)
    (horbit : ∀ x ∈ M, conjugate L x = L ∨ conjugate L x = conjugate L g) :
    (normalizer (L : Set G)).relIndex M = 2 := by
  apply relIndex_eq_two_iff_exists_notMem_and.mpr
  refine ⟨g⁻¹, M.inv_mem hg, ?_, ?_⟩
  · intro h
    exact hm ((mem_normalizer_iff_conjugate_eq L g).mp
      ((normalizer (L : Set G)).inv_mem_iff.mp h))
  · intro x hx
    rcases horbit x hx with h | h
    · exact Or.inr ((mem_normalizer_iff_conjugate_eq L x).mpr h)
    · left
      apply (mem_normalizer_iff_conjugate_eq L (x * g⁻¹)).mpr
      rw [← conjugate_conjugate, h, conjugate_conjugate, mul_inv_cancel, conjugate_one]

/-- Perfect subgroups fix each component when isomorphic components occur in pairs. -/
theorem perfect_le_component_normalizer {K : GroupClass.{v}}
    (a134 : ComponentPairExhaustion K G)
    {H P J : Subgroup G} (hH : IsKGroup K H) (hPH : P ≤ H)
    [Group.IsPerfect P] (hJ : IsComponentIn J H) : P ≤ normalizer (J : Set G) := by
  by_cases hHn : H ≤ normalizer (J : Set G)
  · exact hPH.trans hHn
  obtain ⟨g, hg, hgn⟩ := SetLike.not_le_iff_exists.mp hHn
  have hm : conjugate J g ≠ J := fun he => hgn
    ((mem_normalizer_iff_conjugate_eq J g).mpr he)
  have hconj (x : G) (hx : x ∈ H) : IsComponentIn (conjugate J x) H := by
    have he : conjugate H x = H :=
      (mem_normalizer_iff_conjugate_eq H x).mp (H.le_normalizer hx)
    have hc := hJ.map (MulAut.conj x⁻¹)
    change IsComponentIn (conjugate J x) (conjugate H x) at hc
    rwa [he] at hc
  have horbit (x : G) (hx : x ∈ H) :
      conjugate J x = J ∨ conjugate J x = conjugate J g :=
    a134 H hH J (conjugate J g) hJ (hconj g hg) hm.symm
      ⟨(MulAut.conj g⁻¹).subgroupMap J⟩ _ (hconj x hx)
      ⟨((MulAut.conj x⁻¹).subgroupMap J).symm⟩
  have hi := normalizer_index_of_pair (L := J) hg hm horbit
  let e := (subgroupOfEquivOfLe hPH).symm
  let : Group.IsPerfect (P.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hle := le_of_isPerfect_of_index_eq_two (P.subgroupOf H)
    ((normalizer (J : Set G)).subgroupOf H) hi
  intro x hx
  exact hle (show (⟨x, hPH hx⟩ : H) ∈ P.subgroupOf H from hx)


namespace CounterexampleSetup
variable [Finite G] {K : GroupClass.{v}} (c : CounterexampleSetup K T z L)
include c

theorem orbit_pair_of_moved (a134 : ComponentPairExhaustion K G)
    {g : G} (hg : g ∈ involutionCentralizer z) (hm : conjugate L g ≠ L) :
    ∀ x ∈ involutionCentralizer z,
      conjugate L x = L ∨ conjugate L x = conjugate L g := by
  intro x hx
  exact a134 _ (c.global.properK _ c.centralizer_ne_top) L (conjugate L g)
    c.localSetup.component (local_conjugate_component c.localSetup hg) hm.symm
    ⟨(MulAut.conj g⁻¹).subgroupMap L⟩ _
    (local_conjugate_component c.localSetup hx) ⟨((MulAut.conj x⁻¹).subgroupMap L).symm⟩

theorem exists_twoComponentOrbit (a134 : ComponentPairExhaustion K G) :
    ∃ u : G, TwoComponentOrbit T z L u := by
  have hn : ¬ involutionCentralizer z ≤ normalizer (L : Set G) := fun hn =>
    c.not_normal ((normal_subgroupOf_iff_le_normalizer c.localSetup.component.1).mpr hn)
  obtain ⟨g, hg, hgn⟩ := SetLike.not_le_iff_exists.mp hn
  have hm : conjugate L g ≠ L := fun he => hgn
    ((mem_normalizer_iff_conjugate_eq L g).mpr he)
  have hi := normalizer_index_of_pair hg hm (c.orbit_pair_of_moved a134 hg hm)
  have htn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := by
    intro ht
    have hd := index_dvd_of_le (show (T.subtype c.localSetup.sylow_centralizes :
        Subgroup (involutionCentralizer z)) ≤
        (normalizer (L : Set G)).subgroupOf (involutionCentralizer z) from
      fun _ hx => ht hx)
    change (normalizer (L : Set G)).relIndex (involutionCentralizer z) ∣ _ at hd
    rw [hi] at hd
    exact (T.subtype c.localSetup.sylow_centralizes).not_dvd_index hd
  obtain ⟨u, hu, hun⟩ := SetLike.not_le_iff_exists.mp htn
  have hm : conjugate L u ≠ L := fun he => hun
    ((mem_normalizer_iff_conjugate_eq L u).mpr he)
  exact ⟨u, hu, hm, c.orbit_pair_of_moved a134 (c.localSetup.sylow_centralizes hu) hm⟩
end CounterexampleSetup

namespace TwoComponentOrbit
variable (o : TwoComponentOrbit T z L u) (h : CentralComponentSetup T z L)
include o h

theorem normalizer_index : (normalizer (L : Set G)).relIndex (T : Subgroup G) = 2 :=
  normalizer_index_of_pair o.mem_sylow o.moved
    (fun x hx => o.orbit x (h.sylow_centralizes hx))

theorem normalizer_inter_eq :
    (T : Subgroup G) ⊓ normalizer (conjugate L u : Set G) =
      (T : Subgroup G) ⊓ normalizer (L : Set G) := by
  ext x
  constructor
  · rintro ⟨hxT, hx⟩
    refine ⟨hxT, (mem_normalizer_iff_conjugate_eq L x).mpr ?_⟩
    rcases o.orbit x (h.sylow_centralizes hxT) with he | he
    · exact he
    · have hU := (mem_normalizer_iff_conjugate_eq (conjugate L u) x).mp hx
      exact (o.moved ((conjugate_injective x (he.trans hU.symm)).symm)).elim
  · rintro ⟨hxT, hx⟩
    refine ⟨hxT, (mem_normalizer_iff_conjugate_eq (conjugate L u) x).mpr ?_⟩
    rcases o.orbit (u * x) ((involutionCentralizer z).mul_mem
      (h.sylow_centralizes o.mem_sylow) (h.sylow_centralizes hxT)) with he | he
    · have hL := (mem_normalizer_iff_conjugate_eq L x).mp hx
      have he' : conjugate (conjugate L u) x = conjugate L x := by
        rw [conjugate_conjugate, he, hL]
      exact (o.moved (conjugate_injective x he')).elim
    · simpa only [conjugate_conjugate] using he
end TwoComponentOrbit
end CFSG.Quasithin.Chapter16.CounterexampleGeometry

end
