module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.OrderTwo.Geometry
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SelectedLargestPairSource
public import CFSG.Quasithin.Chapter2.Section05.NormalComponentPairs.Source

/-!
# Largest normalizer pairs for every inner four-group

Select a genuine largest source pair and use 2.5.12(1) to identify both
coordinates with the normalizers of one four-group in S ∩ K. The full
Sylow action interchanges the two inner four-groups. Conjugation inside
H ∩ M preserves the local-pair conditions and the order of the base, so
every inner four-group supplies a largest normalizer pair.

The compatible earlier-source setup retains the original H, K, S and M.
No pair correspondence or transitivity premise is assumed.
Source: Aschbacher--Smith, 2.5.12(1,3) and 2.5.23, printed pp.557--558
and 567--568 of the combined manuscript of 1 March 2004.
-/

public section

namespace CFSG.Quasithin.Chapter2.A6Shadow.OriginalFrattini
open Subgroup Frattini Frattini.ElementaryCore Section05
open Section05.ComponentSelection ComponentRefinement

variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}

private theorem four_subgroup_conjugacy (d : EarlierSetup κ G)
    (E F : Subgroup G) (hE : E ≤ d.S ⊓ d.K) (hF : F ≤ d.S ⊓ d.K)
    (hfourE : IsKleinFour E) (hfourF : IsKleinFour F) :
    ∃ s ∈ d.S, E.map (MulAut.conj s).toMonoidHom = F := by
  let := hfourE
  let := hfourF
  obtain ⟨s, hs, hconj⟩ := OrderTwo.four_conjugate d
  have hback : (fourOne d).map (MulAut.conj s).toMonoidHom = fourZero d := by
    have h := congrArg (rightConjugate s⁻¹) hconj
    rw [rightConjugate_inv_cancel] at h
    simpa only [rightConjugate, inv_inv] using h.symm
  rcases four_subgroups d E hE with rfl | rfl <;>
    rcases four_subgroups d F hF with rfl | rfl
  · exact ⟨1, d.S.one_mem, by
      simpa only [rightConjugate, inv_one] using (rightConjugate_one (fourZero d))⟩
  · exact ⟨s⁻¹, d.S.inv_mem hs, hconj⟩
  · exact ⟨s, hs, hback⟩
  · exact ⟨1, d.S.one_mem, by
      simpa only [rightConjugate, inv_one] using (rightConjugate_one (fourOne d))⟩

private theorem normalizer_pair_largest_of_one (d : EarlierSetup κ G)
    (F : Subgroup G) (hF : F ≤ d.S ⊓ d.K) (hfourF : IsKleinFour F)
    (hp : (d.S ⊓ normalizer (F : Set G), d.H ⊓ normalizer (F : Set G)) ∈
      largestLocalPairs d.M d.H)
    (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) (hfourE : IsKleinFour E) :
    (d.S ⊓ normalizer (E : Set G), d.H ⊓ normalizer (E : Set G)) ∈
      largestLocalPairs d.M d.H := by
  obtain ⟨s, hs, hFE⟩ := four_subgroup_conjugacy d F E hF hE hfourF hfourE
  let e := MulAut.conj s
  have hS : d.S.map e.toMonoidHom = d.S :=
    mem_normalizer_iff_map_conj_eq.mp (d.S.le_normalizer hs)
  have hH : d.H.map e.toMonoidHom = d.H :=
    mem_normalizer_iff_map_conj_eq.mp (d.H.le_normalizer (d.s_le_h hs))
  have hN : (normalizer (F : Set G)).map e.toMonoidHom =
      normalizer (E : Set G) := by
    rw [map_equiv_normalizer_eq, hFE]
  have hU : (d.S ⊓ normalizer (F : Set G)).map e.toMonoidHom =
      d.S ⊓ normalizer (E : Set G) := by
    rw [map_inf _ _ _ e.injective, hS, hN]
  have hL : (d.H ⊓ normalizer (F : Set G)).map e.toMonoidHom =
      d.H ⊓ normalizer (E : Set G) := by
    rw [map_inf _ _ _ e.injective, hH, hN]
  have hlocal := local_pair_conjugate hp.1 (d.s_le_h hs)
    ((d.s_le_t.trans d.t_le_m) hs)
  refine ⟨?_, ?_⟩
  · change ((d.S ⊓ normalizer (F : Set G)).map e.toMonoidHom,
      (d.H ⊓ normalizer (F : Set G)).map e.toMonoidHom) ∈ _ at hlocal
    simpa only [hU, hL] using hlocal
  · intro W hW
    exact (hp.2 W hW).trans_eq ((Nat.card_congr
      (e.subgroupMap (d.S ⊓ normalizer (F : Set G))).toEquiv).trans
        (congrArg (fun V : Subgroup G => Nat.card V) hU))

variable {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The forward normalizer-pair assertion of original 2.5.23. The four
compatibility equalities identify the earlier setup with the original
source tuple and are supplied by `original_earlier_setup`. -/
theorem normalizer_pairs_of_source
    (c : ComponentRefinement.MathieuSourceSetup H K M S z)
    [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (d : EarlierSetup KnownSimple.IsKnownSimple G)
    (hH : d.H = H) (hK : d.K = K)
    (hS : d.S = (S : Subgroup H).map H.subtype) (hM : d.M = M)
    (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) (hfourE : IsKleinFour E) :
    (d.S ⊓ normalizer (E : Set G), d.H ⊓ normalizer (E : Set G)) ∈
      largestLocalPairs d.M d.H := by
  obtain ⟨U, L, hp, hUS, _⟩ :=
    ComponentSelection.MathieuSourceSetup.exists_largest_pair_in_sylow c hstar
  obtain ⟨F, hF, hfourF, hL, hU, _⟩ :=
    largest_pair_four_normalizers_of_source c hG hempty hgen hb hp hUS
  have hFd : F ≤ d.S ⊓ d.K := by simpa only [hS, hK] using hF
  apply normalizer_pair_largest_of_one d F hFd hfourF _ E hE hfourE
  simpa only [hH, hS, hM, hU, hL] using hp

end CFSG.Quasithin.Chapter2.A6Shadow.OriginalFrattini
