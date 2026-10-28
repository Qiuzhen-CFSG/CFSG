module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.ComponentAction
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ComponentOrbitBound
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness
public import CFSG.KnownSimple.CarrierCatalogue
public import FeitThompson.FinalTheorem

/-!
# Normalization and Sylow subgroups in 13.5.21

The odd-order theorem supplies evenness of the selected simple section.
The proved A.3.8 orbit bound lifts through the actual two-core quotient,
making N_H(K) normal in H. Two-perfectness places L₁ inside N_H(K), and
normal Sylow restriction gives T_X in Syl₂(N_H(K)) and Syl₂(X).
This uses the full known-simple proper-K input, with no component-model
alternatives. The 13.5.19 conclusions remain explicit for the actual Y.

Source: Aschbacher–Smith, combined manuscript, 1.2.1(3), p.504,
and 13.5.21, p.923 (PDF p.940).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
open Section08.Source
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}

/-- The simple central section of the selected component has even order. -/
theorem selected_section_even (s : Selected D K) :
    2 ∣ Nat.card (starImage D.H K ⧸ center (starImage D.H K)) := by
  let := s.quasisimple
  let : IsSimpleGroup (starImage D.H K ⧸ center (starImage D.H K)) :=
    IsQuasisimple.simple
  let : Group.IsPerfect (starImage D.H K ⧸ center (starImage D.H K)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  by_contra hn
  exact Group.IsPerfect.not_isSolvable _ (odd_order_theorem _
    (Nat.not_even_iff_odd.mp (fun he => hn (even_iff_two_dvd.mp he))))

/-- The opening commutator and normalization step, with parity discharged. -/
theorem selected_actor_normalization (s : Selected D K) (h : D.Hypothesis)
    (hindex : D.Vplus.relIndex D.V = 2) (hU : ¬ IsMulCommutative D.UH) :
    D.V ≤ normalizer (K : Set G) ∧
      ⁅starImage D.H K, starImage D.H D.V⁆ = starImage D.H K := by
  obtain ⟨hn, hc⟩ := s.normalizes_and_commutator_of_nonabelian h hindex hU
    (selected_section_even s)
  exact ⟨s.normalizes_of_star _ h.V_le_H hn, hc⟩

/-- The adequate orbit clause of 1.2.1(3), using the full proper-K input.
No component-model alternative is needed. -/
theorem selected_orbit (s : Selected D K)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G) :
    (K.subgroupOf D.H).Normal ∨
      (normalizer (K.subgroupOf D.H : Set D.H)).index = 2 := by
  let := pCore_isNilpotent (p := 2) (G := D.H)
  apply cComponent_normal_or_index_two_of_quotient s.ccomponent (pCore 2 D.H)
  exact ChapterA.Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
    (ChapterA.Section03.CComponentCommutation.noncentralStructureInput
      KnownSimple.IsKnownSimple)
    (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hH)
    (pCore_quotient_pCore_eq_bot 2) (s.ccomponent.map_quotient _)

/-- L₁ is a two-residual, so the normal-or-index-two orbit forces it to
normalize the selected component. -/
theorem selected_local_normalization (s : Selected D K) (h : D.Hypothesis)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G) :
    D.L₁ ≤ normalizer (K : Set G) := by
  have hLH : D.L₁ ≤ D.H := le_sup_left.trans h.local_le
  have hp : IsPPerfect 2 (D.L₁.subgroupOf D.H) :=
    (isPPerfect_embedded_pResidual 2 (D.L ⊓ D.Gz)).of_surjective
      (subgroupOfEquivOfLe hLH).symm.toMonoidHom
      (subgroupOfEquivOfLe hLH).symm.surjective
  have hnorm : D.L₁.subgroupOf D.H ≤ normalizer (K.subgroupOf D.H : Set D.H) := by
    rcases selected_orbit s hG hH with hn | hi
    · let := hn
      exact le_normalizer_of_normal
    · let N := normalizer (K.subgroupOf D.H : Set D.H)
      let : N.Normal := normal_of_index_eq_two hi
      have hq : IsPGroup 2 (D.H ⧸ N) := IsPGroup.of_card (n := 1) hi
      exact (le_pResidual_of_isPPerfect _ hp).trans (sInf_le ⟨inferInstance, hq⟩)
  rw [← subgroupOf_normalizer_eq s.le_H] at hnorm
  intro x hx
  exact hnorm (show (⟨x, hLH hx⟩ : D.H) ∈ D.L₁.subgroupOf D.H from hx)

/-- The literal star images have the normalization used by ComponentAction. -/
theorem selected_star_local_normalization (s : Selected D K) (h : D.Hypothesis)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G) :
    starImage D.H D.L₁ ≤ normalizer (starImage D.H K : Set (Hstar D.H)) := by
  have hn : D.L₁.subgroupOf D.H ≤ normalizer (K.subgroupOf D.H : Set D.H) := by
    rw [← subgroupOf_normalizer_eq s.le_H]
    exact comap_mono (selected_local_normalization s h hG hH)
  exact (map_mono hn).trans (le_normalizer_map _)

/-- The normalizer in H is normal, including the nonnormal two-orbit case. -/
theorem selected_normalizer_normal (s : Selected D K)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G) :
    (normalizer (K.subgroupOf D.H : Set D.H)).Normal := by
  rcases selected_orbit s hG hH with hn | hi
  · let := hn
    rw [normalizer_eq_top]
    infer_instance
  · exact normal_of_index_eq_two hi

/-- The actual T_X is Sylow in N_H(K). -/
theorem TX_sylow_normalizer (s : Selected D K) (h : D.Hypothesis)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G) :
    Chapter1.IsSylowIn 2 (TX D K) (D.H ⊓ normalizer (K : Set G)) := by
  let N := normalizer (K.subgroupOf D.H : Set D.H)
  let : N.Normal := selected_normalizer_normal s hG hH
  obtain ⟨P, hP⟩ := (D.T.subtype h.T_le_H).exists_subgroupOf_eq_of_normal N
  have hi : Chapter1.IsSylowIn 2
      (((D.T.subtype h.T_le_H : Sylow 2 D.H) : Subgroup D.H) ⊓ N) N := by
    refine ⟨P, ?_⟩
    rw [hP, subgroupOf_map_subtype]
  have hm := (Chapter1.IsSylowIn.map_iff D.H.subtype D.H.subtype_injective).mpr hi
  have hN : N.map D.H.subtype = D.H ⊓ normalizer (K : Set G) := by
    rw [show N = (normalizer (K : Set G)).subgroupOf D.H from
      (subgroupOf_normalizer_eq s.le_H).symm, subgroupOf_map_subtype, inf_comm]
  have hS : (((D.T.subtype h.T_le_H : Sylow 2 D.H) : Subgroup D.H) ⊓ N).map
      D.H.subtype = TX D K := by
    rw [map_inf _ _ _ D.H.subtype_injective, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le h.T_le_H, hN]
    rw [← inf_assoc, inf_eq_left.mpr h.T_le_H]
    rfl
  simpa only [hN, hS] using hm

/-- T_X remains Sylow in the source product X=K L₁ T_X. -/
theorem TX_sylow_X (s : Selected D K) (h : D.Hypothesis)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G) :
    Chapter1.IsSylowIn 2 (TX D K) (X D K) := by
  apply (TX_sylow_normalizer s h hG hH).restrict
    (le_sup_right.trans le_sup_right)
  exact le_inf (s.X_le_H h) (sup_le K.le_normalizer
    (sup_le (selected_local_normalization s h hG hH) inf_le_right))

/-- Both clauses of 13.5.19 now give the Y- and L₁-commutator conclusions
without a normalization or parity premise. Y is the original chosen subgroup. -/
theorem selected_local_commutators (s : Selected D K) (h : D.Hypothesis)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G)
    (Y : Subgroup G) (hYL : Y ≤ D.L₁)
    (himage : starImage D.H (D.H ⊓ normalizer (Y : Set G)) =
      normalizer (starImage D.H Y : Set (Hstar D.H)))
    (hcore : D.V ≤ (D.H ⊓ normalizer (Y : Set G)).pCoreIn 2) :
    ⁅starImage D.H K, starImage D.H Y⁆ = starImage D.H K ∧
      ⁅starImage D.H K, starImage D.H D.L₁⁆ = starImage D.H K :=
  s.full_local_commutator Y hYL himage hcore
    (selected_star_local_normalization s h hG hH)

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
