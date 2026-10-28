module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SQTKSectionImage
public import CFSG.Quasithin.ChapterB.Section01.IrreducibleSections
public import Theory.Representation.BinaryOffender.Stability

/-!
# Structural reductions for the noncentral branch of B.1.13

Let L be the selected component, with [L,K] = L, and suppose that the
best-offender subgroup J(G,V) normalizes L. The three-subgroup lemma shows
that some best offender A contained in the original T moves L. The component
commutator dichotomy then gives [L,A] = L. Applying the proved B.1.11 theorem
constructs an actual Irr⁺ section I/C_I(L), its FF action image and the
relative centralizer bound; no section witness is assumed.

For quasisimple K subnormal in H = K ⊔ T, component calculus gives containment
in L or centralization of H ∩ L. Once K is properly contained in L, that
intersection is proper in L, for both the quasisimple and order-three cases.
All subnormality is relative to the displayed overgroup.

These are structural steps, not the classification alternatives of B.1.13.
General K-group FF recognition, alternating-cover exclusion, the order-three
intersection argument and the model Sylow-overgroup restrictions remain to
be assembled. In particular, the general K hypothesis is not replaced by SQTK.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, B.1.13, printed pp. 73–74 (PDF pp. 84–85).
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition
open Subgroup Theory.GroupTheory Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The local offender commutator lies in the normal global offender subgroup. -/
theorem le_offenderSubgroup_of_local_commutator (K T : Subgroup G)
    (hK : K = ⁅K, generatedBy {A | IsBestOffender ρ A} T⁆) :
    K ≤ offenderSubgroup ρ := by
  let := offenderSubgroup_normal ρ
  have hJ : generatedBy {A | IsBestOffender ρ A} T ≤ offenderSubgroup ρ := by
    unfold generatedBy offenderSubgroup
    exact iSup_le fun A => iSup_le fun hA => le_iSup_of_le A
      (le_iSup_of_le ⟨hA.1, le_top⟩ le_rfl)
  rw [hK]
  exact (commutator_mono le_rfl hJ).trans (commutator_le_right _ _)

/-- A selected component is moved by a best offender inside the original T. -/
theorem exists_bestOffender_commutator (K L T : Subgroup G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hK : K = ⁅K, generatedBy {A | IsBestOffender ρ A} T⁆)
    (hN : offenderSubgroup ρ ≤ normalizer (L : Set G)) :
    ∃ A : Subgroup G, IsBestOffender ρ A ∧ A ≤ T ∧ ⁅L, A⁆ = L := by
  classical
  let := hL.2
  let J := generatedBy {A | IsBestOffender ρ A} T
  by_contra! h
  have hJC : J ≤ centralizer (L : Set G) := by
    unfold J generatedBy
    refine iSup_le fun A => iSup_le fun hA => ?_
    have hAJ : A ≤ offenderSubgroup ρ := by
      unfold offenderSubgroup generatedBy
      exact le_iSup_of_le A (le_iSup_of_le ⟨hA.1, le_top⟩ le_rfl)
    have hAL : ⁅L, A⁆ ≤ L :=
      le_normalizer_iff_commutator_le_left.mp (hAJ.trans hN)
    have hbot : ⁅L, A⁆ = ⊥ := by
      rcases hL.commutator_dichotomy A with hb | he
      · exact hb
      · exact (h A hA.1 hA.2 (le_antisymm hAL (he ▸ le_iSup_conjugates L A))).elim
    exact commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm A L).trans hbot)
  have hJL : ⁅J, L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hJC
  have hLJ : ⁅L, J⁆ = ⊥ := (commutator_comm L J).trans hJL
  have hiter : ⁅⁅K, J⁆, L⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate
      (by rw [hJL, commutator_bot_left]) (by rw [hLK, hLJ])
  have hKL : ⁅K, L⁆ = ⊥ := by
    calc
      ⁅K, L⁆ = ⁅⁅K, J⁆, L⁆ := congrArg (fun X => ⁅X, L⁆) hK
      _ = ⊥ := hiter
  have hbot : L = ⊥ := hLK.symm.trans ((commutator_comm L K).trans hKL)
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  have : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  exact (nontrivial_iff_ne_bot L).mp this hbot

/-- The literal B.1.11 section for the component selected in B.1.13. -/
theorem irreducible_ff_section [Finite G] [FiniteDimensional (ZMod 2) V]
    (hfaith : Function.Injective ρ) (K L T : Subgroup G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hK : K = ⁅K, generatedBy {A | IsBestOffender ρ A} T⁆)
    (hN : offenderSubgroup ρ ≤ normalizer (L : Set G)) :
    ∃ (H : Subgroup G) (I : Submodule (ZMod 2) V),
      L ≤ H ∧ IsIrrPlus ρ L I ∧
      ∃ (hHI : H ≤ subspaceStabilizer ρ I) (hHN : H ≤ normalizer (L : Set G)),
        IsFFModule (imageRepresentation (centralSectionRepresentation ρ L H I hHI hHN)) ∧
        (centralSectionRepresentation ρ L H I hHI hHN).ker.map H.subtype ≤
          H ⊓ centralizer (L : Set G) := by
  let := hL.2
  obtain ⟨A, hA, _, hLA⟩ := exists_bestOffender_commutator ρ K L T hL hLK hK hN
  exact source_lemma_B_1_11 ρ hfaith L A hLA hA

end CFSG.Quasithin.ChapterB.ComponentRecognition

namespace CFSG.Quasithin.ChapterB.ComponentRecognition
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

/-- The component alternative in the local overgroup, with ambient subnormality
of L and only relative subnormality of K. -/
theorem quasisimple_local_dichotomy (K L T : Subgroup G)
    [IsQuasisimple K] (hL : IsComponent G L)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) :
    K ≤ L ∨ ⁅K, L ⊓ (K ⊔ T)⁆ = ⊥ := by
  let H := K ⊔ T
  let : IsQuasisimple (K.subgroupOf H) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)).symm
  have hc : IsComponent H (K.subgroupOf H) := ⟨hK, inferInstance⟩
  rcases hc.subnormal_dichotomy (L.subgroupOf H) hL.1.subgroupOf with hle | hcomm
  · left
    have hm := map_mono (f := H.subtype) hle
    rw [map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left), subgroupOf_map_subtype] at hm
    exact hm.trans inf_le_left
  · right
    have hm := congrArg (Subgroup.map H.subtype) hcomm
    simpa only [map_commutator, map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
      subgroupOf_map_subtype, Subgroup.map_bot] using hm

/-- If the local overgroup contains the selected component, its noncentral
subnormal K already contains that component. This also applies when |K| = 3. -/
theorem component_le_of_le_local_overgroup (K L T : Subgroup G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hLH : L ≤ K ⊔ T) : L ≤ K := by
  let H := K ⊔ T
  rcases (hL.subgroupOf hLH).subnormal_dichotomy (K.subgroupOf H) hK with hle | hc
  · have hm := map_mono (f := H.subtype) hle
    simpa only [H, map_subgroupOf_eq_of_le hLH,
      map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left)] using hm
  · have hm := congrArg (Subgroup.map H.subtype) hc
    have hb : L = ⊥ := by
      simpa only [H, map_commutator, map_subgroupOf_eq_of_le hLH,
        map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
        Subgroup.map_bot, hLK] using hm
    exact hb ▸ bot_le

/-- Once K lies properly in L, the actual intersection H ∩ L is proper in L.
No classification of Sylow overgroups or generalized-Fitting assertion is used. -/
theorem local_intersection_lt (K L T : Subgroup G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hKL : K < L) :
    L ⊓ (K ⊔ T) < L := by
  apply lt_of_le_of_ne inf_le_left
  intro he
  have hLH : L ≤ K ⊔ T := he ▸ inf_le_right
  exact hKL.not_ge (component_le_of_le_local_overgroup K L T hL hLK hK hLH)

end CFSG.Quasithin.ChapterB.ComponentRecognition
