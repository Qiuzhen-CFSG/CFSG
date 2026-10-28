module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.NormalClosureComponent
public import Theory.GroupTheory.ConjugatePairSeed.Supplement
public import Theory.GroupTheory.PCoreImage

/-!
# Centralizer supplements in the actual normal Bender row

The extraspecial closure U lies in the two-core Q of the original H.
Since Q acts trivially on U/Z(U), the extraspecial centralizer theorem
expresses Q as U C_Q(U), with intersection the original central involution.
The centralizing factor is normalized by H and lies in the original Sylow
subgroup and the centralizer of the original four-plane.

The already proved inclusion of U in the selected component gives the
same decomposition for its literal embedded two-core. These source
consequences retain the two centralizing factors: eliminating them is the
remaining core-identification step, supplied by F.1.12 in the printed proof.
No identification of U with either full core is asserted here.

Source: Aschbacher–Smith 14.2.16, printed pp.985–986, using the earlier
G.2.2 central-commutator conclusion and the extraspecial closure.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.LocalBinary
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open Chapter12.Section08
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
/-- The actual H-core is the central product of its extraspecial closure
and the literal closure centralizer. -/
theorem source_normal_bender_core_centralizer_reduction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hnH : 1 < generationParameter H)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) H))
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    (f : ℕ) (hm : BenderModel ((H ⊓ M).subgroupOf H) K f) :
    let U := conjugateSpanBy (localModule T M) H
    let Q := H.pCoreIn 2
    let C := Q ⊓ centralizer (U : Set G)
    U ⊔ C = Q ∧ U ⊓ C = centralInvolutions T ∧
      H ≤ normalizer (C : Set G) ∧ C ≤ (T : Subgroup G) ∧
      C ≤ centralizer (localModule T M : Set G) ∧
      (U = Q ↔ C = centralInvolutions T) := by
  let D : ChapterG.Section02.Setup G :=
    { V := localModule T M, V₁ := centralInvolutions T, L := sourceResidual M Mc,
      T := T, H := H }
  obtain ⟨h,hphi,hphic,_⟩ := source_frattini_seed_orbit
    hG T hempty hM hu hmany hcard e H hH.1 hne
  obtain ⟨hx,hZ,ho⟩ := source_normal_bender_closure_extraspecial
    hG T hempty hM hu hmany hcard e H hH hnH hne K hK hqK hgen f hm
  let : IsExtraspecial 2 D.U := hx
  let C := D.QH ⊓ centralizer (D.U : Set G)
  change D.U ⊔ C = D.QH ∧ D.U ⊓ C = D.V₁ ∧
    D.H ≤ normalizer (C : Set G) ∧ C ≤ D.T ∧
    C ≤ centralizer (D.V : Set G) ∧ (D.U = D.QH ↔ C = D.V₁)
  have hcomm : ⁅D.QH,D.U⁆ ≤ D.V₁ := by
    rw [commutator_comm]
    exact h.commutator_U_core_le_point
  have hs := extraspecial_sup_centralizer_eq D.U D.QH D.V₁ h.U_le_core hZ hcomm
  change D.U ⊔ C = D.QH at hs
  have hi : D.U ⊓ C = D.V₁ := by
    change D.U ⊓ (D.QH ⊓ centralizer (D.U : Set G)) = D.V₁
    rw [← inf_assoc,inf_eq_left.mpr h.U_le_core,← map_center_subtype_eq_inf_centralizer]
    exact hZ
  have hQN : D.H ≤ normalizer (D.QH : Set G) := by
    have hh := (pCore 2 D.H).le_normalizer_map D.H.subtype
    rwa [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] at hh
  have hCN : D.H ≤ normalizer (C : Set G) :=
    (le_inf hQN ((le_normalizer_conjugateSpanBy D.V D.H).trans
      (normalizer_le_normalizer_centralizer D.U))).trans inf_normalizer_le_normalizer_inf
  have hQT : D.QH ≤ D.T := by
    obtain ⟨P,hP⟩ := h.sylow_H
    exact (pCoreIn_le_sylow D.H P).trans_eq hP
  refine ⟨hs,hi,hCN,inf_le_left.trans hQT,
    inf_le_right.trans (centralizer_le (le_conjugateSpanBy D.V D.H)),?_⟩
  constructor
  · intro he
    have hCU : C ≤ D.U := inf_le_left.trans_eq he.symm
    rwa [inf_eq_right.mpr hCU] at hi
  · intro he
    rw [he] at hs
    exact (sup_eq_left.mpr (h.point_le.trans (le_conjugateSpanBy D.V D.H))).symm.trans hs

/-- The closure lies in the literal mapped component core, whose remaining
factor is its closure centralizer. -/
theorem source_normal_bender_component_core_split
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hnH : 1 < generationParameter H)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) H))
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    (f : ℕ) (hm : BenderModel ((H ⊓ M).subgroupOf H) K f) :
    let U := conjugateSpanBy (localModule T M) H
    let QK := (K.pCoreIn 2).map H.subtype
    U ≤ QK ∧ QK ≤ H.pCoreIn 2 ∧
      U ⊔ (QK ⊓ centralizer (U : Set G)) = QK ∧
      U ⊓ (QK ⊓ centralizer (U : Set G)) = centralInvolutions T := by
  let D : ChapterG.Section02.Setup G :=
    { V := localModule T M, V₁ := centralInvolutions T, L := sourceResidual M Mc,
      T := T, H := H }
  let K₁ := K.map H.subtype
  let QK := (K.pCoreIn 2).map H.subtype
  obtain ⟨h,hphi,hphic,_⟩ := source_frattini_seed_orbit
    hG T hempty hM hu hmany hcard e H hH.1 hne
  obtain ⟨hx,hZ,ho⟩ := source_normal_bender_closure_extraspecial
    hG T hempty hM hu hmany hcard e H hH hnH hne K hK hqK hgen f hm
  let : IsExtraspecial 2 D.U := hx
  obtain ⟨_,hUK⟩ := source_normal_bender_closure_commutator
    hG T hempty hM hu hmany hcard e H hH hnH hne K hK hqK hgen f hm
  have hKN : D.H ≤ normalizer (K₁ : Set G) := by
    have hh := K.le_normalizer_map H.subtype
    rwa [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] at hh
  have hQeq : QK = K₁.pCoreIn 2 :=
    map_pCoreIn_of_ker_isPGroup H.subtype
      (IsPGroup.ker_isPGroup_of_injective H.subtype_injective) K
  have hUQ : D.U ≤ QK := by
    rw [hQeq]
    exact le_pCoreIn_of_normalizes h.U_isPGroup hUK
      ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy D.V D.H))
  have hQQ : QK ≤ D.QH := by
    rw [hQeq]
    exact pCoreIn_mono_of_normalizes (map_subtype_le K) hKN
  have hcomm : ⁅QK,D.U⁆ ≤ D.V₁ := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hQQ).trans h.commutator_U_core_le_point
  refine ⟨hUQ,hQQ,extraspecial_sup_centralizer_eq D.U QK D.V₁ hUQ hZ hcomm,?_⟩
  change D.U ⊓ (QK ⊓ centralizer (D.U : Set G)) = D.V₁
  rw [← inf_assoc,inf_eq_left.mpr hUQ,← map_center_subtype_eq_inf_centralizer]
  exact hZ
end CFSG.Quasithin.Chapter14.Section02.LocalBinary
