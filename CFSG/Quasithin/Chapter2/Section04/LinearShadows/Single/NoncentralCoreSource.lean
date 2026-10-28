module
public import CFSG.Quasithin.ChapterC.Section01.BlockCoreCentralConjugation
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2CoverBounds
public import Theory.GroupTheory.PerfectNormalizedIntersection
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.ComponentRecognition
public import Theory.GroupTheory.IndexTwoConjugateSpan

/-!
# The fixed-pair component in the noncentral single branch

The noncommuting fixed-module pair makes the ambient two-core intersect the
natural block centrally. The fixed Sylow normalizer geometry then makes the
core normalize the block; perfection upgrades the central commutator to
centralization. The actual index-two local block therefore lies in an ordinary
component, and normality identifies its two-conjugate span with that component.

The literal carrier is K = Lₛ ∨ Lₛ^(x⁻¹), inside X = K ∨ Tₛ. The actual
Sylow and local-family inputs remain explicit; no full-Sylow action on Lₛ
is inferred from the index-two actor. The fixed-block source and the ambient
centralizer Sylow argument supply these earlier inputs.

Source: Aschbacher–Smith 2.4.23(3–5), printed pp.537–538.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G]

/-- The source fixed-Sylow geometry makes the actual ambient two-core
centralize the perfect natural block without identifying the core first. -/
theorem core_centralizes_of_fixed_pair
    (L R S T X : Subgroup G) {n : ℕ} (hL : ChapterC.IsL2EvenBlock L n)
    [Group.IsPerfect L] (hLX : L ≤ X) (hTX : T ≤ X)
    (hcore : pCore 2 L = ChapterC.blockU L)
    (hUR : (ChapterC.blockU L).map L.subtype ≤ R) (hRL : R ≤ L)
    (hTR : T ≤ normalizer (R : Set G))
    (hTS : T ⊓ normalizer ((ChapterC.blockU L).map L.subtype : Set G) ≤ S)
    (hSL : S ≤ normalizer (L : Set G))
    (hQT : twoCore X ≤ T) (x : G) (hxT : x ∈ T)
    (hnc : ¬ ((ChapterC.blockU L).map L.subtype).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer ((ChapterC.blockU L).map L.subtype : Set G)) :
    L ≤ centralizer (twoCore X : Set G) := by
  let Q := twoCore X
  let U := (ChapterC.blockU L).map L.subtype
  have hQN : X ≤ normalizer (Q : Set G) := le_normalizer_twoCore X
  have hQI := hL.2.1.inf_le_center_of_noncommuting_conjugate Q R
    (isPGroup_pCoreIn 2 X) (hLX.trans hQN) hcore hUR hRL x
    (hQN (hTX hxT)) (hTR hxT) hnc
  have hZU : (center L).map L.subtype ≤ U :=
    map_mono (hL.center_le_module hcore)
  have hcomm : ⁅Q,U⁆ ≤ Q ⊓ L := by
    apply le_inf
    · exact le_normalizer_iff_commutator_le_left.mp
        ((map_subtype_le _).trans (hLX.trans hQN))
    · exact ((commutator_mono le_rfl hUR).trans
        (le_normalizer_iff_commutator_le_right.mp (hQT.trans hTR))).trans hRL
  have hQU : Q ≤ normalizer (U : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr (hcomm.trans (hQI.trans hZU))
  have hQL : Q ≤ normalizer (L : Set G) := ((le_inf hQT hQU).trans hTS).trans hSL
  apply le_centralizer_iff.mp
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply commutator_eq_bot_of_iterated_eq_bot
  have hc : ⁅Q,L⁆ ≤ (center L).map L.subtype :=
    (le_inf (le_normalizer_iff_commutator_le_left.mp (hLX.trans hQN))
      (le_normalizer_iff_commutator_le_right.mp hQL)).trans hQI
  apply le_bot_iff.mp
  apply (commutator_mono hc le_rfl).trans_eq
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rintro a ⟨b,hb,rfl⟩ l hl
  exact congrArg Subtype.val (mem_center_iff.mp hb ⟨l,hl⟩)

/-- The literal conjugate span in the fixed-centralizer argument is an
ordinary component. The actual Sylow subgroup and index-two local block are
retained, rather than replacing the local actor with a full Sylow actor. -/
theorem fixed_pair_isComponent [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (L R S T : Subgroup G) {n : ℕ} (hL : ChapterC.IsL2EvenBlock L n)
    (hST : S ≤ T) (hi : S.relIndex T = 2)
    (hcore : pCore 2 L = ChapterC.blockU L)
    (hUR : (ChapterC.blockU L).map L.subtype ≤ R) (hRL : R ≤ L)
    (hTR : T ≤ normalizer (R : Set G))
    (hTS : T ⊓ normalizer ((ChapterC.blockU L).map L.subtype : Set G) ≤ S)
    (hSL : S ≤ normalizer (L : Set G)) (x : G) (hxT : x ∈ T) (hxS : x ∉ S)
    (hnc : ¬ ((ChapterC.blockU L).map L.subtype).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer ((ChapterC.blockU L).map L.subtype : Set G)) :
    let K := L ⊔ L.map (MulAut.conj x⁻¹).toMonoidHom
    let X := K ⊔ T
    twoCore X ≠ ⊥ →
      (∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype = T) →
      L.subgroupOf X ∈ Chapter1.L X (S.subgroupOf X) →
      IsComponent X (K.subgroupOf X) := by
  dsimp only
  let K := L ⊔ L.map (MulAut.conj x⁻¹).toMonoidHom
  let X := K ⊔ T
  change twoCore X ≠ ⊥ → _
  intro hQne hSylow hlocal
  obtain ⟨P,hP⟩ := hSylow
  have hKX : K ≤ X := le_sup_left
  have hLX : L ≤ X := le_sup_left.trans hKX
  have hTX : T ≤ X := le_sup_right
  let e := subgroupOfEquivOfLe hLX
  let := Chapter1.mem_L_isPerfect hlocal
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hQT : twoCore X ≤ T := by
    rw [←hP]
    exact pCoreIn_le_sylow X P
  have hcentral := core_centralizes_of_fixed_pair L R S T X hL hLX hTX
    hcore hUR hRL hTR hTS hSL hQT x hxT hnc
  let : (K.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le K.le_normalizer (index_two_normalizes_pair S T L hST hi x hxT hxS hSL))
  have hPin : (P : Subgroup X) = T.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hTX]
  have hSP : S.subgroupOf X ≤ P := by
    rw [hPin]
    exact subgroupOf_mono X hST
  have hindex : (S.subgroupOf X).relIndex (P : Subgroup X) ≤ 2 := by
    rw [hPin,relIndex_subgroupOf hTX,hi]
  have hc : L.subgroupOf X ≤ centralizer (pCore 2 X : Set X) := by
    intro l hl u hu
    apply Subtype.ext
    exact hcentral hl u (mem_map_of_mem X.subtype hu)
  let xX : X := ⟨x⁻¹,X.inv_mem (hTX hxT)⟩
  have hgen : K.subgroupOf X = L.subgroupOf X ⊔
      (L.subgroupOf X).map (MulAut.conj xX).toMonoidHom := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hKX,Subgroup.map_sup,
      map_subgroupOf_eq_of_le hLX,map_map]
    have he : X.subtype.comp (MulAut.conj xX).toMonoidHom =
        (MulAut.conj x⁻¹).toMonoidHom.comp X.subtype := rfl
    rw [he,←map_map,map_subgroupOf_eq_of_le hLX]
  exact Double.normal_pair_isComponent_of_index_two
    (Chapter1.Section02.uniqueness_local_quotient_sqtk hG (by change twoCore X ≠ ⊥; exact hQne))
    P (S.subgroupOf X) (L.subgroupOf X) (K.subgroupOf X) xX hSP hindex hlocal
    (hL.of_mulEquiv e.symm) hc hgen
end CFSG.Quasithin.Chapter2.LinearShadows.Single
