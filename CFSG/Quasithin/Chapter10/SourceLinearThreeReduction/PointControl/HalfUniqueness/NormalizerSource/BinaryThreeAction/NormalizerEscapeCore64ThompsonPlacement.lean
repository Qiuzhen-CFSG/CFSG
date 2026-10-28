module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeDoubledReplacement
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeCore64Join
public import Stellmacher.BaumannNormalizer
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# The two complete cores inside the original Thompson subgroup

Exact maximum-elementary replacement puts the first full MS core in J(T1).
The original exchanger normalizes T1, so the exchanged full core lies there
as well. Their join is the literal orbit movement of O2(L0T). Consequently
the omega-center of J(T1) centralizes this entire join and lies in the original
action kernel O2(L0T). No normalization of either full core by N_G(T1) is used.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02 ChapterC.BinaryMS
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

omit [Finite G] in
private theorem relative_commutator_sup (R A B : Subgroup G)
    (ha : A ≤ normalizer (R : Set G)) (hb : B ≤ normalizer (R : Set G)) :
    ⁅R,A ⊔ B⁆ = ⁅R,A⁆ ⊔ ⁅R,B⁆ := by
  let W := ⁅R,A⁆ ⊔ ⁅R,B⁆
  have hWR : W ≤ R := sup_le (le_normalizer_iff_commutator_le_left.mp ha)
    (le_normalizer_iff_commutator_le_left.mp hb)
  have haW : A ≤ normalizer (W : Set G) := le_normalizer_iff_commutator_le_right.mpr
    ((commutator_mono le_rfl hWR).trans (by rw [commutator_comm]; exact le_sup_left))
  have hbW : B ≤ normalizer (W : Set G) := le_normalizer_iff_commutator_le_right.mpr
    ((commutator_mono le_rfl hWR).trans (by rw [commutator_comm]; exact le_sup_right))
  apply le_antisymm ?_ (sup_le (commutator_mono le_rfl le_sup_left)
    (commutator_mono le_rfl le_sup_right))
  rw [commutator_comm]
  exact commutator_sup_le_of_relative_normal (A ⊔ B) A B R W (sup_le haW hbW)
    le_sup_left le_sup_right (by rw [commutator_comm]; exact le_sup_left)
    (by rw [commutator_comm]; exact le_sup_right)

/-- The actual rank-twelve orbit movement lies in J(T1), whose omega-center
lies in the original join core. -/
theorem normalizerEscape_fullCore64_thompson_placement
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (s : NaturalData D)
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal)
    (hc : IsMulCommutative (commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))))
    (hcard : Nat.card ((commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))).map
        (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))).subtype) = 64) :
    let U := ⁅(localJoin T L).pCoreIn 2,localOrbit T L⁆
    let T₁ := (T : Subgroup G) ⊓ normalizer (L : Set G)
    U ≤ elementaryAbelianMaxJ T₁ ∧
      omegaOneCenterAmbient (elementaryAbelianMaxJ T₁) ≤ (localJoin T L).pCoreIn 2 := by
  let T₁ := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let J := L ⊔ T₁
  let A := L.subgroupOf J
  let R := T₁.subgroupOf J
  let h := normalizerEscapeBinaryInput D (selected_nonnormal s) hout s.quotient
  have hCcard : Nat.card (commutatorCore A) = 64 := by
    change Nat.card ((commutatorCore A).map J.subtype) = 64 at hcard
    simpa only [card_map_of_injective J.subtype_injective] using hcard
  obtain ⟨m,hm,⟨q⟩⟩ :=
    AbelianCore.QuotientRecognition.Input.exists_abelianCore_naturalQuotient (h := h) hc
  have hm2 : m = 2 := by
    rcases hm with hm | hm
    · have hb := (h.abelianCore_fixedKernel_bounds hc (Or.inl hm) q).1
      have he := q.card
      rw [hm] at he
      change Nat.card (commutatorCore A) = 2^(3*1) * Nat.card (coreFixed A) at he
      rw [hCcard] at he
      change Nat.card (coreFixed A) ≤ 2 at hb
      norm_num at he
      omega
    · exact hm
  subst m
  have hz : coreFixed A = ⊥ :=
    (eq_bot_iff_card _).mpr (h.abelianCore_fixedKernel_eq_one_of_twoCopies hc q)
  have hi : Function.Injective q.projection :=
    (MonoidHom.ker_eq_bot_iff q.projection).mp (q.kernel.trans hz)
  obtain ⟨P,hP⟩ := halfSylow_sylow_component_join D (selected_nonnormal s)
  have hPR : (P : Subgroup J) = R := by
    apply map_injective J.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le le_sup_right]
  obtain ⟨d⟩ := h.exists_doubledCoreAction hc q hi P hPR.symm.le
  let B := elementaryAbelianMaxJ T₁
  let R₀ := (localJoin T L).pCoreIn 2
  let C := ⁅R₀,L⁆
  let a := (MulAut.conj s.exchange).toMonoidHom
  let Ct := C.map a
  have hR : R.map J.subtype = T₁ := map_subgroupOf_eq_of_le le_sup_right
  have hC : C = (commutatorCore A).map J.subtype :=
    normalizerEscape_join_core_component D (selected_nonnormal s) hout s.quotient
  have hCB : C ≤ B := by
    rw [hC]
    have hh := map_mono (f := J.subtype) (d.core_le_thompson hc hPR.symm.le)
    rw [←elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,hR] at hh
    exact hh
  have hTB : (T : Subgroup G) ≤ normalizer (B : Set G) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    change B.map (MulAut.conj t).toMonoidHom = B
    dsimp only [B]
    rw [← elementaryAbelianMaxJ_map_injective (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective]
    have htN : t ∈ normalizer (T₁ : Set G) :=
      Parabolics.stabilizer_normalized D (selected_nonnormal s) ht
    exact congrArg elementaryAbelianMaxJ (mem_normalizer_iff_map_conj_eq.mp htN)
  have hCtB : Ct ≤ B :=
    (map_mono hCB).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hTB s.exchange_mem))
  have hJR : localJoin T L ≤ normalizer (R₀ : Set G) :=
    (localJoin T L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have htR : R₀.map a = R₀ := mem_normalizer_iff_map_conj_eq.mp
    (hJR (mem_sup_right s.exchange_mem))
  have hCt : Ct = ⁅R₀,L.map a⁆ := by
    change (⁅R₀,L⁆).map a = _
    rw [map_commutator,htR]
  have hLtJ : L.map a ≤ localJoin T L :=
    ((orbit_eq_pair s).symm ▸ le_sup_right).trans le_sup_left
  have hgen : ⁅R₀,localOrbit T L⁆ = C ⊔ Ct := by
    rw [orbit_eq_pair s,relative_commutator_sup R₀ L _
      (((le_componentOrbit L T).trans le_sup_left).trans hJR) (hLtJ.trans hJR),←hCt]
  have hUB : ⁅R₀,localOrbit T L⁆ ≤ B := hgen ▸ sup_le hCB hCtB
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hVU : D.fullModule ≤ ⁅R₀,localOrbit T L⁆ := by
    conv_lhs => rw [D.fullModule_eq_commutator hu]
    exact commutator_mono (s.full_eq_local.symm ▸ D.module_le_core) le_rfl
  refine ⟨hUB,?_⟩
  intro z hz
  obtain ⟨hzB,_,hzC⟩ := (mem_omegaOneCenterAmbient_iff B z).mp hz
  have hzT : z ∈ (T : Subgroup G) :=
    (show T₁ ≤ (T : Subgroup G) from inf_le_left)
      ((sSup_le fun _ hA => hA.1 : B ≤ T₁) hzB)
  have hzV : z ∈ centralizer (D.moduleSubgroup : Set G) := by
    rw [←s.full_eq_local]
    intro v hv
    exact hzC v (hUB (hVU hv))
  exact (D.sylow_centralizer_module hu).le ⟨hzT,hzV⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
