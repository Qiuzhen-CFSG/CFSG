module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.JankoFour.NormalFourPlacement
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.LocalConfiguration
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.FourGroupIrreducible
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.NormalFour
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CharacteristicTwo
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The original J₄ exclusion in the rank-one source argument

Every automorphism of the actual J₄ model is inner, so the source's faithful
normal component is its whole action quotient. Align the original Sylow and
normal four-group with the concrete Sylow. The full commutator action proves
irreducibility under the four-group normalizer, and the concrete catalogue
places that normalizer in max1 or a specified conjugate of max4.

Both overgroups have characteristic two. Source maximality identifies the
local group with that overgroup, contradicting its normal-four obstruction.
The final application retains the original quotient L/O₂(L), the source
planes, and every earlier reduction input. No maximal-Sylow cover is assumed.

Source: Aschbacher--Smith, 15.3.43, printed p.1140, and 1.1.5(3)(f), p.502.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
variable {G : Type*} [Group G] [Finite G]

namespace JankoFourSource
omit [Finite G] in
private theorem component_eq_top_of_inner {K S M Y V : Subgroup G}
    (c : LocalConfiguration K S M Y V) (e : K ≃* Janko4.Model)
    (hi : Function.Surjective (MulAut.conj : Janko4.Model →* MulAut Janko4.Model)) :
    K = ⊤ := by
  let : K.Normal := c.normal
  apply top_unique
  intro x _
  obtain ⟨k, hk⟩ := hi (MulAut.congr e (MulAut.conjNormal x))
  obtain ⟨k, hk⟩ := (MulAut.congr_inner_iff e (MulAut.conjNormal x)).mp ⟨k, hk.symm⟩
  have hx : x = (k : G) :=
    MulAut.conjNormal_injective_of_centralizer_eq_bot K c.faithful
      (hk.trans MulAut.conjNormal_val.symm)
  exact hx ▸ k.property

omit [Finite G] in
private theorem four_contradiction {K S M Y V : Subgroup G}
    (c : LocalConfiguration K S M Y V) {H : Type*} [Group H]
    (e : M ≃* H)
    (hf : ∀ W : Subgroup H, W.Normal → IsElementaryAbelian 2 W → Nat.card W ≠ 4) :
    False := by
  let : IsElementaryAbelian 2 V := c.plane_elementary
  let : IsElementaryAbelian 2 (V.subgroupOf M) :=
    IsElementaryAbelian.subgroupOf c.plane_le_local
  have hn : ((V.subgroupOf M).map e.toMonoidHom).Normal :=
    c.plane_normal.map e.toMonoidHom e.surjective
  apply hf _ hn (IsElementaryAbelian.map e.toMonoidHom)
  rw [Subgroup.card_map_of_injective e.injective]
  exact (Nat.card_congr (subgroupOfEquivOfLe c.plane_le_local).toEquiv).trans c.plane_card

private theorem local_equiv_of_cover {K S M Y V : Subgroup G}
    (c : LocalConfiguration K S M Y V) (e : G ≃* Janko4.Model)
    {H : Type*} [Group H] {Q : Subgroup Janko4.Model}
    (hMQ : M.map e.toMonoidHom ≤ Q) (f : Q ≃* H)
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H) :
    Nonempty (M ≃* H) := by
  let R := Q.map e.symm.toMonoidHom
  have hR : R.map e.toMonoidHom = Q := by
    simp [R, map_map]
  let eR : R ≃* H := (e.subgroupMap R).trans ((MulEquiv.subgroupCongr hR).trans f)
  have hMR : M ≤ R := by
    simpa [R, map_map] using map_mono (f := e.symm.toMonoidHom) hMQ
  have hchar : Theory.GroupTheory.generalizedFitting R = pCore 2 R :=
    Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2
      ((Theory.Quasithin.centralizer_pCore_le_iff 2 eR).mpr hc)
  have he : M = R := le_antisymm hMR (c.maximal.2 hchar hMR)
  exact ⟨(MulEquiv.subgroupCongr he).trans eR⟩


open Janko4.LocalStructure.SymmetricLinear
open Janko4.OuterReduction.OddIndex
open Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
open MatrixNormalizerBounds
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  Janko4.Cardinality.max1Subgroup max4Subgroup

private noncomputable def markedSylow : Sylow 2 Janko4.Model :=
  twoSubgroup_isPGroup.toSylow (by
    rw [twoSubgroup, index_map_subtype, localTwoSubgroup_index]
    exact Nat.Prime.not_dvd_mul Nat.prime_two (by decide)
      Janko4.OuterReduction.max1_odd_index_unconditional)

theorem not_janko_four_of_irreducible {K S M Y V : Subgroup G}
    (c : LocalConfiguration K S M Y V) (e : K ≃* Janko4.Model)
    (hi : ∀ B : Subgroup G, B ≤ V →
      normalizer (V : Set G) ≤ normalizer (B : Set G) → B = ⊥ ∨ B = V) : False := by
  have hK := component_eq_top_of_inner c e Janko4.AdequateLocal.conj_surjective
  let e₀ : G ≃* Janko4.Model :=
    Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hK.symm).trans e)
  obtain ⟨P, hP⟩ := c.sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Janko4.Model
    (P.mapSurjective (f := e₀.toMonoidHom) e₀.surjective) markedSylow
  let eG : G ≃* Janko4.Model := e₀.trans (MulAut.conj g)
  have hS : S.map eG.toMonoidHom = twoSubgroup := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((P : Subgroup G).map e₀.toMonoidHom).map
      (MulAut.conj g).toMonoidHom = twoSubgroup at hh
    have he : eG.toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp e₀.toMonoidHom := by
      ext x
      rfl
    rw [he]
    simpa only [map_map, hP] using hh
  let A := V.map eG.toMonoidHom
  have hMN : M ≤ normalizer (V : Set G) :=
    (normal_subgroupOf_iff_le_normalizer c.plane_le_local).mp c.plane_normal
  have hMNA : M.map eG.toMonoidHom ≤ normalizer (A : Set Janko4.Model) := by
    rw [← map_equiv_normalizer_eq]
    exact map_mono hMN
  have hAS : A ≤ twoSubgroup := hS ▸ map_mono c.plane_le_sylow
  have hSN : twoSubgroup ≤ normalizer (A : Set Janko4.Model) := by
    rw [← hS]
    exact (map_mono c.sylow_le_local).trans hMNA
  have hAi : ClosureNormalizerIrreducible A := by
    intro B hBA hBN
    have hBV : B.map eG.symm.toMonoidHom ≤ V := by
      simpa [A, map_map] using map_mono (f := eG.symm.toMonoidHom) hBA
    have hNB : normalizer (V : Set G) ≤
        normalizer (B.map eG.symm.toMonoidHom : Set G) := by
      have hh := map_mono (f := eG.symm.toMonoidHom) hBN
      rw [map_equiv_normalizer_eq, map_equiv_normalizer_eq] at hh
      simpa [A, map_map] using hh
    rcases hi _ hBV hNB with h | h
    · left
      have hh := congrArg (Subgroup.map eG.toMonoidHom) h
      simpa [map_map] using hh
    · right
      have hh := congrArg (Subgroup.map eG.toMonoidHom) h
      simpa [A, map_map] using hh
  let : IsElementaryAbelian 2 V := c.plane_elementary
  have hAe : IsElementaryAbelian 2 A := IsElementaryAbelian.map eG.toMonoidHom
  have hAc : Nat.card A = 4 := (card_map_of_injective eG.injective).trans c.plane_card
  rcases JankoFour.normal_four_normalizer_placement A hAS hSN hAe hAi hAc with h | h
  · obtain ⟨f⟩ := local_equiv_of_cover c eG (hMNA.trans h) (MulEquiv.refl _)
      Janko4.LocalStructure.max1_twoCore_centralizer_le
    apply four_contradiction c f
    intro W hn _
    let : W.Normal := hn
    exact Janko4.LocalStructure.max1_normal_card_ne_four W
  · let a := MulAut.conj ThirdConjugacy.conjugator
    obtain ⟨f⟩ := local_equiv_of_cover c eG (hMNA.trans h)
      (a.subgroupMap max4Subgroup).symm max4_twoCore_centralizer_le
    exact four_contradiction c f max4_no_normal_elementary_four

end JankoFourSource

/-- The actual J₄ component image is incompatible with the original source
configuration; its normal four-group supplies the required irreducibility. -/
theorem reduced_not_janko_four {Y S M I L V₁ V₂ : Subgroup G}
    (c : ReducedConfiguration Y S M I L V₁ V₂)
    (e : c.toComponentAction.image L ≃* Janko4.Model) : False :=
  JankoFourSource.not_janko_four_of_irreducible (localConfiguration_of_reduced c) e
    c.image_plane_normalizer_irreducible

/-- Application through the literal source reduction, retaining the component's
possible central two-cover. -/
theorem source_not_symmetricThreeShadow_of_janko_four
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    (hI : I ∈ d.HplusMinimal) (h : ReductionSourceInputs d I L)
    (halt : Candidates.Alternatives15343 d.Yplus I L (localSpan L d.S))
    (e : (L ⧸ pCore 2 L) ≃* Janko4.Model) :
    ¬ SymmetricThreeShadow d.Yplus d.S := by
  intro hshadow
  let c := reducedConfiguration_of_source d hI h hshadow halt
  exact reduced_not_janko_four c ((reducedTwoCoreQuotientEquiv c).symm.trans e)

end CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
