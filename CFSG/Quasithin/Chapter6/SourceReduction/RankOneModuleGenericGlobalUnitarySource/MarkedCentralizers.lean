module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.Centralizers
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFullNormalizer.Four
public import Theory.GroupTheory.TwoInvolutionClassOrder
public import Theory.GroupTheory.CentralizerSmallKernelTransport
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFactors
import all Theory.GroupTheory.CentralizerSmallKernelTransport
import all Theory.GroupTheory.TwoInvolutionClassOrder
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourLongCentralizer
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourShortCentralizer

/-!
# Centralizer comparisons on the same marked unitary-four extension

The original ambient long-root centralizer lies in the right-residual
normalizer. Its image on the specified full extension has its entire
centralizer in the point endpoint, by the native matrix calculation and
factorization through the actual middle. The endpoint marking therefore
identifies these full centralizers by an actual group isomorphism, including
all outer actors of that extension. The other endpoint identifies the local
short-root centralizer with the full extension short-root centralizer.
Both isomorphisms retain their literal endpoint equations, on the same
original carrier with the same whole-overlap action.

Both ordinary and degree-two comparisons and both orientations enter the
prepared input; faithfulness excludes only the impossible native orientation.
Source: Aschbacher–Smith F.4.42–43, printed pp.295–296, and 5.3.3, p.659.
The outer-transfer, short-root fixed-coset and ambient order steps remain open.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour ChapterF.SourceCompletion.UnitaryNonbinary
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem center_image_transport {X : Type*} [Group X]
    {K P : Subgroup G} {R Q : Subgroup X} (hKP : K ≤ P) (e : P ≃* Q)
    (hR : (K.subgroupOf P).map (Q.subtype.comp e.toMonoidHom) = R)
    (z : P) (hz : z.val ∈ (center K).map K.subtype) :
    (e z).val ∈ (center R).map R.subtype := by
  let f := Q.subtype.comp e.toMonoidHom
  obtain ⟨k,hk,hkz⟩ := hz
  have hez : z = ⟨k,hKP k.property⟩ := Subtype.ext hkz.symm
  rw [hez]
  let a : P := ⟨k,hKP k.property⟩
  have haR : f a ∈ R := hR ▸ mem_map_of_mem f k.property
  refine ⟨⟨f a,haR⟩,?_,rfl⟩
  apply mem_center_iff.mpr
  intro r
  obtain ⟨b,hb,he⟩ := (show r.val ∈ (K.subgroupOf P).map f from hR.symm ▸ r.property)
  apply Subtype.ext
  change r.val * f a = f a * r.val
  rw [←he,←map_mul,←map_mul]
  apply congrArg f
  apply Subtype.ext
  exact congrArg K.subtype (mem_center_iff.mp hk ⟨b,hb⟩)

omit [Finite G] in
private def ambientCentralizerEquiv (M : Subgroup G) (z : M)
    (hz : centralizer ({z.val} : Set G) ≤ M) :
    centralizer ({z} : Set M) ≃* centralizer ({z.val} : Set G) :=
  { TwoInvolutionClassOrder.centralizerEquiv M z hz with map_mul' := fun _ _ => rfl }

omit [Finite G] in
private def nestedCentralizerEquiv (M N : Subgroup G) (hMN : M ≤ N) (z : M)
    (hz : centralizer ({inclusion hMN z} : Set N) ≤ M.subgroupOf N) :
    centralizer ({z} : Set M) ≃* centralizer ({inclusion hMN z} : Set N) where
  toFun x := ⟨inclusion hMN x.val,mem_centralizer_singleton_iff.mpr
    (congrArg (inclusion hMN) (mem_centralizer_singleton_iff.mp x.property))⟩
  invFun x := ⟨⟨x.val.val,hz x.property⟩,mem_centralizer_singleton_iff.mpr
    (Subtype.ext (congrArg (fun x : N => x.val) (mem_centralizer_singleton_iff.mp x.property)))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

omit [Finite G] in
/-- The full ambient long-root centralizers, identified by the specified
right endpoint map with their centralizers in the same extension. -/
@[expose] def UnitarySource.FourLongCentralizerComparison
    {L K S : Subgroup G} {m : ℕ} {hm : 1 ≤ m}
    (r : UnitaryFourNormalizerMarking L K S m hm)
    (F : RankTwoAmalgam.Iso (normalizerDiagram L K) r.extension.amalgam.reverse) : Prop :=
    ∀ z : normalizer (K : Set G),
          z.val ∈ (center K).map K.subtype → orderOf z.val = 2 →
          centralizer ({inclusion r.extension.left_le (F.right z)} : Set r.extension.carrier) ≤
            r.extension.left.subgroupOf r.extension.carrier ∧
          Nat.card (centralizer ({z.val} : Set G)) =
            Nat.card (centralizer
              ({inclusion r.extension.left_le (F.right z)} : Set r.extension.carrier)) ∧
          ∃ hzN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G),
          ∃ k : centralizer ({z.val} : Set G) ≃* centralizer
              ({inclusion r.extension.left_le (F.right z)} : Set r.extension.carrier),
            ∀ x, (k x).val = inclusion r.extension.left_le (F.right (inclusion hzN x))

omit [Finite G] in
/-- The marked local short-root centralizer, identified with the full
short-root centralizer of the same extension by the left endpoint map. -/
@[expose] def UnitarySource.FourShortCentralizerComparison
    {L K S : Subgroup G} {m : ℕ} {hm : 1 ≤ m}
    (r : UnitaryFourNormalizerMarking L K S m hm)
    (a : UnitarySource.MarkedMiddleAction L K S (amalgam m hm).reverse)
    (F : RankTwoAmalgam.Iso (normalizerDiagram L K) r.extension.amalgam.reverse) : Prop :=
    let t := inclusion r.left_le (inclusion inf_le_left
      (ChapterF.UnitarySource.FourShortTransport.sourceShort m hm a.comparison))
    orderOf t.val = 2 ∧
      inclusion r.extension.right_le (F.left t) =
        r.extension.baseHom (ChapterF.UnitarySource.FourShortTransport.shortRoot m hm) ∧
      centralizer ({inclusion r.extension.right_le (F.left t)} : Set r.extension.carrier) ≤
        r.extension.right.subgroupOf r.extension.carrier ∧
      ∃ k : centralizer ({t} : Set (normalizer (L : Set G))) ≃* centralizer
          ({inclusion r.extension.right_le (F.left t)} : Set r.extension.carrier),
        (∀ x, (k x).val = inclusion r.extension.right_le (F.left x.val)) ∧
        Nat.card (centralizer ({t} : Set (normalizer (L : Set G)))) =
          Nat.card (centralizer ({inclusion r.extension.right_le (F.left t)} : Set r.extension.carrier))

omit [Finite G] in
private theorem marked_short_centralizer {L K S : Subgroup G} {m : ℕ} {hm : 1 ≤ m}
    (r : UnitaryFourNormalizerMarking L K S m hm)
    (a : UnitarySource.MarkedMiddleAction L K S (amalgam m hm).reverse)
    (F : RankTwoAmalgam.Iso (normalizerDiagram L K) r.extension.amalgam.reverse)
    (h0 : ∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) :
    let t := inclusion r.left_le (inclusion inf_le_left
      (ChapterF.UnitarySource.FourShortTransport.sourceShort m hm a.comparison))
    orderOf t.val = 2 ∧
      inclusion r.extension.right_le (F.left t) =
        r.extension.baseHom (ChapterF.UnitarySource.FourShortTransport.shortRoot m hm) ∧
      centralizer ({inclusion r.extension.right_le (F.left t)} : Set r.extension.carrier) ≤
        r.extension.right.subgroupOf r.extension.carrier ∧
      ∃ k : centralizer ({t} : Set (normalizer (L : Set G))) ≃* centralizer
          ({inclusion r.extension.right_le (F.left t)} : Set r.extension.carrier),
        (∀ x, (k x).val = inclusion r.extension.right_le (F.left x.val)) ∧
        Nat.card (centralizer ({t} : Set (normalizer (L : Set G)))) =
          Nat.card (centralizer ({inclusion r.extension.right_le (F.left t)} : Set r.extension.carrier)) := by
  let u := ChapterF.UnitarySource.FourShortTransport.sourceShort m hm a.comparison
  let t := inclusion r.left_le (inclusion inf_le_left u)
  have ht : orderOf t.val = 2 :=
    ChapterF.UnitarySource.FourShortTransport.sourceShort_order m hm a.comparison
  have hnative : (a.comparison.left (inclusion inf_le_left u)).val =
      ChapterF.UnitarySource.FourShortTransport.shortRoot m hm := by
    have he := congrArg Subtype.val (a.comparison.left_commutes u)
    exact he.trans (congrArg Subtype.val (a.comparison.middle.apply_symm_apply _))
  have hmark : inclusion r.extension.right_le (F.left t) =
      r.extension.baseHom (ChapterF.UnitarySource.FourShortTransport.shortRoot m hm) := by
    apply Subtype.ext
    exact (h0 (inclusion inf_le_left u)).trans (congrArg MulAut.conj hnative)
  have hfull : centralizer ({inclusion r.extension.right_le (F.left t)} : Set r.extension.carrier) ≤
      r.extension.right.subgroupOf r.extension.carrier := by
    rw [hmark]
    exact FourExtension.short_root_centralizer_le m hm r.extension
  let k := (CentralizerSmallKernelTransport.centralizerEquiv F.left t).trans
    (nestedCentralizerEquiv _ _ r.extension.right_le (F.left t) hfull)
  exact ⟨ht,hmark,hfull,k,fun _ => rfl,Nat.card_congr k.toEquiv⟩

variable {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

private theorem marked_long_centralizers
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (r : UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm)
    (a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) (amalgam m hm).reverse)
    (F : RankTwoAmalgam.Iso (normalizerDiagram L (residual H)) r.extension.amalgam.reverse)
    (h1 : ∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) :
    ∀ z : normalizer (residual H : Set G),
          z.val ∈ (center (residual H)).map (residual H).subtype → orderOf z.val = 2 →
          centralizer ({inclusion r.extension.left_le (F.right z)} : Set r.extension.carrier) ≤
            r.extension.left.subgroupOf r.extension.carrier ∧
          Nat.card (centralizer ({z.val} : Set G)) =
            Nat.card (centralizer
              ({inclusion r.extension.left_le (F.right z)} : Set r.extension.carrier)) ∧
          ∃ hzN : centralizer ({z.val} : Set G) ≤ normalizer (residual H : Set G),
          ∃ k : centralizer ({z.val} : Set G) ≃* centralizer
              ({inclusion r.extension.left_le (F.right z)} : Set r.extension.carrier),
            ∀ x, (k x).val = inclusion r.extension.left_le (F.right (inclusion hzN x)) := by
  let : Finite (ProjectiveGroup m hm) :=
    Finite.of_surjective (projection m hm)
      (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag.project_surjective
        (MatrixField m) (standardForm m hm))
  have hmgt : 1 < m :=
    (d.unitary_reduced_native_comparison h hH.1.1.2 hp m hm hc).1
  have hr := d.reduced_parabolic_residuals h hH.1.1.2 hp
    (hc.elim (.unitary m hm) (.unitaryExtension m hm))
  intro z hz hz2
  let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1
  have hKP : residual H ≤ P := le_sup_left.trans le_sup_left
  have hzK : z.val ∈ residual H := (map_subtype_le _) hz
  let zP : P := ⟨z.val,hKP hzK⟩
  have hR : ((residual H).subgroupOf P).map
      ((pointParabolic m hm).subtype.comp a.comparison.right.toMonoidHom) = PointLocal.ProjectiveLocal m hm := by
    have hres : (residual H).subgroupOf P = solvableResidual P := by
      have he : (solvableResidual P).map P.subtype = residual H :=
        hr 1
      rw [←he]
      exact comap_map_eq_self_of_injective P.subtype_injective _
    rw [hres,←map_map,map_solvableResidual_eq a.comparison.right.toMonoidHom
      a.comparison.right.surjective]
    exact PointLocal.pointParabolic_solvableResidual m hm hmgt
  have hzn := center_image_transport hKP a.comparison.right hR zP hz
  have hzne : (a.comparison.right zP).val ≠ 1 := by
    intro hh
    have he : a.comparison.right zP = 1 := Subtype.ext hh
    have hzp : zP = 1 := a.comparison.right.map_eq_one_iff.mp he
    have hez : z.val = 1 := congrArg Subtype.val hzp
    simp [hez] at hz2
  have hmark : (F.right z).val = MulAut.conj (a.comparison.right zP).val := h1 zP
  have hbase : inclusion r.extension.left_le (F.right z) =
      r.extension.baseHom (a.comparison.right zP).val := Subtype.ext hmark
  have hfull : centralizer ({inclusion r.extension.left_le (F.right z)} :
      Set r.extension.carrier) ≤ r.extension.left.subgroupOf r.extension.carrier := by
    rw [hbase]
    exact FourExtension.long_root_centralizer_le m hm hmgt r.extension _ hzn hzne
  have hamb := d.unitary_central_involution_centralizers h hH hp m hm hc 1 z hz hz2
  let k := (ambientCentralizerEquiv _ z hamb).symm.trans
    ((CentralizerSmallKernelTransport.centralizerEquiv F.right z).trans
      (nestedCentralizerEquiv _ _ r.extension.left_le (F.right z) hfull))
  exact ⟨hfull,Nat.card_congr k.toEquiv,hamb,k,fun _ => rfl⟩

/-- On the same constructed extension, the long-root map identifies the
full ambient centralizer, and the short-root map identifies the local
centralizer. Both full-extension centralizers lie in their marked endpoints.
The source row supplies every premise of these comparisons. -/
theorem Preparation.unitaryFour_marked_centralizers
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (r : UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm) :
    (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) (amalgam m hm).reverse,
      ∃ f : UnitaryNativeLift.Four.LiftReverse m hm a,
      ∃ F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H)) r.extension.amalgam.reverse,
        (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
        (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
        (∀ z, (F.middle z).val = (f.action z).val) ∧
        UnitarySource.FourLongCentralizerComparison r F ∧
        UnitarySource.FourShortCentralizerComparison r a F) := by
  let : Finite (ProjectiveGroup m hm) :=
    Finite.of_surjective (projection m hm)
      (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag.project_surjective
        (MatrixField m) (standardForm m hm))
  have hmgt : 1 < m :=
    (d.unitary_reduced_native_comparison h hH.1.1.2 hp m hm hc).1
  have hr := d.reduced_parabolic_residuals h hH.1.1.2 hp
    (hc.elim (.unitary m hm) (.unitaryExtension m hm))
  rcases r.marking with ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle⟩ |
    ⟨a,f,F,h0,h1,hD,hE,hleft,hright,hmiddle⟩
  · exfalso
    obtain ⟨b⟩ := UnitaryFactors.residual_factor_equiv (hr 0)
      (PointLocal.pointParabolic_solvableResidual m hm hmgt) a.comparison.left
    exact faithful_not_core_center_central h.local_mem.2 b
      (UnitaryFactors.point_core_center_central m hm)
  · exact ⟨a,f,F,h0,h1,hD,marked_long_centralizers d h hH hp m hm hc r a F h1,
      marked_short_centralizer r a F h0⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
