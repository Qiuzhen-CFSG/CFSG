module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.OddCore
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.MaximalNormalizerPerfect
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.MarkedCentralizers
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.MarkedCentralizers
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortQuotient

/-!
# Full ambient short-root centralizers in the prepared unitary-four rows

For any specified reduced comparison, retain its exact short-root mark.
After odd outer degree, the established return fusion and unique fixed
cosets give N_C_G(t)(U)=C_N_G(L)(t). The whole line U lies in the perfect
residual of C_L(t). Its image centralizes U and contains U, so the
maximal-W odd-core and Bender argument forces C_G(t)≤N_G(L).

Apply this to the very comparison used by the full-normalizer realization.
The literal endpoint map now identifies the full ambient short-root
centralizer with the full centralizer in that same extension, alongside
the already proved long-root centralizer identification. All endpoint
and whole-middle equations are retained.

Source: Aschbacher–Smith F.4.42, printed pp.295–296. The F.4.38 parity
premise remains explicit; outer transfer and F.4.43 order comparison
are further obligations, not conclusions of this module.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour ChapterF.SourceCompletion.UnitaryNonbinary
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The complete maximal-W argument bounds the full ambient centralizer
of the specified short-root mark, after the same extension's odd degree. -/
theorem Preparation.unitary_short_ambient_containment_of_odd_outer
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (r : UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm)
    (hodd : ¬ 2 ∣ (inner (ProjectiveGroup m hm)).relIndex r.extension.carrier)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] ((T : Subgroup G) ⊓ L)) (amalgam m hm).reverse) :
    centralizer ({(ChapterF.UnitarySource.FourShortTransport.sourceShort m hm e).val} : Set G) ≤
      normalizer (L : Set G) := by
  obtain ⟨hmgt,hn,t,ht,htmark,htQ,hcommon,z,hz,hzc,U,hU,hUQ,hUres,hUV,hUc,_,_,_,htU,
      hfix,_,_,hNU,hV,S,hSX,hzS,hScentral⟩ :=
    d.unitary_short_fixed_cosets_sylow_with_actor_at_of_odd_outer h hH hp m hm hc r hodd e
  let M := centralizer ({t.val} : Set G)
  let X := (normalizer (L : Set G)).subgroupOf M
  let Y := centralizer ({t} : Set L)
  let j := UnitarySource.shortCentralizerEmbedding L t
  let U₀ := U.map j
  let t₀ := j ⟨t,mem_centralizer_singleton_iff.mpr rfl⟩
  let P := (solvableResidual Y).map j
  let : Group.IsPerfect P := Group.IsPerfect.map j
  let : IsElementaryAbelian 2 (normalClosure ({z} : Set Y)) := hV
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (inclusion hUV) (inclusion_injective _)
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.map j
  have hUX : U₀ ≤ X := by
    rintro a ⟨b,_,rfl⟩
    exact L.le_normalizer b.val.property
  have htU₀ : t₀ ∈ U₀ := mem_map_of_mem j (htU.le (mem_zpowers _))
  have htcenter : t₀ ∈ center M := by
    apply mem_center_iff.mpr
    intro b
    exact Subtype.ext (mem_centralizer_singleton_iff.mp b.property)
  have hUP : U₀ ≤ P := map_mono hUres
  have hPC : P ≤ centralizer (U₀ : Set M) := by
    rintro a ⟨b,_,rfl⟩ v ⟨u,hu,rfl⟩
    exact (j.map_mul u b).symm.trans
      ((congrArg j (mem_center_iff.mp (hU hu) b).symm).trans (j.map_mul b u))
  have hU₀Q : U₀.map M.subtype ≤ L.pCoreIn 2 := by
    change (U.map j).map M.subtype ≤ L.pCoreIn 2
    rw [map_map]
    change U.map (L.subtype.comp Y.subtype) ≤ L.pCoreIn 2
    simpa only [map_map] using hUQ
  have hON (R : Subgroup M) (hR : R ≤ U₀) : pPrimeCore 2 (normalizer (R : Set M)) = ⊥ :=
    d.unitary_short_normalizer_odd_core_of_odd_outer h hH hp m hm hc r hodd t htQ hcommon R
      ((map_mono hR).trans hU₀Q)
  have htop : X = ⊤ := ChapterF.UnitarySource.eq_top_of_perfect_line X U₀ (zpowers t₀)
    hUX (zpowers_le.mpr htU₀) (zpowers_le.mpr htcenter) hNU
    S hSX (j z) hzS hScentral hfix P hUP hPC hON
  rw [←htmark]
  intro a ha
  exact htop.ge (show (⟨a,ha⟩ : M) ∈ (⊤ : Subgroup M) from mem_top _)

/-- The full ambient short-root centralizer, with the same extension and
literal endpoint map used by the whole-normalizer realization. -/
@[expose] def UnitarySource.FourAmbientShortCentralizerComparison
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
      Nat.card (centralizer ({t.val} : Set G)) =
        Nat.card (centralizer ({inclusion r.extension.right_le (F.left t)} : Set r.extension.carrier)) ∧
      ∃ htN : centralizer ({t.val} : Set G) ≤ normalizer (L : Set G),
      ∃ k : centralizer ({t.val} : Set G) ≃* centralizer
          ({inclusion r.extension.right_le (F.left t)} : Set r.extension.carrier),
        ∀ x, (k x).val = inclusion r.extension.right_le (F.left (inclusion htN x))

/-- Both root centralizers are full ambient centralizers on the same
marked source extension. Only its outer-degree parity remains explicit. -/
theorem Preparation.unitaryFour_ambient_centralizers_of_odd_outer
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (r : UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm)
    (hodd : ¬ 2 ∣ (inner (ProjectiveGroup m hm)).relIndex r.extension.carrier) :
    ∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) (amalgam m hm).reverse,
      ∃ f : UnitaryNativeLift.Four.LiftReverse m hm a,
      ∃ F : RankTwoAmalgam.Iso (normalizerDiagram L (residual H)) r.extension.amalgam.reverse,
        (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
        (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
        (∀ z, (F.middle z).val = (f.action z).val) ∧
        UnitarySource.FourLongCentralizerComparison r F ∧
        UnitarySource.FourAmbientShortCentralizerComparison r a F := by
  obtain ⟨a,f,F,h0,h1,hD,hlong,hshort⟩ :=
    d.unitaryFour_marked_centralizers h hH hp m hm hc r
  refine ⟨a,f,F,h0,h1,hD,hlong,?_⟩
  let t := inclusion r.left_le (inclusion inf_le_left
    (ChapterF.UnitarySource.FourShortTransport.sourceShort m hm a.comparison))
  have htN : centralizer ({t.val} : Set G) ≤ normalizer (L : Set G) :=
    d.unitary_short_ambient_containment_of_odd_outer h hH hp m hm hc r hodd a.comparison
  obtain ⟨ht,hmark,hfull,k,hk,_⟩ := hshort
  let c := (ambientCentralizerEquiv _ t htN).symm.trans k
  exact ⟨ht,hmark,hfull,Nat.card_congr c.toEquiv,htN,c,fun x => hk _⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
