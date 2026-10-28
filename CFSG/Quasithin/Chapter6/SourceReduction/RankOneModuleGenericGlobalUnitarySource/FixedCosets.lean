module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.InnerReturn
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortAction
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortPerfect
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortCommon
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ResidualReturn
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.MarkedQuotient
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortAction
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortSylow

/-!
# The first unitary fixed-coset argument after outer transfer

Odd outer degree on the specified full-normalizer extension puts all
involution returns through N_G(L) in L. Residual-return fusion and the common
centralizer bound therefore give an actual unique fixed coset of the marked
long root in C_G(t)/C_N_G(L)(t). The prescribed residual Sylow becomes an
ambient Sylow centralizing that same root, so the local stabilizer controls
all two-element fusion in C_G(t).

Keep the entire q-element fixed line U. Restriction and quotient transport
of the unique fixed coset give the precise I.8.5 hypotheses on its q²-element
quotient module. The already-constructed perfect actor rules out a proper
local stabilizer there, giving N_C_G(t)(U)=C_N_G(L)(t).

The parity premise is precisely F.4.38 on the same marked extension. Its
outer-transfer proof and the subsequent maximal-W part of F.4.42 remain
required for unconditional ambient short-centralizer containment.
Source: Aschbacher–Smith F.4.38,42, printed pp.294–296.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour ChapterF.SourceCompletion.UnitaryNonbinary
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

private theorem short_unique_of_two_subgroups
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (hall : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ normalizer (L : Set G) → S ≤ L)
    (t : L) (htQ : t.val ∈ L.pCoreIn 2)
    (z : centralizer ({t} : Set L)) (hz : orderOf z.val.val = 2)
    (hzc : z.val.val ∈ (center (residual H)).map (residual H).subtype)
    (hC : centralizer ({t.val} : Set G) ⊓ centralizer ({z.val.val} : Set G) ≤ normalizer (L : Set G)) :
    ∃! q : centralizer ({t.val} : Set G) ⧸
        (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)),
      UnitarySource.shortCentralizerEmbedding L t z • q = q := by
  have hzQ : z.val.val ∈ L.pCoreIn 2 := mem_map_of_mem L.subtype
    (d.unitary_long_residual_return h hH hp m hm hc z.val.val hzc hz z.val (IsConj.refl _))
  apply UniqueFixedCoset.unique_of_transporter
    (M := (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)))
    (x := UnitarySource.shortCentralizerEmbedding L t z) (L.le_normalizer z.val.property)
  intro g hg
  have hx : IsConj z.val.val (g.val*z.val.val*g.val⁻¹) := isConj_iff.mpr ⟨g.val,rfl⟩
  have hzsq : z.val.val ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z.val.val
  have hx2 : (g.val*z.val.val*g.val⁻¹)^2 = 1 := isConj_one_right.mp (hzsq ▸ hx.pow 2)
  have hxL := hall (zpowers (g.val*z.val.val*g.val⁻¹))
    (IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hx2))
    (zpowers_le.mpr hg) (mem_zpowers _)
  exact short_core_return_transporter d h hH hp m hm hc t.val z.val.val htQ hzQ hC g.val
    (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp g.property))
    (mem_map_of_mem L.subtype
      (d.unitary_long_residual_return h hH hp m hm hc z.val.val hzc hz ⟨_,hxL⟩ hx))

open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot

/-- F.4.38's odd outer degree supplies actual unique fixed cosets and the
first F.4.42 line-normalizer conclusion, on one marked full-line quotient.
No fusion or unique-fixed-coset premise remains. -/
theorem Preparation.unitary_short_fixed_cosets_sylow_with_actor_at_of_odd_outer
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (r : UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm)
    (hodd : ¬ 2 ∣ (inner (ProjectiveGroup m hm)).relIndex r.extension.carrier)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] ((T : Subgroup G) ⊓ L)) (amalgam m hm).reverse) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
      t.val = (ChapterF.UnitarySource.FourShortTransport.sourceShort m hm e).val ∧
      t.val ∈ L.pCoreIn 2 ∧
      (∀ z ∈ (center (residual H)).map (residual H).subtype, orderOf z = 2 →
        centralizer ({t.val} : Set G) ⊓ centralizer ({z} : Set G) ≤ normalizer (L : Set G)) ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
      z.val.val ∈ (center (residual H)).map (residual H).subtype ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ hU : U ≤ center (centralizer ({t} : Set L)),
      (U.map (centralizer ({t} : Set L)).subtype).map L.subtype ≤ L.pCoreIn 2 ∧
      U ≤ solvableResidual (centralizer ({t} : Set L)) ∧
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      let f := UnitarySource.shortLineQuotientMap L t U hU
      let X := UnitarySource.shortLineLocalQuotient L t U
      U ≤ V ∧ Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      (∃! q : centralizer ({t.val} : Set G) ⧸
          (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)),
        UnitarySource.shortCentralizerEmbedding L t z • q = q) ∧
      (∀ x y : centralizer ({t.val} : Set G),
        x.val ∈ normalizer (L : Set G) → y.val ∈ normalizer (L : Set G) →
        IsPGroup 2 (zpowers x) → IsConj x y →
        ∃ a : centralizer ({t.val} : Set G), a.val ∈ normalizer (L : Set G) ∧ a*x*a⁻¹ = y) ∧
      (∀ v ∈ V.map f, v ≠ 1 → ∃! q :
          (UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U) ⧸ X,
        v • q = q) ∧
      UnitarySource.shortLineNormalizer L t U =
        (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)) ∧
      IsElementaryAbelian 2 V ∧
      ∃ P : Sylow 2 (centralizer ({t.val} : Set G)),
        (P : Subgroup _) ≤
          (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)) ∧
        UnitarySource.shortCentralizerEmbedding L t z ∈ (P : Subgroup _) ∧
        ∀ b ∈ (P : Subgroup _), Commute (UnitarySource.shortCentralizerEmbedding L t z) b := by
  have hall := (d.unitaryFour_two_subgroups_of_odd_outer h hH hp m hm hc r hodd).1
  obtain ⟨hmgt,hn,_⟩ := d.unitary_reduced_native_comparison h hH.1.1.2 hp m hm hc
  obtain ⟨_,_,_,hcommon⟩ := d.unitary_short_common_centralizers_at h hH hp m hm hc e
  have hr := d.reduced_parabolic_residuals h hH.1.1.2 hp
    (hc.elim (.unitary m hm) (.unitaryExtension m hm))
  obtain ⟨a,hat,haz⟩ := ChapterF.UnitarySource.FourShortMarked.marked_plane_equiv
    (ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L))
    L (residual H) hr m hm hmgt e
  let t := a (shortLocal (MatrixField m) (fieldConj m) (fieldConj_involutive m hm))
  obtain ⟨ht,z,hzmark,hz,U,hV,hVQ,hVc,hUc,hindex,hUV,hU,htU,horbit,hVintrinsic,hperfect,
      hclass,hSylow,hlift,hline⟩ :=
    short_quotient_from_marked_equiv m hm hmgt a
  let c := (a.subgroupMap (shortCentralizer (MatrixField m) (fieldConj m)
    (fieldConj_involutive m hm))).trans
      (MulEquiv.subgroupCongr (CentralizerSmallKernelTransport.map_centralizer a
        (shortLocal (MatrixField m) (fieldConj m) (fieldConj_involutive m hm))))
  have hzres : z ∈ solvableResidual (centralizer ({t} : Set L)) := by
    have hq : 3 < Nat.card (FixedBy.subfield (MatrixField m) (fieldConj m)) := by
      rw [PointLocal.fixedField_card m hm]
      have hfour : 2^2 ≤ 2^m := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hmgt
      omega
    have he : c (SourceNormalizer.FourShortRoot.longMark
        (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)) = z := by
      apply Subtype.ext
      exact hzmark.symm
    rw [←he]
    exact map_solvableResidual_le c.toMonoidHom (mem_map_of_mem c.toMonoidHom
      (SourceNormalizer.FourShortRoot.longMark_mem_solvableResidual
        (MatrixField m) (fieldConj m) (fieldConj_involutive m hm) hq))
  have hUres : U ≤ solvableResidual (centralizer ({t} : Set L)) :=
    hUV.trans (normalClosure_le_normal (by rintro x rfl; exact hzres))
  have hzc : z.val.val ∈ (center (residual H)).map (residual H).subtype := by
    rw [hzmark]
    exact haz
  have hC : centralizer ({t.val} : Set G) ⊓ centralizer ({z.val.val} : Set G) ≤ normalizer (L : Set G) := by
    rw [show t.val = (ChapterF.UnitarySource.FourShortTransport.sourceShort m hm e).val from hat]
    exact hcommon z.val.val hzc hz
  have htQ : t.val ∈ L.pCoreIn 2 := hVQ
    (mem_map_of_mem L.subtype (mem_map_of_mem (centralizer ({t} : Set L)).subtype
      (hUV (htU.le (mem_zpowers _)))))
  have hfix := short_unique_of_two_subgroups d h hH hp m hm hc hall t htQ z hz hzc hC
  let M := centralizer ({t.val} : Set G)
  let Y := centralizer ({t} : Set L)
  let j₀ := UnitarySource.shortCentralizerEmbedding L t
  obtain ⟨R₀,hRz⟩ := hSylow
  obtain ⟨P₀,hPR,hQP,hPL⟩ := d.unitary_short_centralizer_sylow_extension h hH hp m hm hc t htQ R₀
  have hP₀X : (P₀ : Subgroup M) ≤ (normalizer (L : Set G)).subgroupOf M := by
    intro b hb
    exact hPL (mem_map_of_mem M.subtype hb)
  have hzQ : z.val.val ∈ L.pCoreIn 2 := hVQ
    (mem_map_of_mem L.subtype (mem_map_of_mem Y.subtype
      (subset_normalClosure (Set.mem_singleton _))))
  have hzP : j₀ z ∈ (P₀ : Subgroup M) := by
    obtain ⟨b,hb,he⟩ := hQP hzQ
    exact (show b = j₀ z from Subtype.ext he) ▸ hb
  have hPcentral : ∀ b ∈ (P₀ : Subgroup M), Commute (j₀ z) b := by
    intro b hb
    have hbL := hall ((P₀ : Subgroup M).map M.subtype) (P₀.isPGroup'.map M.subtype)
      hPL (mem_map_of_mem M.subtype hb)
    let c : Y := ⟨⟨b.val,hbL⟩,mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp b.property))⟩
    have hcP : c ∈ (P₀ : Subgroup M).comap j₀ := hb
    have hcR : c ∈ (R₀ : Subgroup Y) := hPR ▸ hcP
    exact Subtype.ext (congrArg (fun u : Y => u.val.val)
      (mem_centralizer_singleton_iff.mp (hRz hcR))).symm
  have hfusion : ∀ x y : M,
      x.val ∈ normalizer (L : Set G) → y.val ∈ normalizer (L : Set G) →
      IsPGroup 2 (zpowers x) → IsConj x y →
      ∃ a : M, a.val ∈ normalizer (L : Set G) ∧ a*x*a⁻¹ = y := by
    intro x y hx hy hxp hxy
    exact UniqueFixedCoset.p_element_fusion P₀ hP₀X hzP hPcentral hfix hx hy hxp hxy
  let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
  let f := UnitarySource.shortLineQuotientMap L t U hU
  let X := UnitarySource.shortLineLocalQuotient L t U
  have hker : f.ker = U := UnitarySource.shortLineQuotientMap_ker L t U hU
  let : IsElementaryAbelian 2 V := hV
  let : IsElementaryAbelian 2 (V.map f) := IsElementaryAbelian.map f
  have hcard : Nat.card (V.map f) = (2^m)^2 := by rw [←relIndex_ker,hker]; exact hindex
  have hVX : V.map f ≤ X := by
    rintro _ ⟨w,hw,rfl⟩
    exact UnitarySource.shortLineQuotientMap_mem_local L t U hU w
  let : ((V.map f).subgroupOf X).Normal :=
    UnitarySource.quotient_module_normal L t U hU V hVintrinsic
  obtain ⟨P,hP,hPr,horbitP⟩ := hperfect f hker.ge
  have hPX : P ≤ X := by
    intro v hv
    obtain ⟨w,rfl⟩ := hPr hv
    exact UnitarySource.shortLineQuotientMap_mem_local L t U hU w
  let R := UnitarySource.shortLineNormalizer L t U
  let j := UnitarySource.shortLineNormalizerMap L t U hU
  let X₀ := UnitarySource.shortLineLocal L t U
  have hzX₀ : j z ∈ X₀ := L.le_normalizer z.val.property
  have hfixR : ∃! q : R ⧸ X₀, j z • q = q := by
    apply UniqueFixedCoset.unique_of_transporter hzX₀
    intro g hg
    exact UniqueFixedCoset.transporter_mem
      (M := (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)))
      (L.le_normalizer z.val.property) hfix (g := g.val) hg
  have hfixQ : ∃! q : (R ⧸ UnitarySource.shortLineKernel L t U) ⧸ X, f z • q = q :=
    UniqueFixedCoset.unique_map_of_surjective
      (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U))
      (QuotientGroup.mk'_surjective _) (by
        rw [QuotientGroup.ker_mk']
        exact UnitarySource.shortLineKernel_le_local L t U) hzX₀ hfixR
  have hfixV : ∀ v ∈ V.map f, v ≠ 1 →
      ∃! q : (R ⧸ UnitarySource.shortLineKernel L t U) ⧸ X, v • q = q := by
    intro v hv hv1
    obtain ⟨b,_,hb⟩ := horbitP v hv hv1
    exact UniqueFixedCoset.unique_of_isConj hfixQ (isConj_iff.mpr ⟨b,hb⟩)
  let : Group.IsPerfect P := hP
  have hbig : 2 < Nat.card (V.map f) := by
    rw [hcard]
    have hq : 2 < 2^m := Nat.pow_lt_pow_right (by decide : 1 < 2) hmgt
    nlinarith
  have htop := ChapterF.UnitarySource.eq_top_of_perfect_orbit
    (V.map f) X P hVX hPX hbig (f z)
    (mem_map_of_mem f (subset_normalClosure (Set.mem_singleton _))) horbitP hfixQ
  have hcommon' : ∀ v ∈ (center (residual H)).map (residual H).subtype, orderOf v = 2 →
      centralizer ({t.val} : Set G) ⊓ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
    rw [show t.val = (ChapterF.UnitarySource.FourShortTransport.sourceShort m hm e).val from hat]
    exact hcommon
  refine ⟨hmgt,hn,t,ht,hat,htQ,hcommon',z,hz,hzc,U,hU,
    (map_mono (map_mono hUV)).trans hVQ,hUres,
    hUV,hUc,hker,inferInstance,hcard,htU,hfix,hfusion,hfixV,?_,hV,P₀,hP₀X,hzP,hPcentral⟩
  apply le_antisymm ?_ (UnitarySource.short_local_le_line_normalizer L t U V hVintrinsic hline)
  intro b hb
  let c : UnitarySource.shortLineNormalizer L t U := ⟨b,hb⟩
  apply (UnitarySource.shortLineLocalQuotient_mk_iff L t U c).mp
  change QuotientGroup.mk' (UnitarySource.shortLineKernel L t U) c ∈ X
  rw [htop]
  exact mem_top _

/-- Preserve the fixed-coset interface with its original core markings.
The stronger theorem additionally locates the whole line in a perfect actor. -/
theorem Preparation.unitary_short_fixed_cosets_sylow_with_core_of_odd_outer
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (r : UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm)
    (hodd : ¬ 2 ∣ (inner (ProjectiveGroup m hm)).relIndex r.extension.carrier) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧ t.val ∈ L.pCoreIn 2 ∧
      (∀ z ∈ (center (residual H)).map (residual H).subtype, orderOf z = 2 →
        centralizer ({t.val} : Set G) ⊓ centralizer ({z} : Set G) ≤ normalizer (L : Set G)) ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
      z.val.val ∈ (center (residual H)).map (residual H).subtype ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ hU : U ≤ center (centralizer ({t} : Set L)),
      (U.map (centralizer ({t} : Set L)).subtype).map L.subtype ≤ L.pCoreIn 2 ∧
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      let f := UnitarySource.shortLineQuotientMap L t U hU
      let X := UnitarySource.shortLineLocalQuotient L t U
      U ≤ V ∧ Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      (∃! q : centralizer ({t.val} : Set G) ⧸
          (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)),
        UnitarySource.shortCentralizerEmbedding L t z • q = q) ∧
      (∀ x y : centralizer ({t.val} : Set G),
        x.val ∈ normalizer (L : Set G) → y.val ∈ normalizer (L : Set G) →
        IsPGroup 2 (zpowers x) → IsConj x y →
        ∃ a : centralizer ({t.val} : Set G), a.val ∈ normalizer (L : Set G) ∧ a*x*a⁻¹ = y) ∧
      (∀ v ∈ V.map f, v ≠ 1 → ∃! q :
          (UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U) ⧸ X,
        v • q = q) ∧
      UnitarySource.shortLineNormalizer L t U =
        (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)) ∧
      IsElementaryAbelian 2 V ∧
      ∃ P : Sylow 2 (centralizer ({t.val} : Set G)),
        (P : Subgroup _) ≤
          (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)) ∧
        UnitarySource.shortCentralizerEmbedding L t z ∈ (P : Subgroup _) ∧
        ∀ b ∈ (P : Subgroup _), Commute (UnitarySource.shortCentralizerEmbedding L t z) b := by
  obtain ⟨_,_,e,_⟩ := d.unitary_short_root_common_centralizers h hH hp m hm hc
  obtain ⟨hmgt,hn,t,ht,_,htQ,hcommon,z,hz,hzc,U,hU,hUQ,_,hrest⟩ :=
    d.unitary_short_fixed_cosets_sylow_with_actor_at_of_odd_outer h hH hp m hm hc r hodd e
  exact ⟨hmgt,hn,t,ht,htQ,hcommon,z,hz,hzc,U,hU,hUQ,hrest⟩

/-- Preserve the original fixed-coset and Sylow interface. The strengthened
version also retains core placement and the entire root-group centralizer bound. -/
theorem Preparation.unitary_short_fixed_cosets_sylow_of_odd_outer
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (r : UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm)
    (hodd : ¬ 2 ∣ (inner (ProjectiveGroup m hm)).relIndex r.extension.carrier) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
      z.val.val ∈ (center (residual H)).map (residual H).subtype ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ hU : U ≤ center (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      let f := UnitarySource.shortLineQuotientMap L t U hU
      let X := UnitarySource.shortLineLocalQuotient L t U
      U ≤ V ∧ Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      (∃! q : centralizer ({t.val} : Set G) ⧸
          (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)),
        UnitarySource.shortCentralizerEmbedding L t z • q = q) ∧
      (∀ x y : centralizer ({t.val} : Set G),
        x.val ∈ normalizer (L : Set G) → y.val ∈ normalizer (L : Set G) →
        IsPGroup 2 (zpowers x) → IsConj x y →
        ∃ a : centralizer ({t.val} : Set G), a.val ∈ normalizer (L : Set G) ∧ a*x*a⁻¹ = y) ∧
      (∀ v ∈ V.map f, v ≠ 1 → ∃! q :
          (UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U) ⧸ X,
        v • q = q) ∧
      UnitarySource.shortLineNormalizer L t U =
        (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)) ∧
      IsElementaryAbelian 2 V ∧
      ∃ P : Sylow 2 (centralizer ({t.val} : Set G)),
        (P : Subgroup _) ≤
          (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)) ∧
        UnitarySource.shortCentralizerEmbedding L t z ∈ (P : Subgroup _) ∧
        ∀ b ∈ (P : Subgroup _), Commute (UnitarySource.shortCentralizerEmbedding L t z) b := by
  obtain ⟨hmgt,hn,t,ht,_,_,z,hz,hzc,U,hU,_,hrest⟩ :=
    d.unitary_short_fixed_cosets_sylow_with_core_of_odd_outer h hH hp m hm hc r hodd
  exact ⟨hmgt,hn,t,ht,z,hz,hzc,U,hU,hrest⟩

/-- The fixed-coset and line-normalizer conclusions, preserving the original
public interface. The stronger theorem also retains the same ambient Sylow. -/
theorem Preparation.unitary_short_fixed_cosets_of_odd_outer
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (r : UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm)
    (hodd : ¬ 2 ∣ (inner (ProjectiveGroup m hm)).relIndex r.extension.carrier) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
      z.val.val ∈ (center (residual H)).map (residual H).subtype ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ hU : U ≤ center (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      let f := UnitarySource.shortLineQuotientMap L t U hU
      let X := UnitarySource.shortLineLocalQuotient L t U
      U ≤ V ∧ Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      (∃! q : centralizer ({t.val} : Set G) ⧸
          (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)),
        UnitarySource.shortCentralizerEmbedding L t z • q = q) ∧
      (∀ x y : centralizer ({t.val} : Set G),
        x.val ∈ normalizer (L : Set G) → y.val ∈ normalizer (L : Set G) →
        IsPGroup 2 (zpowers x) → IsConj x y →
        ∃ a : centralizer ({t.val} : Set G), a.val ∈ normalizer (L : Set G) ∧ a*x*a⁻¹ = y) ∧
      (∀ v ∈ V.map f, v ≠ 1 → ∃! q :
          (UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U) ⧸ X,
        v • q = q) ∧
      UnitarySource.shortLineNormalizer L t U =
        (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)) := by
  obtain ⟨hmgt,hn,t,ht,z,hz,hzc,U,hU,hUV,hUc,hker,hVmap,hVc,htU,
      hfix,hfusion,hfixV,hNU,_⟩ :=
    d.unitary_short_fixed_cosets_sylow_of_odd_outer h hH hp m hm hc r hodd
  exact ⟨hmgt,hn,t,ht,z,hz,hzc,U,hU,hUV,hUc,hker,hVmap,hVc,htU,
    hfix,hfusion,hfixV,hNU⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
