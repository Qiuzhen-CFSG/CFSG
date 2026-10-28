module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.QuotientCentralizers
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortNormalizer
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.PerfectOrbit
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.MarkedQuotient
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortNormalizer

/-!
# Perfect action on the same prepared short-line quotient

Retain the short and long roots selected through one reduced comparison.
The orthogonal three-space is intrinsically [O₂(L),C_L(t)], so the full
local stabilizer normalizes its image in N_{C_G(t)}(U)/U. The fixed-field
SL₂ supplies an actual perfect subgroup acting transitively on the nonzero
quotient vectors. The full line remains exactly the kernel.

I.8.5 now proves N_{C_G(t)}(U) ≤ N_G(L) from the single marked unique-
fixed-coset premise, with no action-solvability premise. The ambient
fixed-coset and subsequent maximal-W arguments are still required.
Source: Aschbacher–Smith F.4.42, printed pp.295–296.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot
namespace UnitarySource
variable {G : Type*} [Group G] (L : Subgroup G) (t : L)

private theorem quotient_module_normal
    (U : Subgroup (centralizer ({t} : Set L)))
    (hU : U ≤ center (centralizer ({t} : Set L)))
    (V : Subgroup (centralizer ({t} : Set L)))
    (hV : V.map (centralizer ({t} : Set L)).subtype =
      ⁅pCore 2 L,centralizer ({t} : Set L)⁆) :
    ((V.map (shortLineQuotientMap L t U hU)).subgroupOf
      (shortLineLocalQuotient L t U)).Normal := by
  let Y := centralizer ({t} : Set L)
  let r := shortLineNormalizerMap L t U hU
  let q := QuotientGroup.mk' (shortLineKernel L t U)
  have hVamb : (V.map Y.subtype).map L.subtype =
      ⁅L.pCoreIn 2,L ⊓ centralizer ({t.val} : Set G)⁆ := by
    rw [hV,map_commutator,map_subtype_centralizer_singleton L t]
    rfl
  constructor
  intro v hv g
  obtain ⟨a,ha,he⟩ := g.property
  obtain ⟨w,hw,hwq⟩ := hv
  change g.val * v.val * g.val⁻¹ ∈ V.map (shortLineQuotientMap L t U hU)
  change shortLineQuotientMap L t U hU w = v.val at hwq
  rw [←he,←hwq]
  change q a * q (r w) * (q a)⁻¹ ∈ V.map (shortLineQuotientMap L t U hU)
  have hn := (short_normalizers L t.val).1 ⟨ha,a.val.property⟩
  have hwG : w.val.val ∈ (V.map Y.subtype).map L.subtype :=
    mem_map_of_mem L.subtype (mem_map_of_mem Y.subtype hw)
  have hreturn : a.val.val * w.val.val * a.val.val⁻¹ ∈
      (V.map Y.subtype).map L.subtype := by
    rw [hVamb] at hwG ⊢
    exact (mem_normalizer_iff.mp hn _).mp hwG
  obtain ⟨y,⟨b,hb,rfl⟩,hbval⟩ := hreturn
  have hconj : a * r w * a⁻¹ = r b := by
    apply Subtype.ext
    apply Subtype.ext
    exact hbval.symm
  rw [←map_inv,←map_mul,←map_mul,hconj]
  exact mem_map_of_mem (shortLineQuotientMap L t U hU) hb

end UnitarySource

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The original row supplies the perfect vector action on its actual
line-normalizer quotient. I.8.5 then discharges the first line-normalizer
contradiction from the precise remaining unique-fixed-coset premise. -/
theorem Preparation.unitary_short_quotient_perfect_action
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
      z.val.val ∈ (center (residual H)).map (residual H).subtype ∧
      centralizer ({t.val} : Set G) ⊓ centralizer ({z.val.val} : Set G) ≤
        normalizer (L : Set G) ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ hU : U ≤ center (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      let f := UnitarySource.shortLineQuotientMap L t U hU
      let X := UnitarySource.shortLineLocalQuotient L t U
      U ≤ V ∧ Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      V.map f ≤ X ∧ ((V.map f).subgroupOf X).Normal ∧
      (∃ P : Subgroup (UnitarySource.shortLineNormalizer L t U ⧸
          UnitarySource.shortLineKernel L t U), Group.IsPerfect P ∧ P ≤ X ∧
        ∀ v ∈ V.map f, v ≠ 1 → ∃ a ∈ P, a * f z * a⁻¹ = v) ∧
      ((∃! q : centralizer ({t.val} : Set G) ⧸
          (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)),
          UnitarySource.shortCentralizerEmbedding L t z • q = q) →
        UnitarySource.shortLineNormalizer L t U ≤
          (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G))) := by
  obtain ⟨hm',hn,e,_,_,_,hcommon⟩ :=
    d.unitary_short_root_common_centralizers h hH hp m hm hc
  have hr := d.reduced_parabolic_residuals h hH.1.1.2 hp
    (hc.elim (fun he => .unitary m hm he) (fun he => .unitaryExtension m hm he))
  obtain ⟨a,hat,haz⟩ := ChapterF.UnitarySource.FourShortMarked.marked_plane_equiv
    (ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L))
    L (residual H) hr m hm hm' e
  let t := a (shortLocal (MatrixField m) (fieldConj m) (fieldConj_involutive m hm))
  obtain ⟨ht,z,hzmark,hz,U,hV,hVQ,hVc,hUc,hindex,hUV,hU,htU,horbit,hVintrinsic,hperfect,_⟩ :=
    short_quotient_from_marked_equiv m hm hm' a
  have hzc : z.val.val ∈ (center (residual H)).map (residual H).subtype := by
    rw [hzmark]
    exact haz
  have hC : centralizer ({t.val} : Set G) ⊓ centralizer ({z.val.val} : Set G) ≤
      normalizer (L : Set G) := by
    rw [show t.val = (ChapterF.UnitarySource.FourShortTransport.sourceShort m hm e).val from hat]
    exact hcommon z.val.val hzc hz
  let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
  let f := UnitarySource.shortLineQuotientMap L t U hU
  let X := UnitarySource.shortLineLocalQuotient L t U
  have hker : f.ker = U := UnitarySource.shortLineQuotientMap_ker L t U hU
  let : IsElementaryAbelian 2 V := hV
  let : IsElementaryAbelian 2 (V.map f) := IsElementaryAbelian.map f
  have hcard : Nat.card (V.map f) = (2^m)^2 := by
    rw [←relIndex_ker,hker]
    exact hindex
  have hVX : V.map f ≤ X := by
    rintro v ⟨w,hw,rfl⟩
    exact UnitarySource.shortLineQuotientMap_mem_local L t U hU w
  let : ((V.map f).subgroupOf X).Normal :=
    UnitarySource.quotient_module_normal L t U hU V hVintrinsic
  obtain ⟨P,hP,hPr,horbitP⟩ := hperfect f hker.ge
  have hPX : P ≤ X := by
    intro v hv
    obtain ⟨w,rfl⟩ := hPr hv
    exact UnitarySource.shortLineQuotientMap_mem_local L t U hU w
  refine ⟨hm',hn,t,ht,z,hz,hzc,hC,U,hU,hUV,hUc,hker,inferInstance,hcard,
    hVX,inferInstance,⟨P,hP,hPX,horbitP⟩,?_⟩
  intro hfix
  let R := UnitarySource.shortLineNormalizer L t U
  let r := UnitarySource.shortLineNormalizerMap L t U hU
  let X₀ := UnitarySource.shortLineLocal L t U
  have hzX₀ : r z ∈ X₀ := L.le_normalizer z.val.property
  have hfixR : ∃! q : R ⧸ X₀, r z • q = q := by
    apply UniqueFixedCoset.unique_of_transporter hzX₀
    intro g hg
    exact UniqueFixedCoset.transporter_mem
      (M := (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G)))
      (L.le_normalizer z.val.property) hfix
      (g := g.val) hg
  have hfixQ : ∃! q : (R ⧸ UnitarySource.shortLineKernel L t U) ⧸ X,
      f z • q = q := UniqueFixedCoset.unique_map_of_surjective
    (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U))
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      exact UnitarySource.shortLineKernel_le_local L t U) hzX₀ hfixR
  let : Group.IsPerfect P := hP
  have hbig : 2 < Nat.card (V.map f) := by
    rw [hcard]
    have hq : 2 < 2^m := Nat.pow_lt_pow_right (by decide : 1 < 2) hm'
    nlinarith
  have htop := ChapterF.UnitarySource.eq_top_of_perfect_orbit
    (V.map f) X P hVX hPX hbig (f z)
    (mem_map_of_mem f (subset_normalClosure (Set.mem_singleton _))) horbitP hfixQ
  intro b hb
  let c : UnitarySource.shortLineNormalizer L t U := ⟨b,hb⟩
  apply (UnitarySource.shortLineLocalQuotient_mk_iff L t U c).mp
  change QuotientGroup.mk' (UnitarySource.shortLineKernel L t U) c ∈ X
  rw [htop]
  exact mem_top _

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
