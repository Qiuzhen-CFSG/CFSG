module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortSylow
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourLongClass
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.QuotientCentralizers
public import Theory.GroupTheory.ConjugacyOrderCensus
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.MarkedQuotient
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortSylow
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.QuotientCentralizers
import all Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# The full local stabilizer preserves the marked long-root orbit

An automorphism of the plane residual fixing the short root preserves its
long-root class, by the intrinsic singular-cone/Sylow characterization.
Transport through the same reduced comparison therefore identifies the
full local stabilizer orbit with the residual orbit of size q²−1. Its odd
index and the established ambient Sylow placement produce a Sylow of
C_G(t) centralizing the original marked long root z.

The complete q-element short line remains the quotient kernel. The
existing ambient transporter bound and unique residual long-root lifts
now give the exact centralizer preimage in the entire line normalizer.
The image of the selected ambient Sylow centralizes the surviving image
of z. Both original comparisons and orientations, q=4, and n=2m with
m>1 are retained.

Source: Aschbacher–Smith F.4.42, printed pp.295–296. This establishes
invariance of the local orbit and ambient Sylow placement. Conjugates
returning to the whole local stabilizer still require the ambient fusion
argument; unique fixed cosets, maximal-W containment, outer transfer and
same-extension order are not asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitarySource
open ChapterF.GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot
variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)
variable (m : ℕ) (hm : 1 ≤ m) (hm' : 1 < m)
local notation "F" => MatrixField m
local notation "σ" => fieldConj m
local notation "hσ" => fieldConj_involutive m hm
local notation "B" => localFactor F (form F σ hσ)
local notation "C" => shortCentralizer F σ hσ

include hm' in
omit [Finite G] in
private theorem marked_longClass_fusion (e : B ≃* L) :
    let t := e (shortLocal F σ hσ)
    let Y := centralizer ({t} : Set L)
    let b := CentralizerSmallKernelTransport.centralizerEquiv e (shortLocal F σ hσ)
    let z := b (SourceNormalizer.FourShortRoot.longMark F σ hσ)
    ∀ g ∈ normalizer (L : Set G), g*t.val*g⁻¹ = t.val →
      ∃ a : Y, a.val.val*z.val.val*a.val.val⁻¹ = g*z.val.val*g⁻¹ := by
  let : NeZero m := ⟨by omega⟩
  dsimp only
  intro g hg hgt
  let c := L.normalizerMonoidHom ⟨g,hg⟩
  let a : MulAut B := e.trans (c.trans e.symm)
  have ha : a (shortLocal F σ hσ) = shortLocal F σ hσ := by
    apply e.injective
    change e (e.symm (c (e (shortLocal F σ hσ)))) = e (shortLocal F σ hσ)
    rw [e.apply_symm_apply]
    apply Subtype.ext
    exact hgt
  let x := SourceNormalizer.FourShortRoot.longMark F σ hσ
  have horbit := ChapterF.UnitarySource.FourLongClass.automorphism_preserves_longClass
    m hm hm' a ha x (IsConj.refl x)
  obtain ⟨k,hk⟩ := isConj_iff.mp horbit
  let b := CentralizerSmallKernelTransport.centralizerEquiv e (shortLocal F σ hσ)
  refine ⟨b k,?_⟩
  have he := congrArg (fun u : C => (e u.val).val) hk
  change (e (k.val*x.val*k.val⁻¹)).val = (e (a x.val)).val at he
  simp only [map_mul,map_inv] at he
  change (e k.val).val*(e x.val).val*(e k.val).val⁻¹ = g*(e x.val).val*g⁻¹
  have hea : e (a x.val) = c (e x.val) := e.apply_symm_apply _
  exact he.trans (congrArg Subtype.val hea)

variable {M : Type*} [Group M] [Finite M]
omit [Finite M] in
private theorem class_card_of_fusion {Y : Type*} [Group Y] [Finite Y]
    (X : Subgroup M) (j : Y →* M) (hj : Function.Injective j)
    (hjX : j.range ≤ X) (z : Y)
    (hfusion : ∀ a : X, ∃ b : Y, j (b*z*b⁻¹) = a.val*j z*a.val⁻¹) :
    Nat.card {x : X // IsConj (⟨j z,hjX ⟨z,rfl⟩⟩ : X) x} =
      Nat.card {y : Y // IsConj z y} := by
  let f : {y : Y // IsConj z y} → {x : X // IsConj (⟨j z,hjX ⟨z,rfl⟩⟩ : X) x} :=
    fun y => ⟨⟨j y.val,hjX ⟨y.val,rfl⟩⟩,(j.codRestrict X (fun y => hjX ⟨y,rfl⟩)).map_isConj y.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      exact Subtype.ext (hj (congrArg (fun x => x.val.val) he))
    · rintro ⟨x,hx⟩
      obtain ⟨a,ha⟩ := isConj_iff.mp hx
      obtain ⟨b,hb⟩ := hfusion a
      refine ⟨⟨b*z*b⁻¹,isConj_iff.mpr ⟨b,rfl⟩⟩,?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hb.trans (congrArg Subtype.val ha)
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

private theorem centralizer_index_eq_class_card (x : M) :
    (centralizer ({x} : Set M)).index = Nat.card {y : M // IsConj x y} := by
  have he := ConjClasses.nat_card_carrier_mul_card_centralizer x
  change Nat.card {y : M // IsConj x y} * _ = _ at he
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := centralizer ({x} : Set M)))
  rw [mul_comm,Subgroup.card_mul_index]
  exact he.symm

/-- An odd local conjugacy orbit and a local subgroup containing an ambient
Sylow produce an ambient Sylow centralizing the same representative. -/
private theorem ambient_sylow_centralizes_of_odd_class
    (X : Subgroup M) (x : X)
    (hodd : ¬ 2 ∣ Nat.card {y : X // IsConj x y})
    (P : Sylow 2 M) (hPX : (P : Subgroup M) ≤ X) :
    ∃ R : Sylow 2 M, (R : Subgroup M) ≤ X ∧
      (R : Subgroup M) ≤ centralizer ({x.val} : Set M) := by
  let Z := centralizer ({x} : Set X)
  have hZ : ¬ 2 ∣ Z.index := by
    rw [centralizer_index_eq_class_card]
    exact hodd
  have hX : ¬ 2 ∣ X.index := fun hd =>
    P.not_dvd_index (hd.trans (index_dvd_of_le hPX))
  let R : Sylow 2 Z := default
  let j := X.subtype.comp Z.subtype
  have hj : Function.Injective j := X.subtype_injective.comp Z.subtype_injective
  have hi : ¬ 2 ∣ ((R : Subgroup Z).map j).index := by
    change ¬ 2 ∣ ((R : Subgroup Z).map (X.subtype.comp Z.subtype)).index
    rw [←map_map,index_map_of_injective _ X.subtype_injective,range_subtype,
      index_map_of_injective _ Z.subtype_injective,range_subtype]
    exact Nat.prime_two.not_dvd_mul (Nat.prime_two.not_dvd_mul R.not_dvd_index hZ) hX
  refine ⟨(R.isPGroup'.map j).toSylow hi,?_,?_⟩
  · rintro _ ⟨a,ha,rfl⟩
    exact a.val.property
  · rintro _ ⟨a,ha,rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp a.property))
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitarySource

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The same marked long-root orbit is preserved by the entire local
stabilizer; an ambient short-centralizer Sylow centralizes that long root.
The literal full-line quotient has a Sylow centralizing its marked image. -/
theorem Preparation.unitary_short_full_stabilizer_orbit
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
      let X := (normalizer (L : Set G)).subgroupOf (centralizer ({t.val} : Set G))
      U ≤ V ∧ IsElementaryAbelian 2 V ∧
      Nat.card V = (2^m)^3 ∧ Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      f (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) = 1 ∧
      f z ≠ 1 ∧
      Nat.card {x : centralizer ({t} : Set L) // IsConj z x} = (2^m)^2 - 1 ∧
      (∀ v ∈ V.map f, v ≠ 1 →
        ∃! x : centralizer ({t} : Set L), IsConj z x ∧ f x = v) ∧
      (∀ g ∈ normalizer (L : Set G), g*t.val*g⁻¹ = t.val →
        ∃ a : centralizer ({t} : Set L),
          a.val.val*z.val.val*a.val.val⁻¹ = g*z.val.val*g⁻¹) ∧
      Nat.card {x : X // IsConj
        (⟨UnitarySource.shortCentralizerEmbedding L t z,L.le_normalizer z.val.property⟩ : X) x}
          = (2^m)^2 - 1 ∧
      (centralizer ({f z} : Set _)).comap
        (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U)) =
          centralizer ({UnitarySource.shortLineNormalizerMap L t U hU z} : Set _) ∧
      ∃ P : Sylow 2 (centralizer ({t.val} : Set G)),
        (P : Subgroup _) ≤ X ∧
        (P : Subgroup _) ≤ centralizer ({UnitarySource.shortCentralizerEmbedding L t z} : Set _) ∧
        (P : Subgroup _) ≤ UnitarySource.shortLineNormalizer L t U ∧
      ∃ Pbar : Sylow 2 (UnitarySource.shortLineNormalizer L t U ⧸
          UnitarySource.shortLineKernel L t U),
        (Pbar : Subgroup _) =
          ((P : Subgroup _).subgroupOf (UnitarySource.shortLineNormalizer L t U)).map
            (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U)) ∧
        (Pbar : Subgroup _) ≤ centralizer ({f z} : Set _) := by
  obtain ⟨hm',hn,e,_,_,_,hcommon⟩ :=
    d.unitary_short_root_common_centralizers h hH hp m hm hc
  have hr := d.reduced_parabolic_residuals h hH.1.1.2 hp
    (hc.elim (fun he => .unitary m hm he) (fun he => .unitaryExtension m hm he))
  obtain ⟨a,hat,haz⟩ := ChapterF.UnitarySource.FourShortMarked.marked_plane_equiv
    (ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L))
    L (residual H) hr m hm hm' e
  let t := a (shortLocal (MatrixField m) (fieldConj m) (fieldConj_involutive m hm))
  obtain ⟨ht,z,hzmark,hz,U,hV,hVQ,hVc,hUc,hindex,hUV,hU,htU,horbit,hcomm,_,hclass,hSylow,hlift,hline⟩ :=
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
  have hker : f.ker = U := UnitarySource.shortLineQuotientMap_ker L t U hU
  let : IsElementaryAbelian 2 V := hV
  have hcV : Nat.card (V.map f) = (2^m)^2 := by
    rw [←relIndex_ker,hker]
    exact hindex
  have horbit := horbit f hker.ge
  have hzne : f z ≠ 1 := by
    let : Nontrivial (V.map f) := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hcV]
      exact Nat.one_lt_pow (by decide) (Nat.one_lt_pow (by omega) (by decide)))
    obtain ⟨v,hv⟩ := exists_ne (1 : V.map f)
    have hvne : v.val ≠ 1 := fun he => hv (Subtype.ext he)
    obtain ⟨b,hb,he⟩ := horbit v.val v.property hvne
    intro hzero
    rw [hzero,mul_one,mul_inv_cancel] at he
    exact hvne he.symm
  have htkill : f (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) = 1 :=
    MonoidHom.mem_ker.mp (hker.ge (htU.le (mem_zpowers _)))
  have hfusion : ∀ g ∈ normalizer (L : Set G), g*t.val*g⁻¹ = t.val →
      ∃ b : centralizer ({t} : Set L),
        b.val.val*z.val.val*b.val.val⁻¹ = g*z.val.val*g⁻¹ := by
    intro g hg hgt
    obtain ⟨b,hb⟩ := UnitarySource.marked_longClass_fusion L m hm hm' a g hg hgt
    refine ⟨b,?_⟩
    rw [hzmark]
    exact hb
  let Y := centralizer ({t} : Set L)
  let M := centralizer ({t.val} : Set G)
  let X := (normalizer (L : Set G)).subgroupOf M
  let j := UnitarySource.shortCentralizerEmbedding L t
  have hjX : j.range ≤ X := by
    rintro _ ⟨b,rfl⟩
    exact L.le_normalizer b.val.property
  let zX : X := ⟨j z,L.le_normalizer z.val.property⟩
  have hclassX : Nat.card {x : X // IsConj zX x} = (2^m)^2 - 1 := by
    rw [UnitarySource.class_card_of_fusion X j
      (UnitarySource.shortCentralizerEmbedding_injective L t) hjX z]
    · exact hclass
    · intro g
      obtain ⟨b,hb⟩ := hfusion g.val.val g.property
        (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp g.val.property))
      exact ⟨b,Subtype.ext hb⟩
  have htQ : t.val ∈ L.pCoreIn 2 := hVQ
    (mem_map_of_mem L.subtype (mem_map_of_mem Y.subtype
      (hUV (htU.le (mem_zpowers _)))))
  obtain ⟨R,hRz⟩ := hSylow
  obtain ⟨P₀,_,_,hP₀⟩ :=
    d.unitary_short_centralizer_sylow_extension h hH hp m hm hc t htQ R
  have hP₀X : (P₀ : Subgroup M) ≤ X := by
    intro b hb
    exact hP₀ (mem_map_of_mem M.subtype hb)
  have hodd : ¬ 2 ∣ Nat.card {x : X // IsConj zX x} := by
    rw [hclassX]
    have hq : 2 ∣ (2^m)^2 := dvd_pow (dvd_pow_self 2 (by omega : m ≠ 0)) (by decide)
    have hpos : 0 < (2^m)^2 := by positivity
    omega
  obtain ⟨P,hPX,hPz⟩ := UnitarySource.ambient_sylow_centralizes_of_odd_class X zX hodd P₀ hP₀X
  have hLN := UnitarySource.short_local_le_line_normalizer L t U V hcomm hline
  have hPN : (P : Subgroup M) ≤ UnitarySource.shortLineNormalizer L t U := hPX.trans hLN
  let N := UnitarySource.shortLineNormalizer L t U
  let q := QuotientGroup.mk' (UnitarySource.shortLineKernel L t U)
  let Pbar := (P.subtype hPN).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let r := UnitarySource.shortLineNormalizerMap L t U hU
  have hpre : (centralizer ({f z} : Set _)).comap q =
      centralizer ({r z} : Set _) := by
    ext b
    constructor
    · intro hb
      have hqfix : q b * f z * (q b)⁻¹ = f z :=
        mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hb)
      have hzQ : z.val.val ∈ L.pCoreIn 2 := hVQ
        (mem_map_of_mem L.subtype (mem_map_of_mem Y.subtype
          (subset_normalClosure (Set.mem_singleton _))))
      have hUQ : ∀ u ∈ U, u.val.val ∈ L.pCoreIn 2 := by
        intro u hu
        exact hVQ (mem_map_of_mem L.subtype (mem_map_of_mem Y.subtype (hUV hu)))
      have hbX := short_line_quotient_transporter d h hH hp m hm hc t htQ z hzQ
        hC U hU hUQ (q b) (by
          rw [hqfix]
          exact ⟨r z,hzQ,rfl⟩)
      have hbL : b.val.val ∈ normalizer (L : Set G) :=
        (UnitarySource.shortLineLocalQuotient_mk_iff L t U b).mp hbX
      obtain ⟨c,hc⟩ := hfusion b.val.val hbL
        (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp b.val.property))
      have he : b*r z*b⁻¹ = r (c*z*c⁻¹) := Subtype.ext (Subtype.ext hc.symm)
      have himage : f (c*z*c⁻¹) = f z := by
        change q (r (c*z*c⁻¹)) = f z
        rw [←he,map_mul,map_mul,map_inv]
        exact hqfix
      have hlifts := hlift f hker (f z)
        (mem_map_of_mem f (subset_normalClosure (Set.mem_singleton _))) hzne
      have hcfix : c*z*c⁻¹ = z := hlifts.unique
        ⟨isConj_iff.mpr ⟨c,rfl⟩,himage⟩ ⟨IsConj.refl z,rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      apply mul_inv_eq_iff_eq_mul.mp
      exact he.trans (congrArg r hcfix)
    · intro hb
      apply mem_centralizer_singleton_iff.mpr
      exact (q.map_mul _ _).symm.trans
        ((congrArg q (mem_centralizer_singleton_iff.mp hb)).trans (q.map_mul _ _))
  refine ⟨hm',hn,t,ht,z,hz,hzc,hC,U,hU,hUV,hV,hVc,hUc,hker,
    IsElementaryAbelian.map f,hcV,htU,htkill,hzne,hclass,hlift f hker,
    hfusion,hclassX,hpre,P,hPX,hPz,hPN,Pbar,rfl,?_⟩
  rintro _ ⟨b,hb,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  have he : b * r z = r z * b := Subtype.ext
    (mem_centralizer_singleton_iff.mp (hPz hb))
  exact (q.map_mul _ _).symm.trans ((congrArg q he).trans (q.map_mul _ _))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
