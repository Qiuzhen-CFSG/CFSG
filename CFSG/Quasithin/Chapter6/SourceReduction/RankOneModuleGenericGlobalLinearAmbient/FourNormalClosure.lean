module
public import CFSG.Quasithin.Chapter5.Section03LinearSource.NormalClosure
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.FourSylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.LineFusion
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan

/-!
# The actual central-line normal closure at field four

For an original Sylow-central involution z, take the normal closure of
Z(S) in C_G(z). Characteristic-two descent modulo the same z proves that
this closure lies in O₂(C_G(z)) and that each square lies in ⟨z⟩.

If the closure is abelian, its involutory generators make it elementary.
It centralizes Z(S), hence lies in S and in one of the two root planes.
Every generating conjugate of Z(S) contains z, so the proved partition of
that plane forces it to equal Z(S). This closes the abelian centralizer
branch without an assumed ambient hyperplane-centralizer calculation.

Source: Aschbacher--Smith §5.3.6(2), §5.3.7, printed pp.660--661
(`refs/quasithin.pdf`). The nonabelian quaternion branch and ambient
recognition are not asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
open Matrix.PSL3Even.UnipotentGeometry Matrix.PSL3.LinearAmbientGeometry
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include d h hH hp hm hF he hmax

/-- The literal normal closure used in the exceptional centralizer proof. -/
@[expose] def linearCentralLineClosure (L H : Subgroup G) (z : G) : Subgroup G :=
  conjugateSpanBy (centerIn (sourceS L H)) (centralizer ({z} : Set G))

/-- At field four the actual normal closure lies in the centralizer two-core,
and every square lies in the marked central involution subgroup. -/
theorem Preparation.linear_four_normalClosure (hn : n = 2)
    (z : G) (hz2 : orderOf z = 2) (hz : z ∈ centerIn (sourceS L H))
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    linearCentralLineClosure L H z ≤ (centralizer ({z} : Set G)).pCoreIn 2 ∧
    ∀ x ∈ linearCentralLineClosure L H z, x^2 ∈ zpowers z := by
  let C := centralizer ({z} : Set G)
  let Z := centerIn (sourceS L H)
  have hZC : Z ≤ C := fun x hx => mem_centralizer_singleton_iff.mpr (hx.2 z hz.1).symm
  let zC : C := ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩
  let U := zpowers zC
  have hu : U ≤ center C := zpowers_le_of_mem (mem_center_iff.mpr (fun x =>
    Subtype.ext (mem_centralizer_singleton_iff.mp x.property)))
  let : U.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hu hx) g,mul_assoc,mul_inv_cancel,mul_one]
    exact hx⟩
  let ZC := Z.subgroupOf C
  have hgeo := d.linear_involution_geometry h hH hp F hm hF he hmax
  have hZV : Z ≤ L.pCoreIn 2 := by
    rw [←centerIn_eq_map_center] at hgeo
    exact hgeo.1.le.trans inf_le_left
  let : IsElementaryAbelian 2 (L.pCoreIn 2) :=
    ((d.linear_core_structure h hH hp F hm hF he).2.2 0).1
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_injective
    (inclusion hZV) (inclusion_injective hZV)
  let : IsElementaryAbelian 2 ZC := IsElementaryAbelian.subgroupOf hZC
  have hZ4 : Nat.card Z = 4 := by
    change Nat.card (centerIn (sourceS L H)) = 4
    rw [centerIn_eq_map_center,card_map_of_injective (sourceS L H).subtype_injective,
      hgeo.2.1,hF,(d.linear_core_structure h hH hp F hm hF he).1,hn]
    rfl
  have hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G) := by
    rw [d.linear_center_normalizer h hH hp F hm hF he hmax]
    exact le_inf h.sylow_normalizes (hH.1.1.2.trans (le_normalizer_residual H))
  have hnZ : (T.subtype hzT : Subgroup C) ≤ normalizer (ZC : Set C) := by
    intro x hx
    exact (subgroupOf_normalizer_eq hZC).le (hTZ hx)
  have hchar : centralizer (pCore 2 C : Set C) ≤ pCore 2 C :=
    Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
      (h.qtke.evenCharacteristic T) (isTwoLocal_involution_centralizer hz2) hzT)
  obtain ⟨hcore, helem⟩ := Chapter5.Section03LinearSource.four_normalClosure
    (T.subtype hzT) ZC U hchar hnZ
    ((Nat.card_congr (subgroupOfEquivOfLe hZC).toEquiv).trans hZ4)
    (by rw [Nat.card_zpowers,Subgroup.orderOf_mk,hz2])
    (zpowers_le_of_mem hz) hu
  have hcl : normalClosure (ZC : Set C) =
      (linearCentralLineClosure L H z).subgroupOf C :=
    normalClosure_subgroupOf_eq_conjugateSpanBy Z C hZC
  have hWC : linearCentralLineClosure L H z ≤ C := conjugateSpanBy_le_self hZC
  constructor
  · have hh := map_mono hcore (f := C.subtype)
    rw [hcl,map_subgroupOf_eq_of_le hWC] at hh
    exact hh
  · intro x hx
    let a : C := ⟨x,hWC hx⟩
    have ha : a ∈ normalClosure (ZC : Set C) := hcl.symm ▸ hx
    let q := QuotientGroup.mk' U
    let := helem
    have hs : q a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (q a) (mem_map_of_mem q ha)
    have hk : a^2 ∈ U := (QuotientGroup.eq_one_iff (N := U) (a^2)).mp (by
      change q (a^2)=1
      rwa [map_pow])
    have hm := mem_map_of_mem C.subtype hk
    simpa only [U,MonoidHom.map_zpowers,map_pow,Subgroup.coe_subtype,zC,a] using hm

/-- A normal closure lying in either original root plane forces the
centralizer to preserve the original central line. -/
theorem Preparation.linear_centralizer_le_inter_of_normalClosure_le_plane
    (z : G) (hz : z ∈ centerIn (sourceS L H)) (hz1 : z ≠ 1)
    (i : Fin 2)
    (hplane : linearCentralLineClosure L H z ≤ (![L,residual H] i).pCoreIn 2) :
    centralizer ({z} : Set G) ≤
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
  rw [←d.linear_center_normalizer h hH hp F hm hF he hmax]
  intro g hg
  have hconj : (centerIn (sourceS L H)).conjBy g ≤
      (![L,residual H] i).pCoreIn 2 := by
    rintro _ ⟨a,ha,rfl⟩
    apply hplane
    exact le_normalizer_iff.mp
      (le_normalizer_conjugateSpanBy (centerIn (sourceS L H)) (centralizer ({z} : Set G)))
      g hg a (le_conjugateSpanBy _ _ ha)
  obtain ⟨a,ha,heqa⟩ := d.linear_root_line_fusion h hH hp F hm hF he hmax i g hconj
  have hzg : z ∈ (centerIn (sourceS L H)).conjBy g := by
    refine ⟨z,hz,?_⟩
    change g*z*g⁻¹=z
    rw [mem_centralizer_singleton_iff.mp hg,mul_assoc,mul_inv_cancel,mul_one]
  have hh := d.linear_local_root_lines_eq h hH hp F hm hF he hmax i a 1 z
    ha (one_mem _) (heqa.symm ▸ hzg) ⟨z,hz,by simp⟩ hz1
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact heqa.symm.trans (hh.trans (by
    ext x
    simp [Subgroup.conjBy]))

/-- The abelian normal-closure case of §5.3.7 is closed using the actual
central-line partition, without an ambient hyperplane-centralizer premise. -/
theorem Preparation.linear_four_centralizer_le_inter_of_abelian_normalClosure
    (hn : n = 2) (z : G) (hz2 : orderOf z = 2)
    (hz : z ∈ centerIn (sourceS L H))
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcomm : IsMulCommutative (linearCentralLineClosure L H z)) :
    centralizer ({z} : Set G) ≤
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
  let U := linearCentralLineClosure L H z
  let Z := centerIn (sourceS L H)
  have hZU : Z ≤ U := le_conjugateSpanBy _ _
  let : IsMulCommutative U := hcomm
  have hUZ : U ≤ centralizer (Z : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr hcomm).trans (centralizer_le hZU)
  have hUT : U ≤ (T : Subgroup G) :=
    (d.linear_four_normalClosure h hH hp F hm hF he hmax hn z hz2 hz hzT).1.trans
      (d.linear_centralizer_core_displacement h hH hp F hm hF he hmax z hz hzT).1
  have hUS : U ≤ sourceS L H := by
    have hh := le_inf hUT hUZ
    rwa [d.linear_sylow_center_centralizer h hH hp F hm hF he hmax] at hh
  have helem : IsElementaryAbelian 2 U := by
    let : IsMulCommutative (Subgroup.closure
      {x | ∃ g ∈ centralizer ({z} : Set G), ∃ a ∈ centerIn (sourceS L H), g*a*g⁻¹=x}) := hcomm
    apply IsElementaryAbelian.closure_of_isMulCommutative
    rintro _ ⟨g,hg,a,ha,rfl⟩
    have ha2 := (d.linear_involution_geometry h hH hp F hm hF he hmax).2.2.2.1 a
      (by rwa [←centerIn_eq_map_center])
    change (MulAut.conj g a)^2=1
    rw [←map_pow,ha2,map_one]
  let := helem
  obtain ⟨e,hplanes⟩ := d.linear_root_coordinates h hH hp F hm hF he hmax
  have hplane := marked_elementary_le_plane F (sourceS L H) e U hUS
  have hplane' : U ≤ L.pCoreIn 2 ∨ U ≤ (residual H).pCoreIn 2 := by
    rcases hplanes with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · simpa only [hl,hr] using hplane
    · simpa only [hl,hr,or_comm] using hplane
  have hz1 : z ≠ 1 := by intro heq; simp [heq] at hz2
  rcases hplane' with hplane | hplane
  · exact d.linear_centralizer_le_inter_of_normalClosure_le_plane h hH hp F hm hF he hmax
      z hz hz1 0 hplane
  · exact d.linear_centralizer_le_inter_of_normalClosure_le_plane h hH hp F hm hF he hmax
      z hz hz1 1 hplane

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
