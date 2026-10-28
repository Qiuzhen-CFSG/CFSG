module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Centralizer
public import Theory.GroupTheory.Recognition.QuasithinM23.InvolutionLifts

/-!
# Ambient involution fusion in the original nonmaximal linear row

The exceptional local J has two possible involution classes: its nonidentity
core elements form one class, and all involutions outside its core form one
class by the faithful binary A₇ action and the elementary coboundary argument.
The original left core V lies in the original Sylow subgroup. It contains the
central involution z and an element outside U = O₂(J): otherwise equal core
orders would identify their ambient normalizers, contradicting the prepared
right-factor escape. The compatible affine marking makes L transitive on
V minus the identity, joining the two local classes. Since J contains the
original Sylow two-subgroup, this proves ambient involution fusion.

This proves Aschbacher–Smith 5.2.13, printed p.654 (`refs/quasithin.pdf`).
It retains the selected field and compatible amalgam, and does not presume
that J splits, that the source completion is linear, or that G is M₂₃.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem affine_core_transitive {F : Type} [Field F] [Finite F] [CharP F 2]
    (L : Subgroup G) (e : L ≃* Matrix.SL2.Affine F)
    {x y : G} (hx : x ∈ L.pCoreIn 2) (hy : y ∈ L.pCoreIn 2)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : IsConj x y := by
  obtain ⟨x,hx,rfl⟩ := hx
  obtain ⟨y,hy,rfl⟩ := hy
  let a := ChapterC.SL2Affine.coreEquiv e
  let u := a.symm ⟨x,hx⟩
  let v := a.symm ⟨y,hy⟩
  have hu : u.toAdd ≠ 0 := by
    intro hz
    have hh : u = 1 := Multiplicative.toAdd.injective hz
    have hh' := congrArg a hh
    simp only [u,MulEquiv.apply_symm_apply,map_one] at hh'
    exact hx1 (congrArg (fun w : pCore 2 L => (w.val : G)) hh')
  have hv : v.toAdd ≠ 0 := by
    intro hz
    have hh : v = 1 := Multiplicative.toAdd.injective hz
    have hh' := congrArg a hh
    simp only [v,MulEquiv.apply_symm_apply,map_one] at hh'
    exact hy1 (congrArg (fun w : pCore 2 L => (w.val : G)) hh')
  obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq F u.toAdd v.toAdd hu hv
  let l := e.symm (SemidirectProduct.inr g)
  have hact : Matrix.SL2.naturalAction F (e l).right u = v := by
    change Matrix.SL2.naturalAction F (e (e.symm (SemidirectProduct.inr g))).right u = v
    rw [MulEquiv.apply_symm_apply,SemidirectProduct.right_inr]
    exact Multiplicative.toAdd.injective hg
  have hh := ChapterC.SL2Affine.coreEquiv_action e l u
  rw [hact] at hh
  have hh' : y = l*x*l⁻¹ := by simpa only [a,u,v,MulEquiv.apply_symm_apply] using hh
  exact isConj_iff.mpr ⟨(l : G),congrArg Subtype.val hh'.symm⟩

/-- Source 5.2.13: the ambient group has one conjugacy class of involutions,
from the original nonmaximal whole-residual linear row. -/
theorem Preparation.linear_nonmaximal_involutions_isConj
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
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
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G))
    {s t : G} (hs : orderOf s = 2) (ht : orderOf t = 2) : IsConj s t := by
  obtain ⟨_,hc⟩ := d.linear_maximal_or_exceptional h hH hp F hm hF he
  obtain ⟨hn,J,hJ,hKJ,hblock⟩ := hc.resolve_left hnonmax
  obtain ⟨hTJ,hHJ,hmax,hNJ,hNU,hCU,hHK,hcardJ⟩ :=
    d.linear_exceptional_local h hH hp F hm hF he hJ hKJ
  obtain ⟨_,_,_,hcores,hMcore,hNV,hCV,_⟩ :=
    d.linear_nonmaximal_core_geometry h hH hp F hm hF he hnonmax
  have hVcore : IsElementaryAbelian 2 (pCore 2 L) ∧ Nat.card (pCore 2 L) = 16 := hcores 0
  let := hVcore.1
  let : IsElementaryAbelian 2 (L.pCoreIn 2) := hVcore.1.map L.subtype
  obtain ⟨ha,hcard,_⟩ := d.linear_overcomponent_action h hH.1.1.2 hp F hm hF he hJ.1 hKJ.le
  rw [hn] at hcard
  have hcard : Nat.card (pCore 2 J) = 16 := hcard
  let := ha
  obtain ⟨_,htrans,z,hzU,hz2,hZeq,hCz,hCcore,hquot,hTI,hNT⟩ :=
    d.linear_exceptional_centralizer_geometry h hH hp F hm hF he hJ hKJ
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz2
  have hVT : L.pCoreIn 2 ≤ (T : Subgroup G) := by
    rw [←hMcore]
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le h.sylow_normalizes] using
      pCoreIn_le_sylow (normalizer (L : Set G)) (T.subtype h.sylow_normalizes)
  have hzV : z ∈ L.pCoreIn 2 := by
    rw [←hCV]
    have hzZ : z ∈ (center T).map (T : Subgroup G).subtype := hZeq ▸ mem_zpowers z
    obtain ⟨a,ha,rfl⟩ := hzZ
    intro v hv
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨v,hVT hv⟩)
  have hVU : ¬ L.pCoreIn 2 ≤ J.pCoreIn 2 := by
    intro hle
    have heq : L.pCoreIn 2 = J.pCoreIn 2 := by
      apply eq_of_le_of_card_ge hle
      change Nat.card ((pCore 2 J).map J.subtype) ≤ Nat.card ((pCore 2 L).map L.subtype)
      rw [card_map_of_injective J.subtype_injective,card_map_of_injective L.subtype_injective,
        hcard,hVcore.2]
    have hJM : J = normalizer (L : Set G) := by rw [←hNU,←heq,hNV]
    exact d.right_outside (hJM ▸ hKJ.le)
  obtain ⟨v,hvV,hvU⟩ := Set.not_subset.mp hVU
  have hv1 : v ≠ 1 := fun he => hvU (he ▸ one_mem _)
  have hv2 : orderOf v = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) v hvV) hv1
  have hLaff : Nonempty (L ≃* Matrix.SL2.Affine F) := by
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hH.1.1.2 hp F hm hF 0 true e.left).2.1
      exact ⟨a.trans (Matrix.PSL3.LinearThree.pointLocalEquivAffine F)⟩
    · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hH.1.1.2 hp F hm hF 0 false e.left).2.1
      exact ⟨a.trans (Matrix.PSL3.LinearThree.lineLocalEquivAffine F)⟩
  have hvz : IsConj v z := affine_core_transitive L hLaff.some hvV hzV hv1 hz1
  let e := hblock.2.1.some
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 J :=
    (MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective).trans (QuotientGroup.ker_mk' _)
  have hC : centralizer (pCore 2 J : Set J) = pCore 2 J :=
    le_antisymm (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
      (h.qtke.evenCharacteristic T) hJ.1)
      (fun x hx y hy => setLike_mul_comm hy hx)
  have hlocal (x : J) (hx : orderOf x = 2) : IsConj (x : G) z := by
    by_cases hxU : (x : G) ∈ J.pCoreIn 2
    · have hx1 : (x : G) ≠ 1 := by
        intro he
        have hh : x = 1 := Subtype.ext he
        simp [hh] at hx
      obtain ⟨a,ha⟩ := htrans x z hxU hzU hx1 hz1
      exact isConj_iff.mpr ⟨a,ha⟩
    · let vJ : J := ⟨v,hTJ (hVT hvV)⟩
      have hvJ : orderOf vJ = 2 := (Subgroup.orderOf_coe vJ).symm.trans hv2
      have hc := QuasithinM23.noncore_involutions_isConj (pCore 2 J) hcard q hq hk hC hx hvJ
        (fun hu => hxU (mem_map_of_mem J.subtype hu))
        (fun hu => hvU (mem_map_of_mem J.subtype hu))
      exact (J.subtype.map_isConj hc).trans hvz
  have hamb (x : G) (hx : orderOf x = 2) : IsConj x z := by
    have hxp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (p := 2) (n := 1)
      (by rw [Nat.card_zpowers,hx]; norm_num)
    obtain ⟨P,hP⟩ := hxp.exists_le_sylow
    obtain ⟨a,ha⟩ := MulAction.exists_smul_eq G P T
    have hxa : a*x*a⁻¹ ∈ (T : Subgroup G) := by
      rw [←ha]
      exact mem_map_of_mem (MulAut.conj a).toMonoidHom (hP (mem_zpowers x))
    let xJ : J := ⟨a*x*a⁻¹,hTJ hxa⟩
    have hxJ : orderOf xJ = 2 := (Subgroup.orderOf_coe xJ).symm.trans
      (((MulAut.conj a).orderOf_eq x).trans hx)
    exact (isConj_iff.mpr ⟨a,rfl⟩).trans (hlocal xJ hxJ)
  exact (hamb s hs).trans (hamb t ht).symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
