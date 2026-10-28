module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Fusion
public import BenderSuzuki.SE.InvolutionsInTwoSubgroups
public import BenderSuzuki.SE.SingleInvolutionClass

/-!
# The original locals generate the ambient group

Repeat the established involution-fusion argument inside Y = L ∨ J: all
conjugators lie in L or J, and Y contains the original Sylow two-subgroup.
The original central involution has its full ambient centralizer inside J.
Thus a proper Y would be strongly embedded. The full Bender–Suzuki theorem
then makes all square-one elements of T commute. This would centralize
U = O₂(J) by V = O₂(L), forcing V ≤ U, contrary to their distinct original
normalizers. Therefore L ∨ J = G, and in particular N_G(L) ∨ J = G.

This proves the ambient-generation clause of Aschbacher–Smith 5.2.21,
printed p.657 (`refs/quasithin.pdf`), by the proved Bender–Suzuki theorem
instead of an induction on subgroup recognition. No induction, generation
or recognition premise is added; the full original KnownSimple input stays.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem affine_core_transitive_witness {F : Type} [Field F] [Finite F] [CharP F 2]
    (L : Subgroup G) (e : L ≃* Matrix.SL2.Affine F)
    {x y : G} (hx : x ∈ L.pCoreIn 2) (hy : y ∈ L.pCoreIn 2)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : ∃ l : L, (l : G)*x*(l : G)⁻¹ = y := by
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
  exact ⟨l,congrArg Subtype.val hh'.symm⟩

/-- The original L and exceptional J generate G, without a recognition premise. -/
theorem Preparation.linear_exceptional_ambient_generation
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
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J) : L ⊔ J = ⊤ := by
  have hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G) := by
    intro hK
    exact hKJ.ne (hK.2 J hJ.1 hKJ.le).symm
  have hn := (d.block_overcomponent_parameter h hH.1.1.2 hp F hm hF (.inl he) hJ.1 hKJ).1
  have hblock := d.linear_four_overcomponent_exceptional (hn ▸ h) hH.1.1.2 hp F hm hF he hJ.1 hKJ
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
  let : IsElementaryAbelian 2 (J.pCoreIn 2) := ha.map J.subtype
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
  let Y := L ⊔ J
  have hJY : J ≤ Y := le_sup_right
  have hLY : L ≤ Y := le_sup_left
  have hzY : z ∈ Y := hJY (map_subtype_le _ hzU)
  let zY : Y := ⟨z,hzY⟩
  let vJ : J := ⟨v,hTJ (hVT hvV)⟩
  obtain ⟨l,hl⟩ := affine_core_transitive_witness L hLaff.some hvV hzV hv1 hz1
  have hvz : IsConj (inclusion hJY vJ) zY := by
    exact isConj_iff.mpr ⟨inclusion hLY l,Subtype.ext hl⟩
  let e := hblock.2.1.some
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 J :=
    (MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective).trans (QuotientGroup.ker_mk' _)
  have hC : centralizer (pCore 2 J : Set J) = pCore 2 J :=
    le_antisymm (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
      (h.qtke.evenCharacteristic T) hJ.1)
      (fun x hx y hy => setLike_mul_comm hy hx)
  have hlocal (x : J) (hx : orderOf x = 2) : IsConj (inclusion hJY x) zY := by
    by_cases hxU : (x : G) ∈ J.pCoreIn 2
    · have hx1 : (x : G) ≠ 1 := by
        intro he
        have hh : x = 1 := Subtype.ext he
        simp [hh] at hx
      obtain ⟨a,ha⟩ := htrans x z hxU hzU hx1 hz1
      exact isConj_iff.mpr ⟨inclusion hJY a,Subtype.ext ha⟩
    · have hvJ : orderOf vJ = 2 := (Subgroup.orderOf_coe vJ).symm.trans hv2
      have hc := QuasithinM23.noncore_involutions_isConj (pCore 2 J) hcard q hq hk hC hx hvJ
        (fun hu => hxU (mem_map_of_mem J.subtype hu))
        (fun hu => hvU (mem_map_of_mem J.subtype hu))
      exact ((inclusion hJY).map_isConj hc).trans hvz
  have hTY : (T : Subgroup G) ≤ Y := hTJ.trans hJY
  have hclass (x : Y) (hx : orderOf x = 2) : IsConj x zY := by
    have hxp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (p := 2) (n := 1)
      (by rw [Nat.card_zpowers,hx]; norm_num)
    obtain ⟨P,hP⟩ := hxp.exists_le_sylow
    obtain ⟨a,ha⟩ := MulAction.exists_smul_eq Y P (T.subtype hTY)
    have hxa : a*x*a⁻¹ ∈ (T.subtype hTY : Subgroup Y) := by
      rw [←ha]
      exact mem_map_of_mem (MulAut.conj a).toMonoidHom (hP (mem_zpowers x))
    let xJ : J := ⟨((a*x*a⁻¹ : Y) : G),hTJ hxa⟩
    have hxJ : orderOf xJ = 2 := (Subgroup.orderOf_coe xJ).symm.trans
      ((Subgroup.orderOf_coe (a*x*a⁻¹)).trans (((MulAut.conj a).orderOf_eq x).trans hx))
    exact (isConj_iff.mpr ⟨a,rfl⟩).trans (hlocal xJ hxJ)
  by_contra hproper
  have hstrong := BenderSuzuki.isStronglyEmbedded_of_single_involution_class Y hproper z hz2 hzY
    (hCz.trans hJY) (by
      intro x hx hx2
      have hc := (hclass ⟨x,hx⟩ ((Subgroup.orderOf_coe ⟨x,hx⟩).symm.trans hx2)).symm
      obtain ⟨a,ha⟩ := isConj_iff.mp hc
      exact ⟨a,a.property,congrArg Subtype.val ha⟩)
  have hr : BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo G := by
    obtain ⟨E,hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := pCore 2 L) 2
      (n := 2) (by rw [hVcore.2]; decide)
    let f : pCore 2 L →* G := L.subtype.comp (pCore 2 L).subtype
    have hf : Function.Injective f := L.subtype_injective.comp (pCore 2 L).subtype_injective
    refine ⟨E.map f,?_,?_⟩
    · rw [card_map_of_injective hf,hE]
      rfl
    · rintro ⟨x,y,hy,rfl⟩
      apply Subtype.ext
      change f y ^ 2 = 1
      rw [←map_pow,Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (pCore 2 L)) y,map_one]
  apply hvU
  rw [←hCU]
  intro u hu
  have hUT : J.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ] using
      pCoreIn_le_sylow J (T.subtype hTJ)
  have hc := hstrong.squares_commute_in_twoSubgroup hr (T : Subgroup G) T.isPGroup' u v
    (hUT hu) (hVT hvV)
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) u hu)
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) v hvV)
  exact hc.eq

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
