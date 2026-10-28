module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.ShortCentralizer
public import Theory.GroupTheory.InvolutionClassOrderComparison

/-!
# The ambient order of the same marked U₅(4) extension

Both full ambient involution centralizers lie in the original marked
normalizers. Their literal endpoint maps identify them with the full
centralizers in the same extension and preserve both involution classes.
The odd outer index supplies the extension's two-class coverage. Comparing
the commuting-class counts therefore gives the ambient order, without
assuming a completion or an ambient group isomorphism.

Source: Aschbacher–Smith F.4.42–43, printed pp.295–296 of
refs/quasithin.pdf, using the counting formula F.4.24.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
open UnitaryFiveFusion
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem full_centralizer_equiv {E : Type*} [Group E]
    (N : Subgroup G) (f : N →* E) (hf : Function.Injective f) (t : N)
    (hG : centralizer ({t.val} : Set G) ≤ N)
    (hE : centralizer ({f t} : Set E) ≤ f.range) :
    ∃ e : centralizer ({t.val} : Set G) ≃* centralizer ({f t} : Set E),
      ∀ x, (e x).val = f (inclusion hG x) := by
  let g : centralizer ({t.val} : Set G) →* centralizer ({f t} : Set E) :=
    (f.comp (inclusion hG)).codRestrict _ (by
      intro x
      apply mem_centralizer_singleton_iff.mpr
      change f (inclusion hG x) * f t = f t * f (inclusion hG x)
      rw [←map_mul,←map_mul]
      exact congrArg f (Subtype.ext (mem_centralizer_singleton_iff.mp x.property)))
  have hg : Function.Bijective g := by
    constructor
    · intro x y he
      exact (inclusion_injective hG) (hf (congrArg Subtype.val he))
    · intro y
      obtain ⟨x,hx⟩ := hE y.property
      have hxc : x.val ∈ centralizer ({t.val} : Set G) := by
        apply mem_centralizer_singleton_iff.mpr
        exact congrArg (fun v : N => v.val) (hf (show f (x*t)=f (t*x) from by
          simpa only [map_mul,hx] using mem_centralizer_singleton_iff.mp y.property))
      exact ⟨⟨x.val,hxc⟩,Subtype.ext hx⟩
  exact ⟨MulEquiv.ofBijective g hg,fun _ => rfl⟩

private theorem centralizerPoint_map {X Y : Type*} [Group X] [Group Y]
    (N : Subgroup X) (j : N →* Y) (u : N)
    (hN : centralizer ({u.val} : Set X) ≤ N)
    (e : centralizer ({u.val} : Set X) ≃* centralizer ({j u} : Set Y))
    (he : ∀ x, (e x).val = j (inclusion hN x)) :
    e (InvolutionClassOrderComparison.centralizerPoint u.val) =
      InvolutionClassOrderComparison.centralizerPoint (j u) := by
  apply Subtype.ext
  rw [InvolutionClassOrderComparison.centralizerPoint_coe,he]
  exact congrArg j (Subtype.ext (InvolutionClassOrderComparison.centralizerPoint_coe u.val))

/-- The full original source hypotheses determine the order of the same
marked extension, with no ambient order or centralizer premise. -/
theorem Preparation.unitaryFive_source_card_eq
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
 :
    Nat.card G = Nat.card r.extension.carrier := by
  obtain ⟨a,ell,F,h0,h1,hD,hE,hleft,hright,hmiddle,hz,ht,hz2,ht2,hzt,hcov,hfus,hnative,hcover⟩ :=
    d.unitaryFive_marked_ambient_classes h hH hp U hc r
  let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0
  let zP : P := a.comparison.left.symm U.longInvolution
  let tP : P := a.comparison.left.symm U.shortInvolution
  let zL := inclusion r.left_le zP
  let tL := inclusion r.left_le tP
  let j := markedLeftHom r F
  let k := markedRightHom r F
  have hj : Function.Injective j := (inclusion_injective r.extension.right_le).comp F.left.injective
  have hk : Function.Injective k := (inclusion_injective r.extension.left_le).comp F.right.injective
  have hT : tP.val ∈ (T : Subgroup G) := by
    have hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
      sSup_le fun _ hB => hB.1
    exact hJ ((d.unitaryFive_thompson h hH hp U hc).ge ht)
  let tD : (normalizerAmalgam L (residual H)).M₁₂ :=
    ⟨tP.val,tL.property,(hH.1.1.2.trans (le_normalizer_residual H)) hT⟩
  have hshort : (F.middle tD).val = MulAut.conj U.shortInvolution.val := by
    rw [←show (F.left tL).val = (F.middle tD).val from congrArg Subtype.val (F.left_commutes tD),h0]
    exact congrArg (fun x : U.rightParabolic => MulAut.conj x.val)
      (a.comparison.left.apply_symm_apply _)
  have htN : centralizer ({tL.val} : Set G) ≤ normalizer (L : Set G) :=
    d.unitaryFive_short_centralizer_at h hH hp U hc r a F h0 h1 tD ht ht2 hshort
  have hzC := d.unitaryFive_marked_long_mem_right_center h hH hp U hc a
  let zK : normalizer (residual H : Set G) :=
    ⟨zP.val,(residual H).le_normalizer (map_subtype_le _ hzC)⟩
  have hzN : centralizer ({zK.val} : Set G) ≤ normalizer (residual H : Set G) :=
    d.unitaryFive_central_involution_centralizers h hH hp U hc 1 zP.val hzC hz2
  have hjz : j zL = k zK := marked_overlap U r F ⟨zP.val,zL.property,zK.property⟩
  have hbasez : j zL = r.extension.baseHom U.longInvolution.val := by
    apply Subtype.ext
    exact (h0 zP).trans (congrArg (fun x : U.rightParabolic => MulAut.conj x.val)
      (a.comparison.left.apply_symm_apply _))
  have hbaset : j tL = r.extension.baseHom U.shortInvolution.val := by
    apply Subtype.ext
    exact (h0 tP).trans (congrArg (fun x : U.rightParabolic => MulAut.conj x.val)
      (a.comparison.left.apply_symm_apply _))
  have hEleft : k.range = r.extension.left.subgroupOf r.extension.carrier := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact (F.right y).property
    · intro hx
      obtain ⟨y,hy⟩ := F.right.surjective ⟨x.val,hx⟩
      exact ⟨y,Subtype.ext (congrArg (fun v : r.extension.left => v.val) hy)⟩
  have hEright : j.range = r.extension.right.subgroupOf r.extension.carrier := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact (F.left y).property
    · intro hx
      obtain ⟨y,hy⟩ := F.left.surjective ⟨x.val,hx⟩
      exact ⟨y,Subtype.ext (congrArg (fun v : r.extension.right => v.val) hy)⟩
  have hzE : centralizer ({k zK} : Set r.extension.carrier) ≤ k.range := by
    rw [←hjz,hbasez,hEleft]
    exact FiveExtension.long_root_centralizer_le U r.extension _
      U.longInvolution_mem_leftLocalImage_center (by
        intro he
        have hh : orderOf U.longInvolution.val = 2 :=
          (Subgroup.orderOf_coe _).trans U.longInvolution_order
        simp only [he,orderOf_one] at hh
        omega)
  have htE : centralizer ({j tL} : Set r.extension.carrier) ≤ j.range := by
    rw [hbaset,hEright]
    exact FiveExtension.shortInvolution_centralizer_le U r.extension
  obtain ⟨eZ,heZ⟩ := full_centralizer_equiv _ k hk zK hzN hzE
  obtain ⟨eT,heT⟩ := full_centralizer_equiv _ j hj tL htN htE
  have hztE : ¬ IsConj (k zK) (j tL) := by
    rw [←hjz]
    exact fun he => hzt ((marked_left_class d h hH hp U hc r a F h0 zL hz hz2 tL).mpr he)
  have hzE2 : orderOf (k zK) = 2 := by
    rw [←hjz,orderOf_injective j hj,←Subgroup.orderOf_coe]
    exact hz2
  have htE2 : orderOf (j tL) = 2 := by
    rw [orderOf_injective j hj,←Subgroup.orderOf_coe]
    exact ht2
  have hodd := d.unitaryFive_outer_odd h hH hp U hc r
  let I := (ChapterF.SourceCompletion.UnitaryNonbinary.inner U.Carrier).subgroupOf r.extension.carrier
  let : I.Normal := by
    constructor
    rintro b ⟨v,hv⟩ g
    refine ⟨g.val v,?_⟩
    change MulAut.conj (g.val v) =
      g.val * (r.extension.carrier.subtype b) * g.val⁻¹
    rw [←hv]
    ext x
    simp [MulAut.conj_apply,map_mul]
  have hbase : r.extension.baseHom.range = I := by
    ext x
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨b,rfl⟩
    · rintro ⟨b,hb⟩
      exact ⟨b,Subtype.ext hb⟩
  have hcoverE : ∀ x : r.extension.carrier, orderOf x = 2 →
      IsConj (k zK) x ∨ IsConj (j tL) x := by
    intro x hx
    have hpX : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1)
      (by simpa only [Nat.card_zpowers,pow_one] using hx)
    have hxI : x ∈ I :=
      IsPGroup.le_normal_of_index_primeTo I (zpowers x) hpX hodd (mem_zpowers x)
    obtain ⟨b,rfl⟩ := hbase.ge hxI
    have hb2 : orderOf b = 2 := by
      rwa [orderOf_injective r.extension.baseHom (r.extension.baseHom_injective (five_conj_injective U))] at hx
    rw [←hjz]
    exact hnative b hb2
  have hpointZ := centralizerPoint_map _ k zK hzN eZ heZ
  have hpointT := centralizerPoint_map _ j tL htN eT heT
  have hzZ (x : centralizer ({zK.val} : Set G)) :
      IsConj zK.val x.val ↔ IsConj (k zK) (eZ x).val := by
    rw [heZ x,←hjz]
    exact marked_right_class d h hH hp U hc r a F h0 zL hz hz2 (inclusion hzN x)
  have htZ (x : centralizer ({zK.val} : Set G)) :
      IsConj tL.val x.val ↔ IsConj (j tL) (eZ x).val := by
    rw [heZ x]
    exact marked_right_class d h hH hp U hc r a F h0 tL ht ht2 (inclusion hzN x)
  have hzT (x : centralizer ({tL.val} : Set G)) :
      IsConj zK.val x.val ↔ IsConj (k zK) (eT x).val := by
    rw [heT x,←hjz]
    exact marked_left_class d h hH hp U hc r a F h0 zL hz hz2 (inclusion htN x)
  have htT (x : centralizer ({tL.val} : Set G)) :
      IsConj tL.val x.val ↔ IsConj (j tL) (eT x).val := by
    rw [heT x]
    exact marked_left_class d h hH hp U hc r a F h0 tL ht ht2 (inclusion htN x)
  have hkZ := InvolutionClassOrderComparison.kappa_eq zK.val tL.val zK.val (k zK) (j tL) (k zK)
    hz2 ht2 hzt hzE2 htE2 hztE eZ hpointZ hzZ htZ
  have hkT := InvolutionClassOrderComparison.kappa_eq zK.val tL.val tL.val (k zK) (j tL) (j tL)
    hz2 ht2 hzt hzE2 htE2 hztE eT hpointT hzT htT
  have hcZ := Nat.card_congr eZ.toEquiv
  have hcT := Nat.card_congr eT.toEquiv
  rw [TwoInvolutionClassOrder.card_eq zK.val tL.val hz2 ht2 hzt hcover,
    TwoInvolutionClassOrder.card_eq (k zK) (j tL) hzE2 htE2 hztE hcoverE,hkZ,hkT,hcZ,hcT]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
