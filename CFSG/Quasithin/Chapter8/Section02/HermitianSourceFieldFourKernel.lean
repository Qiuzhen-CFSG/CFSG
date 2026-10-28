module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCentralizer
public import Theory.GroupTheory.PerfectCentralCoverLocalResidual
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# The two-core kernel of the Hermitian normalizer residual

For the original subgroup R = N_L(U)^∞, the full action on U is SL₂(4).
Its pointwise kernel maps into the plane radical of the faithful Hermitian
image. This radical is a two-group. In L/O₂(L), the remaining module kernel
is central. The perfect residual image has odd-prime rank at most one, so
cyclic-Sylow transfer removes that central kernel. Consequently the actual
kernel C_R(U) is a two-group and is exactly O₂(R); the original quotient
R/O₂(R) is isomorphic to SL₂(4).

The argument retains a possibly nonfaithful original component action and
uses its quasisimple two-core quotient. The Chapter 12 companion discharges
these hypotheses on both original closure branches. This is the Hermitian
clause of 8.2.6(3); the containing component's quotient in 8.2.7 remains a
separate source obligation.

Source: Aschbacher--Smith H.4.6(2), 8.2.6(3), and I.1.2, printed
pp.382,717,407, refs/quasithin.pdf (1 March 2004 manuscript).
-/

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
public noncomputable section
open ChapterE

private theorem perfect_kernel_two
    {X Y R : Type*} [Group X] [Finite X] [Group Y] [Finite Y] [Nontrivial Y]
    [Group R] [Finite R] [Group.IsPerfect R] [IsQuasisimple (X ⧸ pCore 2 X)]
    (q : X →* Y) (hq : Function.Surjective q) (hk : pCore 2 X ≤ q.ker)
    (i : R →* X) (hi : Function.Injective i)
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p (q.comp i).range ≤ 1) :
    IsPGroup 2 (q.comp i).ker := by
  let π := QuotientGroup.mk' (pCore 2 X)
  let c := QuotientGroup.lift (pCore 2 X) q hk
  have hc : Function.Surjective c := QuotientGroup.lift_surjective_of_surjective _ _ hq _
  have hcZ : c.ker ≤ center (X ⧸ pCore 2 X) := by
    rcases IsQuasisimple.normal_le_center_or_eq_top c.ker with hz | ht
    · exact hz
    · exfalso
      obtain ⟨y,hy⟩ := exists_ne (1 : Y)
      obtain ⟨x,rfl⟩ := hc y
      exact hy (show x ∈ c.ker from ht.symm ▸ mem_top x)
  let cover : PerfectCentralCovering.Cover (X ⧸ pCore 2 X) Y :=
    ⟨c,hc,inferInstance,hcZ⟩
  let K := (π.comp i).range
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (π.comp i).rangeRestrict) (π.comp i).rangeRestrict_surjective
  have hmap : K.map c = (q.comp i).range := by
    ext y
    constructor
    · rintro ⟨x,⟨r,rfl⟩,rfl⟩
      exact ⟨r,rfl⟩
    · rintro ⟨r,rfl⟩
      exact ⟨π (i r),⟨r,rfl⟩,rfl⟩
  have hinj := cover.injective_on_perfect_subgroup (pCore_quotient_pCore_eq_bot 2)
    K (fun p hp ho => by rw [hmap]; exact hr p hp ho)
  let j : (q.comp i).ker →* pCore 2 X :=
    { toFun := fun r => ⟨i r.val,by
        apply (QuotientGroup.eq_one_iff (N := pCore 2 X) (i r.val)).mp
        have he : c.subgroupMap K ⟨π (i r.val),⟨r.val,rfl⟩⟩ = 1 := by
          apply Subtype.ext
          exact r.property
        exact congrArg Subtype.val (hinj (he.trans (map_one _).symm))⟩
      map_one' := by apply Subtype.ext; exact map_one i
      map_mul' := fun a b => by apply Subtype.ext; exact map_mul i a.val b.val }
  exact pCore_isPGroup.of_injective j (fun a b hab =>
    Subtype.ext (hi (congrArg Subtype.val hab)))

/-- The original residual has precisely its two-core as pointwise kernel
on the canonical rank-four subgroup, including a possible central cover of
the original component. -/
theorem field_four_fixed_residual_kernel
    {G : Type*} [Group G] [Finite G]
    (V L U : Subgroup G) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 U]
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hUV : U ≤ V) (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1)
    (q : L →* binaryImage 1) (hq : Function.Surjective q)
    (hk : pCore 2 L ≤ q.ker)
    (he : ∀ (l : L) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v) = (q l).val (e v))
    (hU : ∀ v : Additive V, (v.toMul : G) ∈ U ↔
      e v ∈ fixedSpace (UnipotentRadicals.ambientAction 1) (UnipotentRadicals.plane 1)) :
    let R := (solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).map
      (L ⊓ normalizer (U : Set G)).subtype
    R ⊓ centralizer (U : Set G) = R.pCoreIn 2 ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* SL(2,E 1)) := by
  let : Finite (binaryImage 1) := Finite.of_surjective q hq
  let H := L ⊓ normalizer (U : Set G)
  let R := solvableResidual H
  let i : R →* L := (inclusion (show H ≤ L from inf_le_left)).comp R.subtype
  let a : R →* Automizer U := U.normalizerMonoidHom.rangeRestrict.comp
    ((inclusion (show H ≤ normalizer (U : Set G) from inf_le_right)).comp R.subtype)
  have haC (r : R) : a r = 1 ↔ (r.val.val : G) ∈ centralizer (U : Set G) := by
    change inclusion (show H ≤ normalizer (U : Set G) from inf_le_right) r.val ∈
      U.normalizerMonoidHom.rangeRestrict.ker ↔ _
    rw [MonoidHom.ker_rangeRestrict,Subgroup.normalizerMonoidHom_ker]
    rfl
  obtain ⟨_,f,hf,hrange,_⟩ := field_four_fixed_subgroup_sl2_action V L U hUV hLN e q hq he hU
  have ha : a.range = f.range := by
    rw [hrange]
    apply le_antisymm
    · rintro _ ⟨x,rfl⟩
      exact mem_map_of_mem U.normalizerMonoidHom.rangeRestrict
        (mem_map_of_mem H.subtype x.property)
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨y,hy,hyx⟩ := hx
      refine ⟨⟨y,hy⟩,?_⟩
      exact congrArg U.normalizerMonoidHom.rangeRestrict (Subtype.ext hyx)
  let ea : SL(2,E 1) ≃* a.range :=
    (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr ha.symm)
  let α := ea.symm.toMonoidHom.comp a.rangeRestrict
  have hα : Function.Surjective α := ea.symm.surjective.comp a.rangeRestrict_surjective
  have hαa (r : R) : α r = 1 ↔ a r = 1 := by
    change ea.symm (a.rangeRestrict r) = 1 ↔ a r = 1
    rw [ea.symm.map_eq_one_iff]
    exact Subtype.ext_iff
  let b := q.comp i
  have hba : b.rangeRestrict.ker ≤ α.ker := by
    intro r hr
    apply (hαa r).mpr
    apply (haC r).mpr
    intro u hu
    let v : Additive V := Additive.ofMul ⟨u,hUV hu⟩
    have hq1 : q (i r) = 1 := congrArg Subtype.val hr
    have hh := he (i r) v
    rw [hq1] at hh
    have hh' := congrArg (fun w : Additive V => (w.toMul : G)) (e.injective hh)
    change (r.val.val : G) * u * (r.val.val : G)⁻¹ = u at hh'
    exact (mul_inv_eq_iff_eq_mul.mp hh').symm
  let β : b.range →* SL(2,E 1) :=
    b.rangeRestrict.liftOfSurjective b.rangeRestrict_surjective ⟨α,hba⟩
  have hβ (r : R) : β (b.rangeRestrict r) = α r :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  let : Nontrivial (binaryImage 1) :=
    (((imageEquivPSL 1 (by decide)).symm.trans (binaryImageEquiv 1)).injective).nontrivial
  have hβ2 : IsPGroup 2 β.ker := by
    have hplane (x : β.ker) : x.val.val.val ∈ UnipotentRadicals.plane 1 := by
      obtain ⟨r,hr⟩ := b.rangeRestrict_surjective x.val
      have hrα : α r = 1 := (hβ r).symm.trans ((congrArg β hr).trans x.property)
      have hrC := (haC r).mp ((hαa r).mp hrα)
      have hfix : ∀ X : Space 1, X ∈ fixedSpace (UnipotentRadicals.ambientAction 1)
          (UnipotentRadicals.plane 1) → (q (i r)).val X = X := by
        intro X hX
        obtain ⟨v,rfl⟩ := e.surjective X
        rw [← he]
        apply congrArg e
        apply Additive.toMul.injective
        apply Subtype.ext
        change (r.val.val : G) * (v.toMul : G) * (r.val.val : G)⁻¹ = (v.toMul : G)
        rw [← hrC _ ((hU v).mpr hX),mul_assoc,mul_inv_cancel,mul_one]
      have ht := (field_four_plane_pointwise_stabilizer _ (q (i r)).property).mp hfix
      have hv := congrArg (fun z : b.range => z.val.val) hr
      exact hv ▸ ht
    let j : β.ker →* UnipotentRadicals.plane 1 :=
      (((binaryImage 1).subtype.comp b.range.subtype).comp β.ker.subtype).codRestrict _ hplane
    have hj : Function.Injective j := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (Subtype.ext
        (congrArg (fun z : UnipotentRadicals.plane 1 => z.val) hxy)))
    have hp : IsPGroup 2 (UnipotentRadicals.plane 1) :=
      (IsElementaryAbelian.isPGroup 2 (Matrix.PSL3Even.UnipotentGeometry.V₂ (E 1))).map
        (UnipotentRadicals.unipotentHom 1)
    exact hp.of_injective j hj
  have hb2 : IsPGroup 2 b.ker := perfect_kernel_two q hq hk i
    ((inclusion_injective (show H ≤ L from inf_le_left)).comp R.subtype_injective) (fun p hp ho => by
      let : Fact p.Prime := ⟨hp⟩
      exact Matrix.SL2.primeRank_le_one_of_two_kernel ho β hβ2)
  have hb2' : IsPGroup 2 b.rangeRestrict.ker := by
    rwa [MonoidHom.ker_rangeRestrict]
  have hα2 : IsPGroup 2 α.ker := by
    have hh := hβ2.comap_of_ker_isPGroup b.rangeRestrict hb2'
    have heq : β.ker.comap b.rangeRestrict = α.ker := by
      ext r
      change β (b.rangeRestrict r) = 1 ↔ α r = 1
      rw [hβ]
    rwa [heq] at hh
  have hker : α.ker = pCore 2 R := by
    have hh := α.comap_pCore_of_ker_isPGroup hα hα2
    rw [Atlas.RankOneFieldAutomorphisms.sl_twoCore_eq_bot] at hh
    exact hh
  let er := R.equivMapOfInjective H.subtype H.subtype_injective
  let eq := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)
  refine ⟨?_,⟨(QuotientGroup.congr _ _ er (pCore_map_iso 2 er)).symm.trans eq⟩⟩
  have hm : α.ker.map (H.subtype.comp R.subtype) =
      R.map H.subtype ⊓ centralizer (U : Set G) := by
    ext x
    constructor
    · rintro ⟨r,hr,rfl⟩
      exact ⟨mem_map_of_mem H.subtype r.property,(haC r).mp ((hαa r).mp hr)⟩
    · rintro ⟨⟨r,hr,rfl⟩,hc⟩
      exact ⟨⟨r,hr⟩,(hαa _).mpr ((haC _).mpr hc),rfl⟩
  rw [hker] at hm
  rw [←hm]
  change (pCore 2 R).map (H.subtype.comp R.subtype) =
    (pCore 2 (R.map H.subtype)).map (R.map H.subtype).subtype
  rw [← pCore_map_iso 2 er,map_map]
  rfl

end
end CFSG.Quasithin.Chapter8.Section02.HermitianSource
