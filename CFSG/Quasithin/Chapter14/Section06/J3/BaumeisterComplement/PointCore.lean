module
public import CFSG.Quasithin.Chapter14.Section06.J3.BaumeisterComplement.Pair
public import Theory.SpecificGroups.MinusExtraspecial.InvolutionCentralizerGeometry

/-!
# The point centralizer meets Q_f exactly in the central involution

In A₄ × C₂ the cubic conjugates any noncentral involution to a distinct
commuting involution outside its span with the center. In a minus-extraspecial
group of order thirty-two, the square-one elements commuting with a fixed
noncentral involution are precisely that four-group. Normality of the core
therefore forces the intersection to be the common central involution.

Ambient involution fusion transports the actual two-core to the checked
minus-extraspecial model. Applying the intersection theorem to the original
field-image centralizer proves C_{L₁}(f) ∩ O₂(C_G(f)) = ⟨f⟩. No A₅
complement or splitting of C_G(f) is assumed.

Source: Baumeister, *A geometry for groups of J₃-type* (2007),
Lemma 2.6, p.496, the elementary-order-eight exclusion. The complement
alignment and identification of the full generated L₃ remain separate.
-/

open Subgroup
namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
public noncomputable section
local notation "W" => alternatingGroup (Fin 4) × Multiplicative (ZMod 2)
private def fourCubic : alternatingGroup (Fin 4) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
    simp [Equiv.Perm.mem_alternatingGroup]⟩
private def fourCenter : W := (1,Multiplicative.ofAdd 1)
private def fourConjugate (x : W) : W :=
  (fourCubic,1) * x * (fourCubic,1)⁻¹
private theorem four_center_unique : ∀ z : W, z ∈ center W → z ≠ 1 → z=fourCenter := by
  decide +kernel
private theorem four_two_power : ∀ x : W, x^32=1 → x^2=1 := by decide +kernel
private instance fourDecidableEq : DecidableEq W := inferInstance

private theorem four_noncentral_conjugate : ∀ x : W, x^2=1 → x≠1 → x≠fourCenter →
    Commute (fourConjugate x) x ∧
      fourConjugate x ≠ 1 ∧ fourConjugate x ≠ fourCenter ∧
      fourConjugate x ≠ x ∧ fourConjugate x ≠ fourCenter*x := by
  intro x hx hx1 hxz
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change fourConjugate x * x = x * fourConjugate x
    revert x
    decide +kernel
  · revert x
    decide +kernel
  · revert x
    decide +kernel
  · revert x
    decide +kernel
  · revert x
    decide +kernel

/-- The A₄ × C₂ centralizer meets a normal minus-extraspecial core only
in the specified common central involution. This is the core-intersection
step in Baumeister 2.6, without any complement assumption. -/
theorem alternatingFour_core_intersection {H : Type*} [Group H] [Finite H]
    (Q X : Subgroup H) [Q.Normal] (eQ : Q ≃* MinusExtraspecial.Model)
    (eX : X ≃* W) (z : H) (hzQ : z ∈ Q) (hzX : z ∈ X) (hz1 : z ≠ 1)
    (hzC : z ∈ center H) : X ⊓ Q = zpowers z := by
  have hzXc : (⟨z,hzX⟩ : X) ∈ center X :=
    mem_center_iff.mpr (fun x => Subtype.ext (mem_center_iff.mp hzC x))
  have hzQc : (⟨z,hzQ⟩ : Q) ∈ center Q :=
    mem_center_iff.mpr (fun x => Subtype.ext (mem_center_iff.mp hzC x))
  have hez : eX ⟨z,hzX⟩ = fourCenter := by
    apply four_center_unique
    · apply mem_center_iff.mpr
      intro x
      obtain ⟨x,rfl⟩ := eX.surjective x
      rw [← map_mul,← map_mul]
      exact congrArg eX (mem_center_iff.mp hzXc x)
    · intro hh
      exact hz1 (congrArg Subtype.val (eX.injective (hh.trans eX.map_one.symm)))
  apply le_antisymm
  · intro x hx
    by_cases hx1 : x=1
    · exact hx1 ▸ (zpowers z).one_mem
    by_cases hxz : x=z
    · exact hxz ▸ mem_zpowers z
    let xX : X := ⟨x,hx.1⟩
    let xQ : Q := ⟨x,hx.2⟩
    have hx32 : x^32=1 := by
      have hd := Q.orderOf_dvd_natCard hx.2
      rw [Nat.card_congr eQ.toEquiv,MinusExtraspecial.card_model] at hd
      exact orderOf_dvd_iff_pow_eq_one.mp hd
    have hxX2 : (eX xX)^2=1 := four_two_power _ (by
      rw [← map_pow,eX.map_eq_one_iff]
      exact Subtype.ext hx32)
    have hx2X : xX^2=1 := eX.injective (by
      rw [map_pow,map_one]
      exact hxX2)
    have hx2 : x^2=1 := congrArg Subtype.val hx2X
    have hxne : eX xX ≠ 1 := fun hh => hx1
      (congrArg Subtype.val (eX.injective (hh.trans eX.map_one.symm)))
    have hxnez : eX xX ≠ fourCenter := fun hh => hxz
      (congrArg Subtype.val (eX.injective (hh.trans hez.symm)))
    obtain ⟨hcomm,hy1,hyz,hyx,hyzx⟩ := four_noncentral_conjugate _ hxX2 hxne hxnez
    let c : X := eX.symm (fourCubic,1)
    let y : H := c * x * (c : H)⁻¹
    have hyQ : y ∈ Q := Subgroup.Normal.conj_mem (inferInstance : Q.Normal) x hx.2 c
    have hyX : y ∈ X := X.mul_mem (X.mul_mem c.property hx.1) (X.inv_mem c.property)
    have hey : eX ⟨y,hyX⟩ = fourConjugate (eX xX) := by
      change eX (c*xX*c⁻¹) = _
      simp only [map_mul,map_inv,c,eX.apply_symm_apply,fourConjugate]
    have hy2 : y^2=1 := by
      change (MulAut.conj (c : H)) x ^ 2 = 1
      rw [← map_pow,hx2,map_one]
    have hycomm : y*x=x*y := by
      have he : (⟨y,hyX⟩ : X)*xX = xX*⟨y,hyX⟩ := by
        apply eX.injective
        rw [map_mul,map_mul,hey]
        exact hcomm.eq
      exact congrArg (fun x : X => (x : H)) he
    have hh := MinusExtraspecial.commuting_square_one_of_equiv eQ hzQc
      (fun hh => hz1 (congrArg Subtype.val hh))
      (u := xQ) (x := (⟨y,hyQ⟩ : Q)) (Subtype.ext hx2)
      (fun hh => hx1 (congrArg Subtype.val hh))
      (fun hh => hxz (congrArg Subtype.val hh)) (Subtype.ext hycomm) (Subtype.ext hy2)
    rcases hh with hh | hh | hh | hh
    · have he : (⟨y,hyX⟩ : X)=1 := Subtype.ext (congrArg (fun q : Q => (q : H)) hh)
      exact (hy1 (by rw [← hey,he,map_one])).elim
    · have he : (⟨y,hyX⟩ : X)=⟨z,hzX⟩ := Subtype.ext (congrArg (fun q : Q => (q : H)) hh)
      exact (hyz (by rw [← hey,he,hez])).elim
    · have he : (⟨y,hyX⟩ : X)=xX := Subtype.ext (congrArg (fun q : Q => (q : H)) hh)
      exact (hyx (by rw [← hey,he])).elim
    · have he : (⟨y,hyX⟩ : X)=⟨z,hzX⟩*xX := Subtype.ext (congrArg (fun q : Q => (q : H)) hh)
      exact (hyzx (by rw [← hey,he,map_mul,hez])).elim
  · exact zpowers_le.mpr ⟨hzX,hzQ⟩
/-- Fusion transports the actual involution-centralizer two-core to the
minus-extraspecial model; this does not assert a splitting of the centralizer. -/
theorem involution_twoCore_model {G : Type*} [Group G] [Finite G]
    {z : G} (h : HTypeAt z) (hc : OneInvolutionClass G) (f : G) (hf : orderOf f=2) :
    Nonempty (pCore 2 (involutionCentralizer f) ≃* MinusExtraspecial.Model) := by
  obtain ⟨a,_,ha⟩ := hc
  obtain ⟨g,hg⟩ := isConj_iff.mp ((ha f hf).trans (ha z h.involution).symm)
  let c := MulAut.conj g
  have hcz : c f = z := hg
  let e : involutionCentralizer f ≃* involutionCentralizer z :=
    (Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv c f).trans
      (MulEquiv.subgroupCongr (by rw [hcz]))
  exact ⟨((pCore 2 (involutionCentralizer f)).equivMapOfInjective e.toMonoidHom e.injective).trans
    ((MulEquiv.subgroupCongr (pCore_map_iso 2 e)).trans
      ((MulEquiv.subgroupCongr h.core_eq_pCore.symm).trans h.core_equiv.some))⟩

/-- The first centralizer's intersection with Q_f = O₂(C_G(f)) is exactly
⟨f⟩, on the literal field-image subgroups used to define the third parabolic. -/
theorem field_point_centralizer_core {G : Type*} [Group G] [Finite G]
    {z : G} (h : HTypeAt z) (hc : OneInvolutionClass G)
    (j : Sporadic.Janko3.SourceRecognition.SingerField.Model →* G)
    (hj : Function.Injective j) :
    let f := j Sporadic.Janko3.SourceRecognition.SingerField.fieldElement
    let C := involutionCentralizer f
    (j.range ⊓ centralizer ({f} : Set G)) ⊓ (pCore 2 C).map C.subtype = zpowers f := by
  classical
  dsimp only
  let f := j Sporadic.Janko3.SourceRecognition.SingerField.fieldElement
  let C := involutionCentralizer f
  let X := j.range ⊓ centralizer ({f} : Set G)
  have hXC : X ≤ C := inf_le_right
  have hf : orderOf f=2 := Sporadic.Janko3.SourceRecognition.BaumeisterParabolics.image_involution_order j hj
  let fC : C := ⟨f,mem_centralizer_singleton_iff.mpr rfl⟩
  have hfC : fC ∈ center C := mem_center_iff.mpr (fun x => Subtype.ext
    (mem_centralizer_singleton_iff.mp x.property))
  have hfX : f ∈ X := ⟨⟨_,rfl⟩,mem_centralizer_singleton_iff.mpr rfl⟩
  have hfQ : fC ∈ pCore 2 C := by
    have hn : (zpowers fC).Normal := by
      constructor
      intro x hx g
      have hh := (zpowers_le.mpr hfC) hx
      rw [mem_center_iff.mp hh g,mul_inv_cancel_right]
      exact hx
    have hp : IsPGroup 2 (zpowers fC) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers,← orderOf_coe fC,hf]; rfl)
    exact (show zpowers fC ≤ pCore 2 C from le_sSup ⟨hn,hp⟩) (mem_zpowers fC)
  obtain ⟨eQ⟩ := involution_twoCore_model h hc f hf
  let eX : X.subgroupOf C ≃* W := (subgroupOfEquivOfLe hXC).trans
    (Sporadic.Janko3.SourceRecognition.BaumeisterParabolics.PointCentralizer.imagePointCentralizerEquiv j hj)
  have he := alternatingFour_core_intersection (pCore 2 C) (X.subgroupOf C) eQ eX
    fC hfQ hfX (by intro hh; have hh' : f=1 := congrArg Subtype.val hh; simp [hh'] at hf) hfC
  have hemap := congrArg (Subgroup.map C.subtype) he
  rw [map_inf _ _ _ C.subtype_injective,map_subgroupOf_eq_of_le hXC,MonoidHom.map_zpowers] at hemap
  exact hemap

end
end CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
