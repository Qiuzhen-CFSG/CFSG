module
public import Theory.Representation.HermitianTensorThree.PointSection.Transvections
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointMovement

/-!
# The original point-core transvection pairing

The equivariant point marking identifies the literal commutator with the
native five-space. Its row map gives the actual quotient by the central
involution. Every binary functional on this quotient is induced by an element
of the original point core; the exact action is expressed by the ambient
group commutator, and its full kernel is retained. Conjugation invariance
of this pairing supplies the dual action for every simultaneous normalizer
fixing the central involution, including outer actors.

The same coordinates identify both the fixed line and the fixed space modulo
that line. The final theorem applies these calculations to O₂(C_L(z)^∞),
using its proved full point-radical image. The Chapter 12 tensor consumer
discharges every coordinate and image premise on the original chosen module.

Source: Aschbacher–Smith H.4.6(4,6) and the transvection calculation of
8.2.11(4), printed pp.382,722, refs/quasithin.pdf. Recognition of the natural
and A₅ sections, V ≤ O₂(L_z), and the remaining 8.2.12–13 argument are
separate obligations; no covering kernel or containment is suppressed here.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE
set_option backward.isDefEq.respectTransparency false
local instance : SMul (ZMod 2) (Space 1) := (binaryModule 1).toSMul
variable {G : Type*} [Group G]

/-- The commutator is the literal inverse image of the native five-space. -/
theorem marked_point_commutator_coordinates
    (V X : Subgroup G) [IsElementaryAbelian 2 V]
    (hXV : X ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1)
    (q : X →* (Space 1 ≃ₗ[ZMod 2] Space 1))
    (he : ∀ x v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hXV x)) v) = q x (e v))
    (hq : q.range = UnipotentRadicals.point 1) :
    ∀ v : Additive V, (v.toMul : G) ∈ ⁅V,X⁆ ↔ e v ∈ PointSection.moved := by
  let f := V.normalizerMonoidHom.rangeRestrict.comp (inclusion hXV)
  let ρ := (automizerRepresentation V).comp f
  let σ := UnipotentRadicals.ambientAction 1
  have hact (x : X) (v : V) :
      ρ x (Additive.ofMul v) = Additive.ofMul
        (⟨(x : G)*(v : G)*(x : G)⁻¹,le_normalizer_iff.mp hXV x x.property v v.property⟩ : V) := rfl
  have hcomm := commutator_image_eq ρ V V X hXV le_rfl (MonoidHom.id X)
    (MonoidHom.id V) (fun x v => hact x v) ⊤ (by
      ext v
      simp [binarySubgroup])
  have hC : (⁅V,X⁆).subgroupOf V = binarySubgroup (subspaceCommutator ρ ⊤ (⊤ : Subgroup X)) := by
    simpa only [map_id,(MonoidHom.id X).range_eq_top_of_surjective (fun x => ⟨x,rfl⟩)] using hcomm
  have he' (x : X) (w : Space 1) : ρ x (e.symm w) = e.symm (σ (q x) w) := by
    apply e.injective
    exact (he x (e.symm w)).trans (by simp only [e.apply_symm_apply]; rfl)
  have hm := subspaceCommutator_map_embedding ρ σ q e.symm.toLinearMap he'
    (⊤ : Subgroup X) (⊤ : Submodule (ZMod 2) (Space 1))
  have hM : subspaceCommutator ρ ⊤ (⊤ : Subgroup X) = PointSection.moved.map e.symm.toLinearMap := by
    dsimp only [σ] at hm
    simpa only [Submodule.map_top,LinearEquiv.range,←MonoidHom.range_eq_map,hq,
      PointSection.point_commutator] using hm
  intro v
  change v.toMul ∈ (⁅V,X⁆).subgroupOf V ↔ _
  rw [hC,hM]
  change v ∈ PointSection.moved.map e.symm.toLinearMap ↔ _
  constructor
  · rintro ⟨w,hw,rfl⟩
    simpa using hw
  · intro hv
    exact ⟨e v,hv,e.symm_apply_apply v⟩

/-- The original central involution gives exactly the native central line. -/
theorem marked_point_line
    (V : Subgroup G) [IsElementaryAbelian 2 V]
    (e : Additive V ≃ₗ[ZMod 2] Space 1) (z : V)
    (hz : e (Additive.ofMul z) = PointSection.pointVector) (v : Additive V) :
    e v ∈ PointSection.line ↔ (v.toMul : G) ∈ zpowers (z : G) := by
  rw [PointSection.mem_line_iff]
  constructor
  · rintro (hv|hv)
    · have hv0 : v=0 := e.injective (hv.trans (map_zero e).symm)
      rw [hv0]
      exact one_mem _
    · have hvz : v=Additive.ofMul z := e.injective (hv.trans hz.symm)
      rw [hvz]
      exact mem_zpowers _
  · intro hv
    have hpow : (z : G)^2=1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ z.property
    obtain ⟨k,hk⟩ := mem_zpowers_iff.mp hv
    have hh := zpow_eq_zpow_emod' k hpow
    norm_num only [Nat.cast_ofNat] at hh
    have hb : k%2=0 ∨ k%2=1 := by omega
    rcases hb with hb|hb
    · left
      have hv1 : v=0 := by
        apply Additive.toMul.injective
        apply Subtype.ext
        change (v.toMul : G)=1
        rw [←hk,hh,hb,zpow_zero]
      rw [hv1,map_zero]
    · right
      have hvz : v=Additive.ofMul z := by
        apply Additive.toMul.injective
        apply Subtype.ext
        change (v.toMul : G)=(z : G)
        rw [←hk,hh,hb,zpow_one]
      rw [hvz,hz]

/-- Coordinates on the actual quotient and a full dual action of the original
radical. The kernel is kept as the actual centralizer in the original group. -/
@[expose] def FullPointTransvectionAction (V X : Subgroup G) (z : G) : Prop :=
  ∃ qW : (⁅V,X⁆ : Subgroup G) →* Multiplicative (Fin 2 → E 1),
    Function.Surjective qW ∧ qW.ker = (zpowers z).subgroupOf ⁅V,X⁆ ∧
    ∃ qX : X →* Multiplicative (Module.Dual (ZMod 2) (Fin 2 → E 1)),
      Function.Surjective qX ∧ qX.ker = (centralizer (V : Set G)).subgroupOf X ∧
      ∀ (x : X) (w : (⁅V,X⁆ : Subgroup G)),
        ⁅(x : G),(w : G)⁆ = z ^ ((qX x).toAdd (qW w).toAdd).val

/-- Marked point coordinates construct the complete transvection group on
the literal commutator, including its quotient and full original kernel. -/
theorem marked_point_transvections
    (V X : Subgroup G) [IsElementaryAbelian 2 V]
    (hXV : X ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1)
    (q : X →* (Space 1 ≃ₗ[ZMod 2] Space 1))
    (he : ∀ x v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hXV x)) v) = q x (e v))
    (hq : q.range = UnipotentRadicals.point 1)
    (z : V) (hz : e (Additive.ofMul z) = PointSection.pointVector) :
    FullPointTransvectionAction V X z := by
  let W := ⁅V,X⁆
  have hWV : W ≤ V := le_normalizer_iff_commutator_le_left.mp hXV
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWV
  have hW := marked_point_commutator_coordinates V X hXV e q he hq
  let p : Additive W →ₗ[ZMod 2] PointSection.moved :=
    (e.toLinearMap.comp ((inclusion hWV).toAdditive.toZModLinearMap 2)).codRestrict
      PointSection.moved (fun w => (hW _).mp w.toMul.property)
  have hp : Function.Surjective p := by
    intro Y
    let v := e.symm Y.val
    have hv : (v.toMul : G) ∈ W := (hW v).mpr (by rw [e.apply_symm_apply]; exact Y.property)
    refine ⟨Additive.ofMul ⟨v.toMul,hv⟩,?_⟩
    apply Subtype.ext
    exact e.apply_symm_apply Y.val
  let qW : W →* Multiplicative (Fin 2 → E 1) :=
    (PointSection.row.comp p).toAddMonoidHom.toMultiplicative
  have hqW : Function.Surjective qW := PointSection.row_surjective.comp hp
  have hline := marked_point_line V e z hz
  have hqWker : qW.ker=(zpowers (z : G)).subgroupOf W := by
    ext w
    change PointSection.row (p (Additive.ofMul w))=0 ↔ (w : G) ∈ zpowers (z : G)
    rw [PointSection.row_kernel]
    exact hline _
  let qP : X →* UnipotentRadicals.point 1 := q.codRestrict _
    (fun x => hq ▸ (show q x ∈ q.range from ⟨x,rfl⟩))
  have hqP : Function.Surjective qP := by
    intro t
    have ht : t.val ∈ q.range := hq.symm ▸ t.property
    obtain ⟨x,hx⟩ := ht
    exact ⟨x,Subtype.ext hx⟩
  let qX := PointSection.pointDualEquiv.toMonoidHom.comp qP
  have hqX : Function.Surjective qX := PointSection.pointDualEquiv.surjective.comp hqP
  have hqXker : qX.ker = (centralizer (V : Set G)).subgroupOf X := by
    ext x
    change PointSection.pointDualEquiv (qP x)=1 ↔ (x : G) ∈ centralizer (V : Set G)
    rw [map_eq_one_iff _ PointSection.pointDualEquiv.injective]
    rw [Subtype.ext_iff]
    change q x=1 ↔ _
    constructor
    · intro hx v hv
      have hh := he x (Additive.ofMul ⟨v,hv⟩)
      rw [hx] at hh
      have hh := e.injective hh
      have hh := congrArg (fun a : Additive V => (a.toMul : G)) hh
      change (x : G)*v*(x : G)⁻¹=v at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hx
      apply LinearEquiv.ext
      intro Y
      obtain ⟨v,rfl⟩ := e.surjective Y
      rw [←he]
      apply congrArg e
      apply Additive.toMul.injective
      apply Subtype.ext
      change (x : G)*(v.toMul : G)*(x : G)⁻¹=(v.toMul : G)
      rw [←hx _ v.toMul.property,mul_inv_cancel_right]
  refine ⟨qW,hqW,hqWker,qX,hqX,hqXker,?_⟩
  intro x w
  let v : V := inclusion hWV w
  let a := ((qX x).toAdd (qW w).toAdd)
  have ha := PointSection.pointDualEquiv_action (qP x) (p (Additive.ofMul w))
  have hc : ⁅(x : G),(w : G)⁆ ∈ V := by
    exact V.mul_mem (le_normalizer_iff.mp hXV x x.property w (hWV w.property))
      (V.inv_mem (hWV w.property))
  have hdisp : e (Additive.ofMul (⟨⁅(x : G),(w : G)⁆,hc⟩ : V)) = a • PointSection.pointVector := by
    have hh := he x (Additive.ofMul v)
    have hv : Additive.ofMul (⟨⁅(x : G),(w : G)⁆,hc⟩ : V) =
        automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict (inclusion hXV x))
          (Additive.ofMul v) - Additive.ofMul v := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change ⁅(x : G),(w : G)⁆ = ((x : G)*(w : G)*(x : G)⁻¹)/(w : G)
      simp only [commutatorElement_def,div_eq_mul_inv,mul_assoc]
    rw [hv,map_sub,hh]
    exact (sub_eq_iff_eq_add.mpr (ha.trans (add_comm _ _)))
  have hzpow (b : ZMod 2) : e (Additive.ofMul (⟨(z : G)^b.val,V.pow_mem z.property _⟩ : V)) =
      b • PointSection.pointVector := by
    fin_cases b
    · simp
    · change e (Additive.ofMul (⟨(z : G)^1,_⟩ : V)) = (1 : ZMod 2) • PointSection.pointVector
      simpa only [pow_one,one_smul] using hz
  exact congrArg (fun b : Additive V => (b.toMul : G)) (e.injective (hdisp.trans (hzpow a).symm))

/-- The fixed space modulo the original central involution is exactly the
original point-core commutator. This is H.4.6(6) on the actual action. -/
theorem marked_point_second_fixed
    (V X : Subgroup G) [IsElementaryAbelian 2 V]
    (hXV : X ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1)
    (q : X →* (Space 1 ≃ₗ[ZMod 2] Space 1))
    (he : ∀ x v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hXV x)) v) = q x (e v))
    (hq : q.range = UnipotentRadicals.point 1)
    (z : V) (hz : e (Additive.ofMul z) = PointSection.pointVector) (v : V) :
    (∀ x : X, ⁅(x : G),(v : G)⁆ ∈ zpowers (z : G)) ↔ (v : G) ∈ ⁅V,X⁆ := by
  have hc (x : X) : ⁅(x : G),(v : G)⁆ ∈ V :=
    V.mul_mem (le_normalizer_iff.mp hXV x x.property v v.property) (V.inv_mem v.property)
  have hec (x : X) : e (Additive.ofMul (⟨⁅(x : G),(v : G)⁆,hc x⟩ : V)) =
      q x (e (Additive.ofMul v))-e (Additive.ofMul v) := by
    rw [←he,←map_sub]
    apply congrArg e
    apply Additive.toMul.injective
    apply Subtype.ext
    change ⁅(x : G),(v : G)⁆ = ((x : G)*(v : G)*(x : G)⁻¹)/(v : G)
    simp only [commutatorElement_def,div_eq_mul_inv,mul_assoc]
  have hl (x : X) : ⁅(x : G),(v : G)⁆ ∈ zpowers (z : G) ↔
      q x (e (Additive.ofMul v))-e (Additive.ofMul v) ∈ PointSection.line := by
    rw [←hec]
    exact (marked_point_line V e z hz (Additive.ofMul (⟨⁅(x : G),(v : G)⁆,hc x⟩ : V))).symm
  refine Iff.trans ?_ (marked_point_commutator_coordinates V X hXV e q he hq (Additive.ofMul v)).symm
  rw [←PointSection.displacement_mem_line_iff]
  constructor
  · intro h t ht
    obtain ⟨x,rfl⟩ := hq.symm ▸ ht
    exact (hl x).mp (h x)
  · intro h x
    exact (hl x).mpr (h _ (hq ▸ (show q x ∈ q.range from ⟨x,rfl⟩)))

/-- The whole point radical fixes precisely the original central line. -/
theorem marked_point_fixed
    (V X : Subgroup G) [IsElementaryAbelian 2 V]
    (hXV : X ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1)
    (q : X →* (Space 1 ≃ₗ[ZMod 2] Space 1))
    (he : ∀ x v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hXV x)) v) = q x (e v))
    (hq : q.range = UnipotentRadicals.point 1)
    (z : V) (hz : e (Additive.ofMul z) = PointSection.pointVector) :
    V ⊓ centralizer (X : Set G) = zpowers (z : G) := by
  have hfix (v : V) : (v : G) ∈ centralizer (X : Set G) ↔
      e (Additive.ofMul v) ∈ PointSection.line := by
    rw [←PointSection.point_fixed_eq_line]
    constructor
    · intro hv t
      have ht : t.val ∈ q.range := by rw [hq]; exact t.property
      obtain ⟨x,hx⟩ := ht
      change t.val (e (Additive.ofMul v))=e (Additive.ofMul v)
      rw [←hx,←he]
      apply congrArg e
      apply Additive.toMul.injective
      apply Subtype.ext
      change (x : G)*(v : G)*(x : G)⁻¹=(v : G)
      rw [hv x x.property,mul_inv_cancel_right]
    · intro hv x hx
      have hh := hv ⟨q ⟨x,hx⟩,hq ▸ (show q ⟨x,hx⟩ ∈ q.range from ⟨⟨x,hx⟩,rfl⟩)⟩
      change q ⟨x,hx⟩ (e (Additive.ofMul v))=e (Additive.ofMul v) at hh
      rw [←he] at hh
      have hh := congrArg (fun a : Additive V => (a.toMul : G)) (e.injective hh)
      change x*(v : G)*x⁻¹=(v : G) at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
  ext v
  constructor
  · rintro ⟨hv,hc⟩
    exact (marked_point_line V e z hz _).mp ((hfix ⟨v,hv⟩).mp hc)
  · intro hv
    have hVv : v ∈ V := (zpowers_le.mpr z.property) hv
    exact ⟨hVv,(hfix ⟨v,hVv⟩).mpr ((marked_point_line V e z hz _).mpr hv)⟩


/-- The literal commutator pairing is invariant under every simultaneous
conjugation fixing z. Thus the normalizer acts on the radical image as the
dual of its action on the actual row quotient, including outer actors. -/
theorem point_transvection_pairing_covariant
    (V X : Subgroup G) (z : G) (hz : z ≠ 1)
    (qW : (⁅V,X⁆ : Subgroup G) →* Multiplicative (Fin 2 → E 1))
    (qX : X →* Multiplicative (Module.Dual (ZMod 2) (Fin 2 → E 1)))
    (hpair : ∀ (x : X) (w : (⁅V,X⁆ : Subgroup G)),
      ⁅(x : G),(w : G)⁆ = z ^ ((qX x).toAdd (qW w).toAdd).val)
    (g : G) (hg : Commute g z) (x y : X) (v w : (⁅V,X⁆ : Subgroup G))
    (hxy : (y : G)=g*(x : G)*g⁻¹) (hvw : (w : G)=g*(v : G)*g⁻¹) :
    (qX y).toAdd (qW w).toAdd = (qX x).toAdd (qW v).toAdd := by
  have hgZ : MulAut.conj g z = z := by
    change g*z*g⁻¹=z
    rw [hg.eq,mul_inv_cancel_right]
  have hp : z^((qX y).toAdd (qW w).toAdd).val = z^((qX x).toAdd (qW v).toAdd).val := by
    calc
      _ = ⁅(y : G),(w : G)⁆ := (hpair y w).symm
      _ = MulAut.conj g ⁅(x : G),(v : G)⁆ := by
        rw [map_commutatorElement]
        exact congrArg₂ (fun a b : G => ⁅a,b⁆) hxy hvw
      _ = MulAut.conj g (z^((qX x).toAdd (qW v).toAdd).val) := congrArg _ (hpair x v)
      _ = _ := by rw [map_pow,hgZ]
  have hi : Function.Injective (fun a : ZMod 2 => z^a.val) := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact False.elim (hz (by simpa [ZMod.val_one_eq_one_mod] using hab.symm))
    · exact False.elim (hz (by simpa [ZMod.val_one_eq_one_mod] using hab))
    · rfl
  exact hi hp

/-- First-isomorphism equivalences for both members of the full pairing.
The radical denominator is its complete original centralizer. -/
theorem FullPointTransvectionAction.quotient_equivalences
    (V X : Subgroup G) (z : G) (h : FullPointTransvectionAction V X z) :
    ∃ hZ : ((zpowers z).subgroupOf ⁅V,X⁆).Normal,
      ∃ hC : ((centralizer (V : Set G)).subgroupOf X).Normal,
        let := hZ
        let := hC
        Nonempty (((⁅V,X⁆ : Subgroup G) ⧸ (zpowers z).subgroupOf ⁅V,X⁆) ≃*
          Multiplicative (Fin 2 → E 1)) ∧
        Nonempty ((X ⧸ (centralizer (V : Set G)).subgroupOf X) ≃*
          Multiplicative (Module.Dual (ZMod 2) (Fin 2 → E 1))) := by
  obtain ⟨qW,hW,hWker,qX,hX,hXker,_⟩ := h
  have hZ : ((zpowers z).subgroupOf ⁅V,X⁆).Normal := hWker ▸ qW.normal_ker
  have hC : ((centralizer (V : Set G)).subgroupOf X).Normal := hXker ▸ qX.normal_ker
  let := hZ
  let := hC
  exact ⟨hZ,hC,⟨(QuotientGroup.quotientMulEquivOfEq hWker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective qW hW)⟩,
    ⟨(QuotientGroup.quotientMulEquivOfEq hXker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective qX hX)⟩⟩

variable [Finite G]
/-- The original residual core acts as the entire transvection group, and
its fixed space modulo Z is the original commutator five-space. -/
theorem marked_point_residual_transvections
    (V L : Subgroup G) [IsElementaryAbelian 2 V]
    (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1) (q : L →* binaryImage 1)
    (he : ∀ (l : L) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v) = (q l).val (e v))
    (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (z : V) (hz : e (Additive.ofMul z) = PointSection.pointVector) :
    FullPointTransvectionAction V (Centralizer.localTwoCore L z) z ∧
      V ⊓ centralizer (Centralizer.localTwoCore L z : Set G) = zpowers (z : G) ∧
      ∀ v : V, (∀ x : Centralizer.localTwoCore L z,
        ⁅(x : G),(v : G)⁆ ∈ zpowers (z : G)) ↔ v.val ∈ Centralizer.commutatorSpace L V z := by
  let f := nativeBinaryEquiv.symm.toMonoidHom.comp q
  have hf : Function.Surjective f := nativeBinaryEquiv.symm.surjective.comp hq
  have hfk : IsPGroup 2 f.ker := by
    rwa [MonoidHom.ker_comp_of_injective _ _ nativeBinaryEquiv.symm.injective]
  have hP := marked_point_centralizer_preimage V L hLN e q he z hz
  have hXimage := (point_residual_images L (z : G) f hf hfk hP).2
  let X := Centralizer.localTwoCore L z
  have hXL : X ≤ L := (Centralizer.localTwoCore_le L z).trans
    ((Centralizer.localResidual_le L z).trans inf_le_left)
  let r := (binaryImage 1).subtype.comp (q.comp (inclusion hXL))
  have hRange : r.range = UnipotentRadicals.point 1 := by
    have hm := congrArg (Subgroup.map ((binaryImage 1).subtype.comp nativeBinaryEquiv.toMonoidHom)) hXimage
    rw [map_map,native_point_root_image] at hm
    have heq : ((binaryImage 1).subtype.comp nativeBinaryEquiv.toMonoidHom).comp f =
        (binaryImage 1).subtype.comp q := by
      apply MonoidHom.ext
      intro l
      exact congrArg Subtype.val (nativeBinaryEquiv.apply_symm_apply (q l))
    rw [heq] at hm
    have hi : (inclusion hXL).range = X.subgroupOf L := by
      ext l
      constructor
      · rintro ⟨x,rfl⟩
        exact x.property
      · intro hl
        exact ⟨⟨l,hl⟩,Subtype.ext rfl⟩
    change (((binaryImage 1).subtype.comp q).comp (inclusion hXL)).range = _
    rw [MonoidHom.range_comp,hi]
    exact hm
  exact ⟨marked_point_transvections V X (hXL.trans hLN) e r
      (fun x v => he (inclusion hXL x) v) hRange z hz,
    marked_point_fixed V X (hXL.trans hLN) e r
      (fun x v => he (inclusion hXL x) v) hRange z hz,
    marked_point_second_fixed V X (hXL.trans hLN) e r
      (fun x v => he (inclusion hXL x) v) hRange z hz⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
