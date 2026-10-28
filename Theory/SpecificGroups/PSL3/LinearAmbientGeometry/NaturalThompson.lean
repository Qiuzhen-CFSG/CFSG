module
public import Theory.SpecificGroups.SL2.Affine.Core
public import Theory.Representation.SL2NaturalOffenders
public import Theory.Representation.SL2NaturalOffenders.OddDegree
public import Theory.Representation.SL2NaturalOffenders.PointwiseFixer
public import Theory.GroupTheory.SylowImageIntersection
public import Theory.GroupAction.Defs
public import Stellmacher.CentralizerQuotientRepresentation
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.ElementaryAbelian.Injective
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Sylow control in affine normal extensions

Let X be a normal affine plane group over a nonbinary even field, with its
translation plane self-centralizing in the ambient group. Conjugation gives a
faithful binary representation of the quotient by that plane. The affine
coordinates identify the image of X with the natural SL₂ layer. The maximum
elementary subgroup inequality makes every nontrivial image an offender, so
B.4.2 puts it in that same layer. Taking its full preimage puts the original
elementary subgroup in X. A Sylow element fixing the center of its affine
intersection fixes the natural fixed line pointwise. Semilinearity then
makes its field coefficient trivial, and its two-power order forces
determinant one; hence it too lies in X. Over an odd-degree field every
ambient two-element has trivial field coefficient, so the whole ambient
Sylow subgroup lies in X.

The source application takes the full normalizer of one PSL₃ local factor as
the ambient group. This proves the containment needed for A(T) = {V₁,V₂}
and C_T(Z(S)) = S. It does not assume that the source normalizers embed in
Aut(PSL₃).
Source: Aschbacher–Smith B.4.2(1), printed p.86, and 5.3.5–6, printed p.660
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Matrix
open scoped MatrixGroups IsMulCommutative
namespace Matrix.PSL3.LinearAmbientGeometry
variable {G : Type*} [Group G] [Finite G]
  {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2

private def coreCoordinates {X : Type*} [Group X] (e : X ≃* SL2.Affine F) :
    Multiplicative (Fin 2 → F) ≃* pCore 2 X :=
  (SL2.translationsEquiv F).trans ((e.symm.subgroupMap (SL2.translations F)).trans
    (MulEquiv.subgroupCongr (by rw [← SL2.affine_twoCore_eq F]; exact pCore_map_iso 2 e.symm)))

private theorem coreCoordinates_apply {X : Type*} [Group X] (e : X ≃* SL2.Affine F)
    (v : Multiplicative (Fin 2 → F)) :
    e (coreCoordinates e v : X) = SemidirectProduct.inl v := by
  change e (e.symm _) = _
  simp

private theorem coreCoordinates_conj {X : Type*} [Group X] (e : X ≃* SL2.Affine F)
    (x : X) (v : Multiplicative (Fin 2 → F)) :
    (coreCoordinates e (SL2.naturalAction F (e x).right v) : X) =
      x * (coreCoordinates e v : X) * x⁻¹ := by
  apply e.injective
  simp only [map_mul,map_inv,coreCoordinates_apply,SL2.conjugate_inl]

private theorem affine_extension_control
    (X : Subgroup G) [X.Normal] (e : X ≃* SL2.Affine F)
    (hF : 2 < Nat.card F)
    (hC : centralizer (X.pCoreIn 2 : Set G) = X.pCoreIn 2)
    : (∀ (S A : Subgroup G), X.pCoreIn 2 ≤ S →
        A ∈ elementaryAbelianMaxSubgroups S → A ≤ X) ∧
      (∀ P : Sylow 2 G,
        (P : Subgroup G) ⊓ centralizer (centerIn ((P : Subgroup G) ⊓ X) : Set G) ≤ X) ∧
      ∀ {n : ℕ}, Odd n → Nat.card F = 2 ^ n → ∀ P : Sylow 2 G, (P : Subgroup G) ≤ X := by
  let V := X.pCoreIn 2
  let a : Multiplicative (Fin 2 → F) ≃* V := (coreCoordinates e).trans
    ((pCore 2 X).equivMapOfInjective X.subtype X.subtype_injective)
  let : V.Normal := inferInstanceAs ((pCore 2 X).map X.subtype).Normal
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_injective a.symm.toMonoidHom a.symm.injective
  let q := QuotientGroup.mk' V
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective V
  have hk : q.ker = centralizer (V : Set G) := (QuotientGroup.ker_mk' V).trans hC.symm
  let α := NormalElementaryQuotient.representation V q hq hk
  let fa : Additive V ≃+ (Fin 2 → F) := {
    toFun v := (a.symm v.toMul).toAdd
    invFun v := Additive.ofMul (a (Multiplicative.ofAdd v))
    left_inv v := a.apply_symm_apply v.toMul
    right_inv v := a.symm_apply_apply (Multiplicative.ofAdd v)
    map_add' v w := congrArg Multiplicative.toAdd (map_mul a.symm v.toMul w.toMul) }
  let f : Additive V ≃ₗ[ZMod 2] (Fin 2 → F) :=
    { fa with map_smul' := ZMod.map_smul fa }
  let τ : Representation (ZMod 2) (G ⧸ V) (Fin 2 → F) :=
    f.conjRingEquiv.toMonoidHom.comp α
  have hf : Function.Injective τ := f.conjRingEquiv.injective.comp
    (NormalElementaryQuotient.representation_injective V q hq hk)
  have htrans (g : G ⧸ V) (v : Additive V) : f (α g v) = τ g (f v) := by
    change f (α g v) = f (α g (f.symm (f v)))
    rw [f.symm_apply_apply]
  let L := X.map q
  let : L.Normal := inferInstance
  have hker : (q.subgroupMap X).ker = pCore 2 X := by
    ext x
    change q.subgroupMap X x = 1 ↔ x ∈ pCore 2 X
    rw [Subtype.ext_iff]
    change q (x : G) = 1 ↔ x ∈ pCore 2 X
    rw [← MonoidHom.mem_ker,QuotientGroup.ker_mk']
    exact Subgroup.mem_map_iff_mem X.subtype_injective
  let b : (X ⧸ pCore 2 X) ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap X) (q.subgroupMap_surjective X))
  let c : L ≃* SL(2,F) := b.symm.trans
    ((QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans (SL2.affineCoreQuotientEquiv F))
  have hc (x : X) : c (q.subgroupMap X x) = (e x).right := by
    have hb : b (QuotientGroup.mk' (pCore 2 X) x) = q.subgroupMap X x := rfl
    change SL2.affineCoreQuotientEquiv F
      ((QuotientGroup.congr _ _ e (pCore_map_iso 2 e)) (b.symm (q.subgroupMap X x))) = _
    rw [← hb,b.symm_apply_apply]
    rfl
  have hn : ∀ (g : L) (v : Fin 2 → F), τ (g : G ⧸ V) v = Matrix.mulVec (c g).val v := by
    intro g v
    obtain ⟨x,rfl⟩ := q.subgroupMap_surjective X g
    rw [hc]
    let w : Additive V := Additive.ofMul (a (Multiplicative.ofAdd v))
    have hw : f w = v := a.symm_apply_apply _
    rw [← hw,← htrans]
    change (a.symm (α (q (x : G)) w).toMul).toAdd = _
    change a.symm (α (q (x : G)) w).toMul =
      SL2.naturalAction F (e x).right (a.symm w.toMul)
    apply a.injective
    rw [a.apply_symm_apply,show a.symm w.toMul = Multiplicative.ofAdd v from a.symm_apply_apply _]
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply]
    exact (congrArg X.subtype (coreCoordinates_conj e x (Multiplicative.ofAdd v))).symm
  refine ⟨?_,?_,?_⟩
  · intro S A hVS hA
    have hAL : A.map q ≤ L := by
      by_cases hzero : A ≤ q.ker
      · rw [(Subgroup.map_eq_bot_iff A).mpr hzero]
        exact bot_le
      · have hOff := NormalElementaryQuotient.maxElementary_isOffender V q hq hk S A hVS hA hzero
        have hOffτ : IsOffender τ (A.map q) := by
          have hh := hOff.map_equivariant α τ (MonoidHom.id _) Function.injective_id f htrans
          simpa only [Subgroup.map_id] using hh
        obtain ⟨P,hP⟩ := SL2NaturalOffenders.exists_sylow hF L c τ hf hn hOffτ
        exact hP ▸ map_subtype_le _
    have hcq : (X.map q).comap q = X := by
      rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr (pCoreIn_le 2 X)]
    exact (map_le_iff_le_comap.mp hAL).trans_eq hcq
  · intro P x hx
    have hVP : V ≤ (P : Subgroup G) :=
      (IsElementaryAbelian.isPGroup 2 V).le_sylow_of_normal P
    let Q := P.mapSurjective hq
    obtain ⟨R,hR⟩ := P.exists_sylow_map_eq_inf_of_normal X
    have hmap : ((P : Subgroup G) ⊓ X).map q = (Q : Subgroup (G ⧸ V)) ⊓ L :=
      P.map_image_eq_inf X _ R hR inf_le_left q
    have hfix : ∀ v ∈ fixedSpace τ ((Q : Subgroup (G ⧸ V)) ⊓ L), τ (q x) v = v := by
      intro v hv
      let w := f.symm v
      have hwc : (w.toMul : G) ∈ centralizer (((P : Subgroup G) ⊓ X) : Set G) := by
        apply (NormalElementaryQuotient.mem_fixedSpace_image V q hq hk
          ((P : Subgroup G) ⊓ X) w).mp
        intro g
        apply f.injective
        change f (α (g : G ⧸ V) w) = f w
        rw [htrans]
        change τ (g : G ⧸ V) (f (f.symm v)) = f (f.symm v)
        rw [f.apply_symm_apply]
        have hh := hv ⟨(g : G ⧸ V),hmap ▸ g.property⟩
        change τ (g : G ⧸ V) v = v at hh
        exact hh
      have hwZ : (w.toMul : G) ∈ centerIn ((P : Subgroup G) ⊓ X) :=
        ⟨⟨hVP w.toMul.property,pCoreIn_le 2 X w.toMul.property⟩,hwc⟩
      have hxc := hx.2 _ hwZ
      have hwfix : α (q x) w = w := by
        apply Additive.toMul.injective
        apply Subtype.ext
        rw [NormalElementaryQuotient.representation_apply]
        exact mul_inv_eq_iff_eq_mul.mpr hxc.symm
      rw [← f.apply_symm_apply v,← htrans,hwfix]
    have hqx : q x ∈ L := SL2NaturalOffenders.mem_layer_of_sylow_fixedSpace
      L c τ hf hn Q (mem_map_of_mem q hx.1) hfix
    have hpre : L.comap q = X := by
      change (X.map q).comap q = X
      rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr (pCoreIn_le 2 X)]
    exact hpre ▸ hqx
  · intro n hnodd hcard P x hx
    have hqx : q x ∈ L := by
      apply SL2NaturalOffenders.mem_layer_of_odd_field_degree hnodd hcard L c τ hf hn
      obtain ⟨k,hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp P.isPGroup') ⟨x,hx⟩
      have hxpow : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
      exact ⟨k,by rw [← map_pow,hxpow,map_one]⟩
    have hpre : L.comap q = X := by
      change (X.map q).comap q = X
      rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr (pCoreIn_le 2 X)]
    exact hpre ▸ hqx

/-- In a subgroup containing the translation plane, every maximum elementary
subgroup lies in the specified normal affine subgroup. -/
theorem maxElementary_le_affine
    (X : Subgroup G) [X.Normal] (e : X ≃* SL2.Affine F)
    (hF : 2 < Nat.card F)
    (hC : centralizer (X.pCoreIn 2 : Set G) = X.pCoreIn 2)
    (S A : Subgroup G) (hVS : X.pCoreIn 2 ≤ S)
    (hA : A ∈ elementaryAbelianMaxSubgroups S) : A ≤ X :=
  (affine_extension_control X e hF hC).1 S A hVS hA

/-- The ambient Sylow centralizer of the center of its affine intersection
lies in that intersection. Pointwise fixation of the natural fixed line
removes the field automorphism; the remaining two-element lies in SL₂. -/
theorem sylow_center_centralizer_eq
    (X : Subgroup G) [X.Normal] (e : X ≃* SL2.Affine F)
    (hF : 2 < Nat.card F)
    (hC : centralizer (X.pCoreIn 2 : Set G) = X.pCoreIn 2)
    (P : Sylow 2 G) :
    (P : Subgroup G) ⊓ centralizer (centerIn ((P : Subgroup G) ⊓ X) : Set G) =
      (P : Subgroup G) ⊓ X := by
  refine le_antisymm (le_inf inf_le_left ((affine_extension_control X e hF hC).2.1 P)) ?_
  exact le_inf inf_le_left (le_centralizer_iff.mp inf_le_right)

/-- Over an odd-degree field every ambient Sylow two-subgroup lies in the
normal affine group: its field coefficient and determinant are both trivial. -/
theorem sylow_le_affine_of_odd_field_degree
    (X : Subgroup G) [X.Normal] (e : X ≃* SL2.Affine F)
    (hF : 2 < Nat.card F)
    (hC : centralizer (X.pCoreIn 2 : Set G) = X.pCoreIn 2)
    {n : ℕ} (hn : Odd n) (hcard : Nat.card F = 2 ^ n) (P : Sylow 2 G) :
    (P : Subgroup G) ≤ X :=
  (affine_extension_control X e hF hC).2.2 hn hcard P

end Matrix.PSL3.LinearAmbientGeometry
