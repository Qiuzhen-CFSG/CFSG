module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CoreInvolutionLifts
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.MarkedOverlaps
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.OverlapIndices
public import Theory.ElementaryAbelian.Injective

/-!
# Original marked core image and involution lifting

The odd-index point-plane overlap contains the whole original extraspecial
core Q. Restricting the original cocode quotient gives a normal subgroup of
the same native sextet stabilizer. Its kernel embeds in the elementary
cocode subgroup, so CoreInvolutionLifts identifies its image with the entire
sextet two-core and gives genuine involution lifts there. Both M24
involution classes meet that core; lifting conjugators gives an involution
above every involution of the original quotient.

All maps retain the original marker, cubic quotient, and cocode marking.
Neither Todd splitting nor LocalData is assumed. The actual Mathieu
application is MathieuJ4RecognitionApplication.CoreInvolutions.
Source: Aschbacher--Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), (4.8), p.599, DOI 10.1007/BF01232280.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open LocalGeometry Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
noncomputable section
variable {G : Type*} [Group G] [Finite G]

/-- The original core, included in the original cocode normalizer. -/
def coreNormalizerInclusion (W : Subgroup G) {z : G}
    (hle : core z ≤ (normalizer (W : Set G)).subgroupOf (centralizer z)) :
    core z →* normalizer (W : Set G) where
  toFun q := ⟨q.val.val,hle q.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Finite G] in
theorem coreNormalizerInclusion_injective (W : Subgroup G) {z : G}
    (hle : core z ≤ (normalizer (W : Set G)).subgroupOf (centralizer z)) :
    Function.Injective (coreNormalizerInclusion W hle) := by
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun n : normalizer (W : Set G) => n.val) he

theorem marked_cocode_core_image_and_lifts
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (f : normalizer (W : Set G) →* M24) (hf : Function.Surjective f)
    (hk : f.ker = W.subgroupOf (normalizer (W : Set G)))
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)))
    (z : W) (S : Sextet) (hz : E (Additive.ofMul z) = sextetVector S)
    (h : IsTypeJ4 (z : G))
    (e : CubicAutomorphismQuotient (centralizer (z : G) ⧸ core (z : G))) :
    ∃ hle : core (z : G) ≤ (normalizer (W : Set G)).subgroupOf (centralizer (z : G)),
      let q := f.comp (coreNormalizerInclusion W hle)
      q.range = (sextetStabilizer S).pCoreIn 2 ∧ Nat.card q.ker = 128 ∧
      ∀ u ∈ (sextetStabilizer S).pCoreIn 2, u ≠ 1 →
        ∃ x : core (z : G), q x = u ∧ orderOf x = 2 := by
  let := h.extraspecial
  have hWc : Nat.card W = 2048 := by
    change Nat.card (Additive W) = _
    rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
      finrank_cocode,Nat.card_zmod]
    norm_num
  have hc := marked_cocode_plane_card W f hf hk hWc E hE z S hz
  have hle := (CubicLift.core_le e).trans
    (marked_pointPlane_contains_cubic h e (normalizer (W : Set G)) hc)
  let j := coreNormalizerInclusion W hle
  let q := f.comp j
  have hpre := marked_cocode_plane_preimage W f E hE z S hz
  have hqS (x : core (z : G)) : q x ∈ sextetStabilizer S :=
    hpre.le x.val.property
  let qS : core (z : G) →* sextetStabilizer S := q.codRestrict _ hqS
  let : qS.range.Normal := ⟨fun y hy g => by
    obtain ⟨x,rfl⟩ := hy
    obtain ⟨n,hn,he⟩ := (marked_cocode_plane_image W f hf E hE z S hz).ge g.property
    let nH : centralizer (z : G) := ⟨n.val,hn⟩
    let x' : core (z : G) := ⟨nH*x.val*nH⁻¹,
      (inferInstance : (core (z : G)).Normal).conj_mem x.val x.property nH⟩
    refine ⟨x',Subtype.ext ?_⟩
    change f (j x') = g.val * f (j x) * g.val⁻¹
    have hj : j x' = n*j x*n⁻¹ := rfl
    rw [hj,map_mul,map_mul,map_inv,he]⟩
  have hker : qS.ker = q.ker := by
    ext x
    change qS x = 1 ↔ q x = 1
    exact Subtype.ext_iff
  let k : qS.ker →* W := {
    toFun x := ⟨x.val.val.val,by
      have hh : j x.val ∈ f.ker := by
        change q x.val=1
        exact hker.le x.property
      rw [hk] at hh
      exact hh⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hki : Function.Injective k := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : W => w.val) he
  let : IsElementaryAbelian 2 qS.ker := IsElementaryAbelian.of_injective k hki
  obtain ⟨hr,hkc⟩ := extraspecial_sextet_image h.core_card S qS
  have hrq : q.range = qS.range.map (sextetStabilizer S).subtype := by
    rw [←MonoidHom.range_comp]
    rfl
  refine ⟨hle,?_,hker ▸ hkc,?_⟩
  · rw [hrq,hr]
    rfl
  · intro u hu hne
    obtain ⟨v,hv,rfl⟩ := hu
    obtain ⟨x,hx,hx2⟩ := extraspecial_sextet_involution_lift h.core_card S qS v hv
      (fun he => hne (congrArg Subtype.val he))
    exact ⟨x,congrArg Subtype.val hx,hx2⟩

/-- Both native involution classes lift through the original cocode quotient. -/
theorem marked_cocode_involution_lift
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (f : normalizer (W : Set G) →* M24) (hf : Function.Surjective f)
    (hk : f.ker = W.subgroupOf (normalizer (W : Set G)))
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)))
    (z : W) (S : Sextet) (hz : E (Additive.ofMul z) = sextetVector S)
    (h : IsTypeJ4 (z : G))
    (e : CubicAutomorphismQuotient (centralizer (z : G) ⧸ core (z : G)))
    (u : M24) (hu : orderOf u = 2) :
    ∃ x : normalizer (W : Set G), f x = u ∧ orderOf x = 2 := by
  obtain ⟨hle,_,_,hlift⟩ := marked_cocode_core_image_and_lifts W f hf hk E hE z S hz h e
  have hclass : ∃ v ∈ (sextetStabilizer S).pCoreIn 2, IsConj v u := by
    rcases M24InvolutionCentralizers.involution_classes u hu with ha | hb
    · obtain ⟨v,hv,hc⟩ := J4Fusion.sextet_core_class S true
      exact ⟨v,hv,hc.symm.trans ha⟩
    · obtain ⟨v,hv,hc⟩ := J4Fusion.sextet_core_class S false
      exact ⟨v,hv,hc.symm.trans hb⟩
  obtain ⟨v,hv,hvu⟩ := hclass
  have hvne : v ≠ 1 := by
    intro he
    obtain ⟨g,hg⟩ := isConj_iff.mp hvu
    rw [he,mul_one,mul_inv_cancel] at hg
    rw [←hg,orderOf_one] at hu
    omega
  obtain ⟨x,hx,hx2⟩ := hlift v hv hvne
  have hjx : orderOf (coreNormalizerInclusion W hle x) = 2 :=
    (orderOf_injective _ (coreNormalizerInclusion_injective W hle) x).trans hx2
  apply Theory.GroupTheory.DoubleCoverInvolutionLifting.involution_lift_of_isConj f hf hjx
  change IsConj ((f.comp (coreNormalizerInclusion W hle)) x) u
  rw [hx]
  exact hvu
end
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
