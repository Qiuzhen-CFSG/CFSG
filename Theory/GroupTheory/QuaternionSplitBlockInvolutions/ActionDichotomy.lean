module
public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.ActionDichotomy.MarkedCubic
public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.ActionDichotomy.CubicInversion
public import Theory.GroupTheory.QuaternionSplitBlockInvolutions

/-!
# Marked quaternion actions through the actual quotient

The pointwise kernel of the square-quotient action is identified literally.
For any normal Q equal to this kernel, the induced H/Q action is faithful;
thus a cubic R-image and its inversion pass from H/Q to the square space.
The full commutator hypothesis then proves the c₂/factor-interchange type
dichotomy. The swapping branch constructs A = ⟨a,[U,a]⟩ itself, including its
fixed-eight commutator and its elementary structure and order sixteen.

The c₂ branch also proves inversion of the whole elementary cubic K-image.
The normalizer product in the swapping case remains a separate source
obligation. In particular, no assumption U = O₂(H) is made.

Source: combined manuscript of 1 March 2004, printed pp.1006–1007.
-/

open Subgroup
open Representation.BinaryOffender
namespace Subgroup.QuaternionCentralProductData
variable {H : Type*} [Group H] [Finite H] (U : Subgroup H) [U.Normal]
    (d : QuaternionCentralProductData U)

public theorem normalSquareLinearAction_apply (h : H) (u : U) :
    d.normalSquareLinearAction U h
      (Additive.ofMul (QuotientGroup.mk' (center U) u)) =
    Additive.ofMul (QuotientGroup.mk' (center U) (MulAut.conjNormal h u)) := by
  change d.quotientLinearAction (MulAut.conjNormal h)
    (Additive.ofMul (QuotientGroup.mk' (center U) u)) = _
  rw [d.quotientLinearAction_apply, quotientAut_apply_mk]

/-- The kernel is exactly the pointwise centralizer of the literal square quotient. -/
public theorem mem_normalSquareLinearAction_ker_iff (h : H) :
    h ∈ (d.normalSquareLinearAction U).ker ↔
      ∀ u : U, QuotientGroup.mk' (center U) (MulAut.conjNormal h u) =
        QuotientGroup.mk' (center U) u := by
  constructor
  · intro hh u
    have he := LinearEquiv.congr_fun hh (Additive.ofMul (QuotientGroup.mk' (center U) u))
    rw [normalSquareLinearAction_apply] at he
    exact congrArg Additive.toMul he
  · intro hh
    apply LinearEquiv.ext
    intro v
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (center U) v.toMul
    have hv : v = Additive.ofMul (QuotientGroup.mk' (center U) u) :=
      congrArg Additive.ofMul hu.symm
    rw [hv, normalSquareLinearAction_apply, hh]
    rfl

/-- Input the marked cubic through the literal quotient map H → H/Q. -/
public theorem marked_action_type_dichotomy_of_quotient
    (Q : Subgroup H) [Q.Normal]
    (hkernel : (d.normalSquareLinearAction U).ker = Q)
    (R : Subgroup H) (hR : Nat.card (R.map (QuotientGroup.mk' Q)) = 3)
    (hmove : subspaceCommutator (d.normalSquareRepresentation U) ⊤ R = ⊤)
    (a : H) (ha : a^2=1)
    (hinv : ∀ r ∈ R, QuotientGroup.mk' Q (a*r*a⁻¹) = (QuotientGroup.mk' Q r)⁻¹) :
    (d.IsC2Action (MulAut.conjNormal a) ∧ d.BothOuter (MulAut.conjNormal a)) ∨
      (d.left.map (MulAut.conjNormal a).toMonoidHom = d.right ∧
        d.IsA2Action (MulAut.conjNormal a)) := by
  let σ := d.normalSquareLinearAction U
  let π := QuotientGroup.mk' Q
  let φ := QuotientGroup.lift Q σ hkernel.ge
  have hφ : Function.Injective φ := (QuotientGroup.injective_lift_iff Q σ hkernel.ge).mpr hkernel.symm
  have hc : φ.comp π = σ := QuotientGroup.lift_comp_mk' Q σ hkernel.ge
  have hcard : Nat.card (R.map σ) = 3 := by
    rw [← hc, ← map_map, card_map_of_injective hφ, hR]
  apply d.marked_action_type_dichotomy U R hcard hmove a ha
  intro r hr
  have he : σ (a*r*a⁻¹) = φ (π (a*r*a⁻¹)) := rfl
  rw [he, hinv r hr, map_inv]
  rfl

/-- Add the literal source elementary sixteen to the factor-interchange branch. -/
public theorem marked_action_type_dichotomy_with_sixteen
    (Q : Subgroup H) [Q.Normal]
    (hkernel : (d.normalSquareLinearAction U).ker = Q)
    (R : Subgroup H) (hR : Nat.card (R.map (QuotientGroup.mk' Q)) = 3)
    (hmove : subspaceCommutator (d.normalSquareRepresentation U) ⊤ R = ⊤)
    (a : H) (ha : a^2=1) (hout : a ∉ U)
    (hinv : ∀ r ∈ R, QuotientGroup.mk' Q (a*r*a⁻¹) = (QuotientGroup.mk' Q r)⁻¹) :
    (d.IsC2Action (MulAut.conjNormal a) ∧ d.BothOuter (MulAut.conjNormal a)) ∨
      (d.IsA2Action (MulAut.conjNormal a) ∧
        (d.left.map U.subtype).map (MulAut.conj a).toMonoidHom = d.right.map U.subtype ∧
        ⁅U,zpowers a⁆ = U ⊓ centralizer ({a} : Set H) ∧
        IsElementaryAbelian 2 (zpowers a ⊔ ⁅U,zpowers a⁆ : Subgroup H) ∧
        Nat.card (zpowers a ⊔ ⁅U,zpowers a⁆ : Subgroup H) = 16) := by
  rcases d.marked_action_type_dichotomy_of_quotient U Q hkernel R hR hmove a ha hinv with
    h | ⟨hs, ht⟩
  · exact Or.inl h
  · have hs' : (d.left.map U.subtype).map (MulAut.conj a).toMonoidHom =
        d.right.map U.subtype := by
      rw [map_map]
      have he : (MulAut.conj a).toMonoidHom.comp U.subtype =
          U.subtype.comp (MulAut.conjNormal a).toMonoidHom := rfl
      rw [he, ← map_map, hs]
    exact Or.inr ⟨ht, hs', d.elementary_sixteen_of_swap U a ha hout hs'⟩

/-- Both outer factor restrictions invert the whole elementary cubic image,
through the literal quotient map, without assuming its inversion. -/
public theorem bothOuter_inverts_elementary_quotient
    (Q : Subgroup H) [Q.Normal]
    (hkernel : (d.normalSquareLinearAction U).ker = Q)
    (K : Subgroup H) (hK : IsElementaryAbelian 3 (K.map (QuotientGroup.mk' Q)))
    (a : H) (ha : a^2=1) (ho : d.BothOuter (MulAut.conjNormal a)) :
    ∀ k ∈ K, QuotientGroup.mk' Q (a*k*a⁻¹) = (QuotientGroup.mk' Q k)⁻¹ := by
  let σ := d.normalSquareLinearAction U
  let π := QuotientGroup.mk' Q
  let φ := QuotientGroup.lift Q σ hkernel.ge
  have hφ : Function.Injective φ :=
    (QuotientGroup.injective_lift_iff Q σ hkernel.ge).mpr hkernel.symm
  intro k hk
  have hcube : (π k)^3=1 := by
    let _ := hK
    exact elemPow_eq_one_of_isElementaryAbelian (π k) (mem_map_of_mem π hk)
  have hkQ : k^3 ∈ Q := (QuotientGroup.eq_one_iff _).mp (by
    change π (k^3)=1
    rw [map_pow]
    exact hcube)
  have hkact := (d.mem_normalSquareLinearAction_ker_iff U (k^3)).mp (hkernel.symm ▸ hkQ)
  have hc : (quotientAut (center U) (MulAut.conjNormal k))^3=1 := by
    rw [← map_pow, ← map_pow]
    ext v
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (center U) v
    rw [quotientAut_apply_mk]
    exact hkact u
  have ha' : (MulAut.conjNormal a : MulAut U)^2=1 := by rw [← map_pow,ha,map_one]
  have hi := BothOuter.inverts_cubic d ho ha' (MulAut.conjNormal k) hc
  have hi' : quotientAut (center U) (MulAut.conjNormal (a*k*a⁻¹)) =
      quotientAut (center U) (MulAut.conjNormal k⁻¹) := by
    simpa only [map_mul,map_inv] using hi
  rw [← map_inv]
  apply hφ
  change σ (a*k*a⁻¹) = σ k⁻¹
  apply LinearEquiv.ext
  intro v
  change d.quotientLinearAction (MulAut.conjNormal (a*k*a⁻¹)) v =
    d.quotientLinearAction (MulAut.conjNormal k⁻¹) v
  change d.quotientLinearAction (MulAut.conjNormal (a*k*a⁻¹)) (Additive.ofMul v.toMul) =
    d.quotientLinearAction (MulAut.conjNormal k⁻¹) (Additive.ofMul v.toMul)
  rw [d.quotientLinearAction_apply,d.quotientLinearAction_apply,hi']

/-- The complete action alternative, including inversion of every element of
K*, with the literal source sixteen retained in the swapping branch.
The normalizer-product clause is a further source obligation. -/
public theorem marked_action_dichotomy_with_cubic_inversion
    (Q : Subgroup H) [Q.Normal]
    (hkernel : (d.normalSquareLinearAction U).ker = Q)
    (K : Subgroup H) (hK : IsElementaryAbelian 3 (K.map (QuotientGroup.mk' Q)))
    (R : Subgroup H) (hR : Nat.card (R.map (QuotientGroup.mk' Q)) = 3)
    (hmove : subspaceCommutator (d.normalSquareRepresentation U) ⊤ R = ⊤)
    (a : H) (ha : a^2=1) (hout : a ∉ U)
    (hinv : ∀ r ∈ R, QuotientGroup.mk' Q (a*r*a⁻¹) = (QuotientGroup.mk' Q r)⁻¹) :
    (d.IsC2Action (MulAut.conjNormal a) ∧ d.BothOuter (MulAut.conjNormal a) ∧
      ∀ k ∈ K, QuotientGroup.mk' Q (a*k*a⁻¹) = (QuotientGroup.mk' Q k)⁻¹) ∨
      (d.IsA2Action (MulAut.conjNormal a) ∧
        (d.left.map U.subtype).map (MulAut.conj a).toMonoidHom = d.right.map U.subtype ∧
        ⁅U,zpowers a⁆ = U ⊓ centralizer ({a} : Set H) ∧
        IsElementaryAbelian 2 (zpowers a ⊔ ⁅U,zpowers a⁆ : Subgroup H) ∧
        Nat.card (zpowers a ⊔ ⁅U,zpowers a⁆ : Subgroup H) = 16) := by
  rcases d.marked_action_type_dichotomy_with_sixteen U Q hkernel R hR hmove a ha hout hinv with
    h | h
  · exact Or.inl ⟨h.1,h.2,d.bothOuter_inverts_elementary_quotient U Q hkernel K hK a ha h.2⟩
  · exact Or.inr h

end Subgroup.QuaternionCentralProductData
