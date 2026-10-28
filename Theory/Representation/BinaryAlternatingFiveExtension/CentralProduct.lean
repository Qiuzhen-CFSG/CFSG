module
public import Theory.Representation.BinaryAlternatingFiveExtension.BorelModel

/-!
# A marked central direct factor

A section of the symmetric quotient and the natural action identify the group
with the natural split extension times its literal central factor. The proof
constructs the product homomorphism and checks its kernel and image. This is the
central-factor step of Aschbacher--Smith, (2.4.29).
-/

public noncomputable section
namespace BinaryPermutation.AlternatingFiveExtension
open Subgroup
variable {H : Type*} [Group H]
local notation "S5" => Equiv.Perm (Fin 5)
local notation "FullModel" => V ⋊[coreAction] S5

/-- A marked section splits off the literal central factor of the natural extension. -/
theorem product_equiv_of_marked_section
    (q : H →* S5) (U D : Subgroup H) (hD : D ≤ center H)
    (hker : q.ker = U ⊔ D) (hdis : Disjoint U D)
    (e : U ≃* V)
    (he : ∀ (h : H) (u : U),
      (e.symm (coreAction (q h) (e u)) : H) = h * (u : H) * h⁻¹)
    (s : S5 →* H) (hs : q.comp s = MonoidHom.id _) :
    ∃ E : H ≃* (FullModel × D),
      (∀ d : D, E (d : H) = (1,d)) ∧
      ((MonoidHom.fst FullModel D).comp E.toMonoidHom).ker = D := by
  let i : V →* H := U.subtype.comp e.symm.toMonoidHom
  have hi : Function.Injective i := U.subtype_injective.comp e.symm.injective
  have hiq (v : V) : q (i v) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [hker]
    exact mem_sup_left (e.symm v).property
  have hdq (d : D) : q (d : H) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [hker]
    exact mem_sup_right d.property
  have hsq (g : S5) : q (s g) = g := DFunLike.congr_fun hs g
  have hact (g : S5) : i.comp (coreAction g).toMonoidHom =
      (MulAut.conj (s g)).toMonoidHom.comp i := by
    apply MonoidHom.ext
    intro v
    change (e.symm (coreAction g v) : H) = s g * (e.symm v : H) * (s g)⁻¹
    have hh := he (s g) (e.symm v)
    rw [hsq,MulEquiv.apply_symm_apply] at hh
    exact hh
  let f : FullModel →* H := SemidirectProduct.lift i s hact
  have hf (x : FullModel) : f x = i x.left * s x.right := rfl
  have hqf (x : FullModel) : q (f x) = x.right := by rw [hf,map_mul,hiq,hsq,one_mul]
  let F : (FullModel × D) →* H := {
    toFun := fun x => f x.1 * x.2
    map_one' := by simp
    map_mul' := by
      intro x y
      change f (x.1*y.1) * ((x.2 : H)*(y.2 : H)) =
        (f x.1 * (x.2 : H)) * (f y.1 * (y.2 : H))
      rw [map_mul]
      have hc := mem_center_iff.mp (hD x.2.property) (f y.1)
      calc
        (f x.1*f y.1) * ((x.2:H)*(y.2:H)) =
            f x.1 * (f y.1 * (x.2:H)) * (y.2:H) := by group
        _ = f x.1 * ((x.2:H) * f y.1) * (y.2:H) := by rw [hc]
        _ = (f x.1 * (x.2:H)) * (f y.1 * (y.2:H)) := by group }
  have hF (x : FullModel) (d : D) : F (x,d) = f x * (d : H) := rfl
  have hFinj : Function.Injective F := by
    apply (MonoidHom.ker_eq_bot_iff F).mp
    apply eq_bot_iff.mpr
    rintro ⟨x,d⟩ hx
    have h0 : f x * (d:H) = 1 := hx
    have hxr : x.right = 1 := by
      have hh := congrArg q h0
      simpa only [map_mul,hqf,hdq,mul_one,map_one] using hh
    have hiv : i x.left = (d:H)⁻¹ := by
      rw [hf,hxr,map_one,mul_one] at h0
      exact eq_inv_of_mul_eq_one_left h0
    have hiD : i x.left ∈ D := hiv ▸ D.inv_mem d.property
    have hi1 : i x.left = 1 := by
      exact (Subgroup.disjoint_def.mp hdis (e.symm x.left).property hiD)
    have hxl : x.left = 1 := hi (hi1.trans i.map_one.symm)
    have hx1 : x = 1 := by apply SemidirectProduct.ext <;> assumption
    have hd1 : d = 1 := by
      apply Subtype.ext
      change (d:H) = 1
      simpa only [hx1,map_one,one_mul] using h0
    exact show (x,d) = 1 by rw [hx1,hd1]; rfl
  let : D.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hD hx) g,mul_inv_cancel_right]
    exact hx⟩
  have hFsurj : Function.Surjective F := by
    intro h
    have hk : h * (s (q h))⁻¹ ∈ U ⊔ D := by
      rw [←hker]
      change q (h * (s (q h))⁻¹) = 1
      rw [map_mul,map_inv,hsq,mul_inv_cancel]
    obtain ⟨u,hu,d,hd,heq⟩ := mem_sup_of_normal_right.mp hk
    let v : V := e ⟨u,hu⟩
    refine ⟨(⟨v,q h⟩,⟨d,hd⟩),?_⟩
    change (i v * s (q h)) * d = h
    have hiv : i v = u := congrArg U.subtype (e.symm_apply_apply ⟨u,hu⟩)
    rw [hiv]
    have hc := mem_center_iff.mp (hD hd) (s (q h))
    calc
      (u*s (q h))*d = (u*d)*s (q h) := by rw [mul_assoc,hc,←mul_assoc]
      _ = (h * (s (q h))⁻¹) * s (q h) := by rw [heq]
      _ = h := by group
  let E : H ≃* (FullModel × D) := (MulEquiv.ofBijective F ⟨hFinj,hFsurj⟩).symm
  have hEd (d : D) : E (d:H) = (1,d) := by
    apply E.symm.injective
    rw [E.symm_apply_apply]
    change (d:H) = f 1 * d
    rw [map_one,one_mul]
  refine ⟨E,hEd,?_⟩
  ext h
  change (E h).1 = 1 ↔ h ∈ D
  constructor
  · intro hh
    have he : E h = (1,(E h).2) := Prod.ext hh rfl
    have hv := congrArg E.symm he
    rw [E.symm_apply_apply] at hv
    change h = F (1,(E h).2) at hv
    rw [hF,map_one,one_mul] at hv
    exact hv.symm ▸ (E h).2.property
  · intro hh
    exact congrArg Prod.fst (hEd ⟨h,hh⟩)

end BinaryPermutation.AlternatingFiveExtension
end
