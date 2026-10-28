module
public import Theory.Representation.BinaryAlternatingFiveExtension.Automorphism
public import Theory.GroupTheory.AlternatingIndexTwoSection

/-!
# Extending the marked alternating complement

For the natural binary module on five letters, an actual odd involution extends
the alternating complement to a symmetric complement. Vanishing first
cohomology corrects its action by a vector. The corrected square lies both in
the natural module and in the centralizer of the alternating extension, so it
is trivial. The original involution hypothesis is essential here.

This supplies the splitting step in Aschbacher--Smith, (2.4.29).
-/

public noncomputable section
namespace BinaryPermutation.AlternatingFiveExtension
open Subgroup
variable {H : Type*} [Group H] [Finite H]
local notation "S5" => Equiv.Perm (Fin 5)
local notation "A5" => alternatingGroup (Fin 5)

/-- The original odd involution, corrected inside the natural kernel,
extends the marked A₅ complement to an S₅ section. -/
theorem exists_section_of_odd_involution
    (q : H →* S5) (U L D : Subgroup H) [L.Normal]
    (hUL : U ≤ L) (hLq : L.map q = A5) (hkerL : q.ker ⊓ L = U)
    (hD : D = centralizer (L : Set H)) (hdis : Disjoint U D)
    (e : U ≃* V)
    (he : ∀ (h : H) (u : U),
      (e.symm (coreAction (q h) (e u)) : H) = h * (u : H) * h⁻¹)
    (t : H) (ht : t^2=1) (hodd : (q t).IsSwap) :
    ∃ s : S5 →* H, q.comp s = MonoidHom.id _ := by
  let qL : L →* A5 := (q.comp L.subtype).codRestrict A5 (fun x => by
    rw [←hLq]
    exact mem_map_of_mem q x.property)
  have hqL : Function.Surjective qL := by
    intro a
    have hm : a.val ∈ L.map q := hLq.symm ▸ a.property
    obtain ⟨l,hl,he⟩ := hm
    exact ⟨⟨l,hl⟩,Subtype.ext he⟩
  have hkL : qL.ker = U.subgroupOf L := by
    ext x
    change qL x = 1 ↔ x.val ∈ U
    have hiff : qL x = 1 ↔ q x.val = 1 :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [hiff]
    rw [←hkerL]
    exact ⟨fun hx => ⟨hx,x.property⟩,fun hx => hx.1⟩
  let eL : qL.ker ≃* V := (MulEquiv.subgroupCongr hkL).trans
    ((subgroupOfEquivOfLe hUL).trans e)
  have heLsymm (v : V) : (((eL.symm v : qL.ker) : L) : H) = (e.symm v : H) := rfl
  have heLval (v : qL.ker) : eL v = e ⟨v.val.val,hkL.le v.property⟩ := rfl
  have heL (g : L) (v : qL.ker) : eL (MulAut.conjNormal g v) =
      Multiplicative.ofAdd (coreRepresentation (Fin 5) (qL g).val (eL v).toAdd) := by
    apply eL.symm.injective
    apply Subtype.ext
    apply Subtype.ext
    rw [eL.symm_apply_apply,heLsymm]
    have hh := he (g:H) ⟨v.val.val,hkL.le v.property⟩
    exact hh.symm
  obtain ⟨E,hEq,hEe⟩ := exists_marked_equiv qL hqL eL heL
  have hαq (g : L) : qL (MulAut.conjNormal t g) = MulAut.conjNormal (q t) (qL g) := by
    apply Subtype.ext
    change q (t * (g:H) * t⁻¹) = q t * q (g:H) * (q t)⁻¹
    simp only [map_mul,map_inv]
  have hαe (v : V) : MulAut.conjNormal t (eL.symm v : L) =
      (eL.symm (coreAction (q t) v) : L) := by
    apply Subtype.ext
    change t * ((eL.symm v : L) : H) * t⁻¹ =
      ((eL.symm (coreAction (q t) v) : L) : H)
    rw [heLsymm,heLsymm]
    have hh := he t (e.symm v)
    rw [e.apply_symm_apply] at hh
    exact hh.symm
  obtain ⟨n,hn⟩ := automorphism_correction qL hqL eL heL E hEq hEe
    (q t) (MulAut.conjNormal t) hαq hαe
  let τ : H := (n.val : H) * t
  have hnq : q (n.val : H) = 1 := congrArg Subtype.val (show qL n.val = 1 from n.property)
  have hτq : q τ = q t := by rw [show τ = (n.val : H) * t from rfl,map_mul,hnq,one_mul]
  have hτact (g : L) : MulAut.conjNormal τ g = E.symm (standardAction (q t) (E g)) := by
    apply Subtype.ext
    have hh := congrArg L.subtype (hn g)
    change t * (g:H) * t⁻¹ = (n.val:H)⁻¹ * (E.symm (standardAction (q t) (E g)) : H) * n.val at hh
    change ((n.val:H)*t) * (g:H) * ((n.val:H)*t)⁻¹ = _
    calc
      ((n.val:H)*t) * (g:H) * ((n.val:H)*t)⁻¹ =
          (n.val:H) * (t * (g:H) * t⁻¹) * (n.val:H)⁻¹ := by group
      _ = (E.symm (standardAction (q t) (E g)) : H) := by rw [hh]; group
  have hτsquareL : τ^2 ∈ L := by
    have hnL : (n.val : H) ∈ L := n.val.property
    have hc : t * (n.val : H) * t⁻¹ ∈ L := (inferInstance : L.Normal).conj_mem _ hnL t
    have htt : t*t=1 := by simpa only [pow_two] using ht
    have heq : τ^2 = (n.val:H) * (t * (n.val:H) * t⁻¹) := by
      dsimp [τ]
      calc
        ((n.val:H)*t)^2 = (n.val:H)*(t*(n.val:H)*t⁻¹)*(t*t) := by simp only [pow_two]; group
        _ = _ := by rw [htt,mul_one]
    rw [heq]
    exact L.mul_mem hnL hc
  have hτsquareU : τ^2 ∈ U := by
    rw [←hkerL]
    refine ⟨?_,hτsquareL⟩
    change q (τ^2) = 1
    rw [map_pow,hτq,←map_pow,ht,map_one]
  have hτsquareD : τ^2 ∈ D := by
    rw [hD]
    intro g hg
    have hiter : MulAut.conjNormal τ (MulAut.conjNormal τ (⟨g,hg⟩ : L)) =
        E.symm (standardAction (q t) (standardAction (q t) (E ⟨g,hg⟩))) := by
      calc
        _ = E.symm (standardAction (q t) (E (MulAut.conjNormal τ ⟨g,hg⟩))) := hτact _
        _ = _ := by rw [hτact (⟨g,hg⟩ : L),E.apply_symm_apply]
    have hstd : standardAction (q t) * standardAction (q t) = 1 := by
      rw [←map_mul,←map_mul,show t*t=1 from by simpa only [pow_two] using ht,map_one,map_one]
    have hfix : standardAction (q t) (standardAction (q t) (E ⟨g,hg⟩)) = E ⟨g,hg⟩ :=
      DFunLike.congr_fun hstd _
    rw [hfix,E.symm_apply_apply] at hiter
    have hh := congrArg L.subtype hiter
    change τ * (τ * g * τ⁻¹) * τ⁻¹ = g at hh
    have hh' : τ^2 * g * (τ^2)⁻¹ = g := by
      calc
        τ^2 * g * (τ^2)⁻¹ = τ * (τ*g*τ⁻¹)*τ⁻¹ := by simp only [pow_two]; group
        _ = g := hh
    exact (mul_inv_eq_iff_eq_mul.mp hh').symm
  have hτ : τ^2=1 := Subgroup.disjoint_def.mp hdis hτsquareU hτsquareD
  let a : A5 →* H := L.subtype.comp (E.symm.toMonoidHom.comp SemidirectProduct.inr)
  have ha : q.comp a = (alternatingGroup (Fin 5)).subtype := by
    apply MonoidHom.ext
    intro g
    change q (E.symm (SemidirectProduct.inr g) : H) = g.val
    have hh := hEq (E.symm (SemidirectProduct.inr g))
    rw [E.apply_symm_apply] at hh
    exact congrArg Subtype.val hh.symm
  have hac (g : A5) : τ*a g*τ⁻¹ = a (MulAut.conjNormal (q t) g) := by
    have hh := congrArg L.subtype (hτact (E.symm (SemidirectProduct.inr g)))
    rw [E.apply_symm_apply,standardAction_inr] at hh
    exact hh
  obtain ⟨s,hs,_,_⟩ := AlternatingIndexTwoSection.exists_section_extending_alternating
    q a ha (q t) hodd τ hτ hτq hac
  exact ⟨s,hs⟩

end BinaryPermutation.AlternatingFiveExtension
end
