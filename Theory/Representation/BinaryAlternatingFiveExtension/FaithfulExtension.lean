module
public import Theory.Representation.BinaryAlternatingFiveExtension.OddExtension

/-!
# Splitting the faithful binary five-point extension

The marked A₅ extension splits over the regular Klein four subgroup. Its
vanishing first cohomology corrects any lift of a transposition to induce
the standard automorphism of that split extension. The corrected square
belongs to the natural kernel and centralizes A₅. The natural kernel has
no fixed vectors, so this square is trivial. The resulting symmetric
section yields an isomorphism retaining both the quotient and kernel maps.

Unlike extensions with an additional central factor, this faithful-kernel
case needs no prescribed involutory lift. The source application is the
plane endpoint of Aschbacher–Smith 13.5.17, printed p.922, whose two-core
is exactly the natural four-dimensional module.
-/
public noncomputable section
namespace BinaryPermutation.AlternatingFiveExtension
open Subgroup
local notation "A5" => alternatingGroup (Fin 5)
local notation "S5" => Equiv.Perm (Fin 5)

private theorem core_fixed_alternating (v : V)
    (h : ∀ a : A5, coreAction a.val v = v) : v = 1 := by
  have hh : ∀ v : V, (∀ a : A5, coreAction a.val v = v) → v = 1 := by decide +kernel
  exact hh v h

/-- A faithful natural kernel has no central obstruction to extending the
alternating complement across the symmetric quotient. -/
theorem exists_section_of_faithful_kernel {G : Type*} [Group G] [Finite G]
    (q : G →* S5) (hq : Function.Surjective q) (e : q.ker ≃* V)
    (he : ∀ (g : G) (v : q.ker), e (MulAut.conjNormal g v) = coreAction (q g) (e v)) :
    ∃ s : S5 →* G, q.comp s = MonoidHom.id _ := by
  let L := (alternatingGroup (Fin 5)).comap q
  let : L.Normal := inferInstanceAs ((alternatingGroup (Fin 5)).comap q).Normal
  let qL : L →* A5 := (q.comp L.subtype).codRestrict A5 (fun x => x.property)
  have hqL : Function.Surjective qL := by
    intro a
    obtain ⟨g,hg⟩ := hq a.val
    exact ⟨⟨g,show q g ∈ A5 by rw [hg]; exact a.property⟩,Subtype.ext hg⟩
  have hUL : q.ker ≤ L := by
    intro x hx
    change q x ∈ alternatingGroup (Fin 5)
    rw [show q x = 1 from hx]
    exact (alternatingGroup (Fin 5)).one_mem
  have hkL : qL.ker = q.ker.subgroupOf L := by
    ext x
    exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
  let eL : qL.ker ≃* V := (MulEquiv.subgroupCongr hkL).trans
    ((subgroupOfEquivOfLe hUL).trans e)
  have heLsymm (v : V) : (((eL.symm v : qL.ker) : L) : G) = (e.symm v : G) := rfl
  have heLval (v : qL.ker) : eL v = e ⟨v.val.val,hkL.le v.property⟩ := rfl
  have heL (g : L) (v : qL.ker) : eL (MulAut.conjNormal g v) =
      Multiplicative.ofAdd (coreRepresentation (Fin 5) (qL g).val (eL v).toAdd) :=
    he g.val ⟨v.val.val,hkL.le v.property⟩
  obtain ⟨E,hEq,hEe⟩ := exists_marked_equiv qL hqL eL heL
  let σ : S5 := Equiv.swap 0 1
  have hσ : σ.IsSwap := ⟨0,1,by decide,rfl⟩
  have hσsq : σ*σ=1 := Equiv.swap_mul_self 0 1
  obtain ⟨t,htq⟩ := hq σ
  have hαq (g : L) : qL (MulAut.conjNormal t g) = MulAut.conjNormal σ (qL g) := by
    apply Subtype.ext
    change q (t * (g:G) * t⁻¹) = σ * q (g:G) * σ⁻¹
    simp only [map_mul,map_inv,htq]
  have hαe (v : V) : MulAut.conjNormal t (eL.symm v : L) =
      (eL.symm (coreAction σ v) : L) := by
    apply Subtype.ext
    change t * ((eL.symm v : L) : G) * t⁻¹ =
      ((eL.symm (coreAction σ v) : L) : G)
    rw [heLsymm,heLsymm]
    have hh := he t (e.symm v)
    rw [e.apply_symm_apply,htq] at hh
    exact congrArg (fun w : q.ker => (w:G)) (e.symm_apply_apply (MulAut.conjNormal t (e.symm v))).symm |>.trans
      (congrArg (fun w : V => (e.symm w : G)) hh)
  obtain ⟨n,hn⟩ := automorphism_correction qL hqL eL heL E hEq hEe
    σ (MulAut.conjNormal t) hαq hαe
  let τ : G := (n.val : G) * t
  have hnq : q (n.val : G) = 1 := congrArg Subtype.val (show qL n.val = 1 from n.property)
  have hτq : q τ = σ := by rw [show τ = (n.val : G)*t from rfl,map_mul,hnq,one_mul,htq]
  have hτact (g : L) : MulAut.conjNormal τ g = E.symm (standardAction σ (E g)) := by
    apply Subtype.ext
    have hh := congrArg L.subtype (hn g)
    change t * (g:G) * t⁻¹ = (n.val:G)⁻¹ * (E.symm (standardAction σ (E g)) : G) * n.val at hh
    change ((n.val:G)*t) * (g:G) * ((n.val:G)*t)⁻¹ = _
    calc
      _ = (n.val:G) * (t * (g:G) * t⁻¹) * (n.val:G)⁻¹ := by group
      _ = _ := by rw [hh]; group
  have hτsquareU : τ^2 ∈ q.ker := by
    change q (τ^2) = 1
    rw [map_pow,hτq,pow_two,hσsq]
  have hτsquareC : τ^2 ∈ centralizer (L : Set G) := by
    intro g hg
    have hiter : MulAut.conjNormal τ (MulAut.conjNormal τ (⟨g,hg⟩ : L)) =
        E.symm (standardAction σ (standardAction σ (E ⟨g,hg⟩))) := by
      calc
        _ = E.symm (standardAction σ (E (MulAut.conjNormal τ ⟨g,hg⟩))) := hτact _
        _ = _ := by rw [hτact (⟨g,hg⟩ : L),E.apply_symm_apply]
    have hstd : standardAction σ * standardAction σ = 1 := by rw [←map_mul,hσsq,map_one]
    have hfix : standardAction σ (standardAction σ (E ⟨g,hg⟩)) = E ⟨g,hg⟩ :=
      DFunLike.congr_fun hstd _
    rw [hfix,E.symm_apply_apply] at hiter
    have hh := congrArg L.subtype hiter
    change τ * (τ * g * τ⁻¹) * τ⁻¹ = g at hh
    have hh' : τ^2 * g * (τ^2)⁻¹ = g := by
      calc
        _ = τ * (τ*g*τ⁻¹)*τ⁻¹ := by simp only [pow_two]; group
        _ = g := hh
    exact (mul_inv_eq_iff_eq_mul.mp hh').symm
  have hτ : τ^2=1 := by
    suffices hh : (⟨τ^2,hτsquareU⟩ : q.ker) = 1 from congrArg Subtype.val hh
    apply e.injective
    rw [map_one]
    apply core_fixed_alternating
    intro a
    obtain ⟨g,hg⟩ := hqL a
    rw [←congrArg Subtype.val hg]
    change coreAction (q g.val) (e ⟨τ^2,hτsquareU⟩) = _
    rw [←he]
    apply congrArg e
    apply Subtype.ext
    change (g:G)*τ^2*(g:G)⁻¹ = τ^2
    rw [hτsquareC g g.property,mul_inv_cancel_right]
  let a : A5 →* G := L.subtype.comp (E.symm.toMonoidHom.comp SemidirectProduct.inr)
  have ha : q.comp a = (alternatingGroup (Fin 5)).subtype := by
    apply MonoidHom.ext
    intro g
    change q (E.symm (SemidirectProduct.inr g) : G) = g.val
    have hh := hEq (E.symm (SemidirectProduct.inr g))
    rw [E.apply_symm_apply] at hh
    exact congrArg Subtype.val hh.symm
  have hac (g : A5) : τ*a g*τ⁻¹ = a (MulAut.conjNormal σ g) := by
    have hh := congrArg L.subtype (hτact (E.symm (SemidirectProduct.inr g)))
    rw [E.apply_symm_apply,standardAction_inr] at hh
    exact hh
  obtain ⟨s,hs,_,_⟩ := AlternatingIndexTwoSection.exists_section_extending_alternating
    q a ha σ hσ τ hτ hτq hac
  exact ⟨s,hs⟩

/-- Every symmetric-five extension by its natural faithful binary kernel has
an isomorphism preserving the given quotient and every kernel coordinate. -/
theorem exists_marked_symmetric_equiv {G : Type*} [Group G] [Finite G]
    (q : G →* S5) (hq : Function.Surjective q) (e : q.ker ≃* V)
    (he : ∀ (g : G) (v : q.ker), e (MulAut.conjNormal g v) = coreAction (q g) (e v)) :
    ∃ E : G ≃* V ⋊[coreAction] S5,
      (∀ g, (E g).right = q g) ∧
      (∀ v : q.ker, E (v : G) = SemidirectProduct.inl (e v)) := by
  obtain ⟨s,hs⟩ := exists_section_of_faithful_kernel q hq e he
  let i : V →* G := q.ker.subtype.comp e.symm.toMonoidHom
  have hi : Function.Injective i := q.ker.subtype_injective.comp e.symm.injective
  have hiq (v : V) : q (i v) = 1 := (e.symm v).property
  have hsq (a : S5) : q (s a) = a := DFunLike.congr_fun hs a
  have hact (a : S5) : i.comp (coreAction a).toMonoidHom =
      (MulAut.conj (s a)).toMonoidHom.comp i := by
    apply MonoidHom.ext
    intro v
    change (e.symm (coreAction a v) : G) = s a * (e.symm v : G) * (s a)⁻¹
    have hh := he (s a) (e.symm v)
    rw [e.apply_symm_apply,hsq] at hh
    have hh' := congrArg (fun w : V => (e.symm w : G)) hh
    simpa only [e.symm_apply_apply,MulAut.conjNormal_apply] using hh'.symm
  let f : V ⋊[coreAction] S5 →* G := SemidirectProduct.lift i s hact
  have hf (x : V ⋊[coreAction] S5) : f x = i x.left * s x.right := rfl
  have hqf (x : V ⋊[coreAction] S5) : q (f x) = x.right := by
    rw [hf,map_mul,hiq,hsq,one_mul]
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hr : x.right=1 := (hqf x).symm.trans (by rw [show f x=1 from hx,map_one])
    have hl : x.left=1 := by
      apply hi
      rw [map_one]
      have hh : f x=1 := hx
      rwa [hf,hr,map_one,mul_one] at hh
    exact SemidirectProduct.ext hl hr
  have hfs : Function.Surjective f := by
    intro g
    let v : q.ker := ⟨g * (s (q g))⁻¹, by
      change q (g * (s (q g))⁻¹)=1
      rw [map_mul,map_inv,hsq,mul_inv_cancel]⟩
    refine ⟨⟨e v,q g⟩,?_⟩
    change (e.symm (e v) : G) * s (q g)=g
    rw [e.symm_apply_apply]
    exact inv_mul_cancel_right _ _
  let E : G ≃* V ⋊[coreAction] S5 := (MulEquiv.ofBijective f ⟨hfi,hfs⟩).symm
  refine ⟨E,?_,?_⟩
  · intro g
    obtain ⟨x,rfl⟩ := hfs g
    change ((MulEquiv.ofBijective f ⟨hfi,hfs⟩).symm
      ((MulEquiv.ofBijective f ⟨hfi,hfs⟩) x)).right = q (f x)
    rw [MulEquiv.symm_apply_apply,hqf]
  · intro v
    apply E.symm.injective
    rw [E.symm_apply_apply]
    change (v:G) = i (e v) * s 1
    simp only [map_one,mul_one]
    exact (congrArg q.ker.subtype (e.symm_apply_apply v)).symm

end BinaryPermutation.AlternatingFiveExtension
