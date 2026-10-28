module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalOrthogonality
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.GroupTheory.TwoInvolutionsSymmetricThree
public import Mathlib.GroupTheory.Perm.Cycle.Type


/-!
# Two natural point transpositions at nonorthogonal points

The displacement image of a nontrivial hyperplane fixer is exactly its
perpendicular line. Commuting fixers preserve—and over F₂ fix—each other's
lines, forcing orthogonality. Thus nonorthogonal points give noncommuting
transpositions. Their product has order three, and the literal generated
subgroup is S₃ by the dihedral presentation.

Source: Aschbacher–Smith,13.7.10(2), printed p.941.
-/

@[expose] public section

open Subgroup BinaryPermutation
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.TransvectionPair
open NaturalGeometry NaturalPairing NaturalOrthogonality

private theorem moved_eq_line (P : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P = 1) (t : S) (ht : t ≠ 1)
    (hf : ∀ v ∈ form.orthogonal P, naturalRepresentation Ω t v = v) :
    LinearMap.range (naturalRepresentation Ω t - 1) = P := by
  have hle : LinearMap.range (naturalRepresentation Ω t - 1) ≤ P := by
    rintro _ ⟨v,rfl⟩
    have hd := (fixes_iff_displacement t (form.orthogonal P)).mp hf v
    rwa [LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate form_alt.isRefl] at hd
  have hn : LinearMap.range (naturalRepresentation Ω t - 1) ≠ ⊥ := by
    intro hh
    have he := sub_eq_zero.mp (LinearMap.range_eq_bot.mp hh)
    exact ht (naturalRepresentation_injective Ω (by decide)
      (he.trans (naturalRepresentation Ω).map_one.symm))
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hu := Submodule.finrank_mono hle
  have hl : Module.finrank (ZMod 2) (LinearMap.range (naturalRepresentation Ω t - 1)) ≠ 0 :=
    fun hh => hn (Submodule.finrank_eq_zero.mp hh)
  rw [hP] at hu ⊢
  exact Nat.le_antisymm hu (Nat.one_le_iff_ne_zero.mpr hl)

private theorem binary_line_fixed (P : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P = 1) (t : S)
    (hf : ∀ v ∈ P, naturalRepresentation Ω t v ∈ P) :
    ∀ v ∈ P, naturalRepresentation Ω t v = v := by
  intro v hv
  by_cases hz : v=0
  · rw [hz,map_zero]
  have hne : (⟨v,hv⟩ : P) ≠ 0 := fun he => hz (congrArg Subtype.val he)
  obtain ⟨a,ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v,hv⟩ : P) hne).mp hP
    ⟨naturalRepresentation Ω t v,hf v hv⟩
  have ha0 : a ≠ 0 := by
    intro he
    have hh : naturalRepresentation Ω t v=0 := by
      have hha := congrArg Subtype.val ha
      simpa [he] using hha.symm
    have hhinj := (LinearMap.GeneralLinearGroup.toLinearEquiv
      ((naturalRepresentation Ω).asGroupHom t)).injective
    exact hz (hhinj (hh.trans (map_zero _).symm))
  have ha1 : a=1 := (by decide : ∀a:ZMod 2,a≠0→a=1) a ha0
  have hh := congrArg Subtype.val ha
  simpa only [ha1, SetLike.val_smul, one_smul] using hh.symm

/-- Nonorthogonal fixed hyperplanes force two genuine natural transpositions
not to commute. -/
theorem not_commute (P R : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P = 1)
    (hR : Module.finrank (ZMod 2) R = 1)
    (t s : S) (ht : t ≠ 1) (hs : s ≠ 1)
    (htf : ∀ v ∈ form.orthogonal P, naturalRepresentation Ω t v = v)
    (hsf : ∀ v ∈ form.orthogonal R, naturalRepresentation Ω s v = v)
    (hcross : ¬ R ≤ form.orthogonal P) : ¬ Commute t s := by
  intro hc
  have heR := moved_eq_line R hR s hs hsf
  have heP := moved_eq_line P hP t ht htf
  have htR : ∀ v ∈ R, naturalRepresentation Ω t v ∈ R := by
    intro v hv
    rw [←heR] at hv ⊢
    obtain ⟨w,rfl⟩ := hv
    refine ⟨naturalRepresentation Ω t w, ?_⟩
    change naturalRepresentation Ω s (naturalRepresentation Ω t w) -
      naturalRepresentation Ω t w = naturalRepresentation Ω t (naturalRepresentation Ω s w - w)
    rw [map_sub]
    have hh := congrArg (fun x : S => naturalRepresentation Ω x w) hc.eq
    simpa only [map_mul,Module.End.mul_apply] using congrArg (fun v : V => v-naturalRepresentation Ω t w) hh.symm
  have hfix := binary_line_fixed R hR t htR
  have hd := (fixes_iff_displacement t R).mp hfix
  have hPorth : P ≤ form.orthogonal R := by
    rw [←heP]
    rintro _ ⟨v,rfl⟩
    exact hd v
  apply hcross
  intro r hr p hp
  exact form_alt.eq_iff.mp (hPorth hp r hr)

private theorem swaps_cube (i j k l : Fin 6) (hij : i≠j) (hkl : k≠l)
    (hn : ¬ Commute (Equiv.swap i j) (Equiv.swap k l)) :
    (Equiv.swap i j * Equiv.swap k l)^3=1 := by
  have hc : ∀i j k l:Fin 6, i≠j→k≠l→
      Equiv.swap i j * Equiv.swap k l ≠ Equiv.swap k l * Equiv.swap i j →
      (Equiv.swap i j * Equiv.swap k l)^3=1 := by decide +kernel
  exact hc i j k l hij hkl hn

theorem product_order_three (t s : S) (ht : t.IsSwap) (hs : s.IsSwap)
    (hn : ¬ Commute t s) : orderOf (t*s)=3 := by
  obtain ⟨i,j,hij,rfl⟩ := ht
  obtain ⟨k,l,hkl,rfl⟩ := hs
  apply orderOf_eq_prime (swaps_cube i j k l hij hkl hn)
  intro he
  apply hn
  have hh : Equiv.swap i j=Equiv.swap k l := by
    have hhi := eq_inv_of_mul_eq_one_left he
    simpa only [Equiv.swap_inv] using hhi
  rw [hh]


private theorem orthogonal_map (g : S) (P : Submodule (ZMod 2) V) :
    (form.orthogonal P).map (naturalRepresentation Ω g) =
      form.orthogonal (P.map (naturalRepresentation Ω g)) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩
    rw [form_invariant]
    exact hv w hw
  · have hfin (D : Submodule (ZMod 2) V) :
        Module.finrank (ZMod 2) (D.map (naturalRepresentation Ω g)) =
          Module.finrank (ZMod 2) D :=
      (LinearMap.GeneralLinearGroup.toLinearEquiv
        ((naturalRepresentation Ω).asGroupHom g)).finrank_map_eq D
    rw [hfin,LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,
      LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,hfin]

/-- Conjugating the actual permutation also transports its fixed hyperplane. -/
theorem conjugate_fixes (P : Submodule (ZMod 2) V) (a t : S)
    (hf : ∀ v ∈ form.orthogonal P, naturalRepresentation Ω t v=v) :
    ∀ v ∈ form.orthogonal (P.map (naturalRepresentation Ω a)),
      naturalRepresentation Ω (a*t*a⁻¹) v=v := by
  rw [←orthogonal_map]
  rintro _ ⟨v,hv,rfl⟩
  simp only [map_mul,Module.End.mul_apply]
  have ha : naturalRepresentation Ω a⁻¹ (naturalRepresentation Ω a v)=v := by
    rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  rw [ha,hf v hv]

/-- The original nonorthogonal point displacement identifies the actual
subgroup generated by a transposition and its conjugate with S₃. -/
theorem conjugate_pair (P : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P=1) (a t : S) (ht : t.IsSwap)
    (hf : ∀ v ∈ form.orthogonal P, naturalRepresentation Ω t v=v)
    (hc : ¬ P.map (naturalRepresentation Ω a) ≤ form.orthogonal P) :
    Nonempty ((zpowers t ⊔ zpowers (a*t*a⁻¹) : Subgroup S) ≃* Equiv.Perm (Fin 3)) := by
  have hs : (a*t*a⁻¹).IsSwap := by
    obtain ⟨i,j,hij,rfl⟩:=ht
    rw [←Equiv.swap_apply_apply]
    exact ⟨_,_,a.injective.ne hij,rfl⟩
  have hr : Module.finrank (ZMod 2) (P.map (naturalRepresentation Ω a))=1 :=
    ((LinearMap.GeneralLinearGroup.toLinearEquiv
      ((naturalRepresentation Ω).asGroupHom a)).finrank_map_eq P).trans hP
  have htn : t≠1 := by
    obtain ⟨i,j,hij,rfl⟩:=ht
    exact fun hh=>hij (Equiv.swap_eq_one_iff.mp hh)
  have hsn : a*t*a⁻¹≠1 := by
    intro hh
    apply htn
    have he:=congrArg (fun x:S=>a⁻¹*x*a) hh
    simpa only [mul_assoc,inv_mul_cancel,mul_inv_cancel_left,inv_mul_cancel_left,mul_one,one_mul] using he
  have hn := not_commute P _ hP hr t _ htn hsn hf (conjugate_fixes P a t hf) hc
  have ht2 : t^2=1 := by obtain ⟨i,j,hij,rfl⟩:=ht; rw [pow_two, Equiv.swap_mul_self]
  have hs2 : (a*t*a⁻¹)^2=1 := by rw [conj_pow,ht2,mul_one,mul_inv_cancel]
  exact symmetricThree_of_involutions_product_three t _ ht2 hs2 (product_order_three t _ ht hs hn)

/-- Centralizing a nonidentity point transposition preserves its literal center line. -/
theorem centralizer_stabilizes_line (P : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P=1) (t c:S) (ht:t≠1)
    (hf : ∀v∈form.orthogonal P,naturalRepresentation Ω t v=v)
    (hc:Commute t c) : P.map (naturalRepresentation Ω c)=P := by
  have he:=moved_eq_line P hP t ht hf
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨v,hv,rfl⟩
    rw [←he] at hv ⊢
    obtain ⟨w,rfl⟩:=hv
    refine ⟨naturalRepresentation Ω c w,?_⟩
    change naturalRepresentation Ω t (naturalRepresentation Ω c w)-naturalRepresentation Ω c w =
      naturalRepresentation Ω c (naturalRepresentation Ω t w-w)
    rw [map_sub]
    have hh:=congrArg (fun x:S=>naturalRepresentation Ω x w) hc.eq
    exact congrArg (fun v:V=>v-naturalRepresentation Ω c w)
      (by simpa only [map_mul,Module.End.mul_apply] using hh)
  · exact (LinearMap.GeneralLinearGroup.toLinearEquiv
      ((naturalRepresentation Ω).asGroupHom c)).finrank_map_eq P
end Theory.SpecificGroups.SymmetricSix.BinaryFlags.TransvectionPair


