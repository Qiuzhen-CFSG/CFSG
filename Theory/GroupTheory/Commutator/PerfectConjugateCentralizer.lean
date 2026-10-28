module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# A perfect subgroup and a centralizing conjugator

Suppose A normalizes W, t centralizes W, and [A,Aᵗ] centralizes W.
The images of A and Aᵗ in the induced automorphism group of W coincide
and commute. If A is perfect, this image is both perfect and abelian,
so A centralizes W.

The source application rules out an element interchanging the two tensor
factors while centralizing their singular plane: Aschbacher–Smith 9.2.2(3)
and 9.3.6, combined manuscript, printed pp.731 and733.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem perfect_centralizes_of_centralizing_conjugator
    (A W : Subgroup G) [Group.IsPerfect A]
    (hAN : A ≤ normalizer (W : Set G)) (t : G)
    (ht : t ∈ centralizer (W : Set G))
    (hc : ⁅A,A.map (MulAut.conj t).toMonoidHom⁆ ≤ centralizer (W : Set G)) :
    A ≤ centralizer (W : Set G) := by
  let N := normalizer (W : Set G)
  let A' := A.subgroupOf N
  let t' : N := ⟨t,centralizer_le_normalizer _ ht⟩
  let f := W.normalizerMonoidHom
  have hAmap : A'.map N.subtype = A := map_subgroupOf_eq_of_le hAN
  have hconj : (A'.map (MulAut.conj t').toMonoidHom).map N.subtype =
      A.map (MulAut.conj t).toMonoidHom := by
    rw [map_map,show N.subtype.comp (MulAut.conj t').toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp N.subtype from rfl,←map_map,hAmap]
  have hft : f t' = 1 := by
    change t' ∈ f.ker
    rw [Subgroup.normalizerMonoidHom_ker]
    exact ht
  have hc' : ⁅A',A'.map (MulAut.conj t').toMonoidHom⁆ ≤ f.ker := by
    intro x hx
    rw [Subgroup.normalizerMonoidHom_ker]
    have hh := mem_map_of_mem N.subtype hx
    rw [map_commutator,hAmap,hconj] at hh
    exact hc hh
  have he : (A'.map (MulAut.conj t').toMonoidHom).map f = A'.map f := by
    rw [map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change f (t'*x*t'⁻¹) = f x
    simp only [map_mul,map_inv,hft,one_mul,inv_one,mul_one]
  let : Group.IsPerfect A' := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hAN).symm.toMonoidHom)
    (subgroupOfEquivOfLe hAN).symm.surjective
  have hp : ⁅A'.map f,A'.map f⁆ = A'.map f := by
    let := Group.IsPerfect.map f (H := A')
    exact Subgroup.commutator_eq_self
  have hbot : A'.map f = ⊥ := by
    calc
      A'.map f = ⁅A'.map f,A'.map f⁆ := hp.symm
      _ = ⁅A'.map f,(A'.map (MulAut.conj t').toMonoidHom).map f⁆ := congrArg (fun K => ⁅A'.map f,K⁆) he.symm
      _ = (⁅A',A'.map (MulAut.conj t').toMonoidHom⁆).map f := (map_commutator _ _ _).symm
      _ = ⊥ := (Subgroup.map_eq_bot_iff _).mpr hc'
  intro a ha
  have hh : (⟨a,hAN ha⟩ : N) ∈ f.ker :=
    ((map_le_iff_le_comap).mp hbot.le) ha
  rwa [Subgroup.normalizerMonoidHom_ker] at hh

end Theory.GroupTheory
