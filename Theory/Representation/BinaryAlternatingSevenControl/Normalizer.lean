module

public import Theory.Representation.BinaryAlternatingSevenControl.FixedLine
public import Theory.LinearAlgebra.BinaryFourAlternatingEight
public import Theory.Alternating.IndexEightSubgroups
/-!
# Normal A₇ actors on a binary four-space

A faithful A₇ image has index eight in GL₄(2) ≃ A₈. The proved index-eight
subgroup theorem therefore makes it self-normalizing. Consequently a faithful
four-dimensional binary action cannot have a proper normal A₇ subgroup.
The final theorem retains the arbitrary acting group and the actual normal
subgroup, matching the centralizer quotient in C.1.23(2), printed p.130.
-/

public section

open Subgroup Representation.BinaryOffender
namespace Representation.BinaryAlternatingSevenControl
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem actionImage_self_normalizing (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4) :
    normalizer (actionImage ρ : Set (Module.End (ZMod 2) V)ˣ) = actionImage ρ := by
  let e := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).trans
    (BinaryFourAlternatingEight.linearEquivAlternatingEight hd)
  let H := (actionImage ρ).map e.toMonoidHom
  have hi : Function.Injective ρ.asGroupHom := fun a b hab => hf (congrArg Units.val hab)
  have hc : Nat.card H = 2520 := by
    rw [card_map_of_injective e.injective]
    rw [actionImage, ← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hindex : H.index = 8 := by
    have hh := H.card_mul_index
    rw [hc,nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh
    omega
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [map_equiv_normalizer_eq]
  exact GroupTheory.AlternatingIndexEight.index_eight_normalizer H hindex

theorem normal_alternatingSeven_eq_top
    {H : Type*} [Group H] [Finite H]
    (ρ : Representation (ZMod 2) H V) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 4)
    (N : Subgroup H) [N.Normal] (e : N ≃* A7) : N = ⊤ := by
  let σ : Representation (ZMod 2) A7 V := ρ.comp (N.subtype.comp e.symm.toMonoidHom)
  have hσ : Function.Injective σ := hf.comp (Subtype.val_injective.comp e.symm.injective)
  have hr : actionImage σ = N.map ρ.asGroupHom := by
    have he : σ.asGroupHom = ρ.asGroupHom.comp (N.subtype.comp e.symm.toMonoidHom) := by
      apply MonoidHom.ext
      intro g
      apply Units.ext
      rfl
    rw [actionImage,he]
    rw [MonoidHom.range_comp,MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr e.symm.surjective,← MonoidHom.range_eq_map,Subgroup.range_subtype]
  have hn := actionImage_self_normalizing σ hσ hd
  rw [hr] at hn
  apply top_unique
  intro x _
  have hx : ρ.asGroupHom x ∈ normalizer (N.map ρ.asGroupHom : Set (Module.End (ZMod 2) V)ˣ) :=
    N.le_normalizer_map ρ.asGroupHom (mem_map_of_mem _ (by rw [N.normalizer_eq_top]; trivial))
  rw [hn] at hx
  obtain ⟨n,hn,hne⟩ := hx
  have heq : n = x := hf (congrArg Units.val hne)
  rwa [heq] at hn

end Representation.BinaryAlternatingSevenControl
