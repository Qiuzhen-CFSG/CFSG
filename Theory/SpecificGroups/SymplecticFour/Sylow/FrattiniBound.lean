module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Frattini
public import Theory.Frattini.OmegaProducts
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SylowPointwiseInner
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.GroupAction.SylowPointwiseInnerTransport

/-!
# Nonbinary symplectic Sylow Frattini subgroups

A Sylow two-subgroup of Sp₄(q), for q > 2 in characteristic two, has
Frattini subgroup equal to its central root group, of order q². Sylow
conjugacy and group equivalences transport that calculation to any actual
Sylow subgroup. Thus a Sylow Frattini subgroup of order at most four rules
out every nonbinary field.

The companion pointwise-fixer theorem transports the proved semilinear
classification along the same group equivalence. These two intrinsic facts
are used in the paired cubic component inspection of Aschbacher–Smith,
2.4.32, printed p.547; its actual source Sylow is placed in the original
Thompson subgroup before applying the bound.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.FrattiniBound
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem frattini_card_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : Nat.card (frattini A) = Nat.card (frattini B) := by
  rw [←frattini_map_equiv e,card_map_of_injective e.injective]

theorem sylow_frattini_card {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (P : Sylow 2 (Sp F)) : Nat.card (frattini P) = (Nat.card F)^2 := by
  have he := frattini_card_equiv (Sylow.equiv P (unipotentSylow hF (by omega)))
  change Nat.card (frattini P) = Nat.card (frattini (unipotent (F := F))) at he
  rw [he,CentralRootGeometry.frattini_eq_center hF hn,
    ←Nat.card_congr (CentralRootGeometry.centerEquiv (F := F)).toEquiv,
    Nat.card_prod]
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F),pow_two]

theorem sylow_frattini_card_of_equiv {A : Type*} [Group A] [Finite A]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : A ≃* Sp F) (P : Sylow 2 A) :
    Nat.card (frattini P) = (Nat.card F)^2 := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let eP : P ≃* Q := (e.subgroupMap (P : Subgroup A))
  exact (frattini_card_equiv eP).trans (sylow_frattini_card hF hn Q)

theorem not_equiv_of_small_sylow_frattini {A : Type*} [Group A] [Finite A]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : A ≃* Sp F) (P : Sylow 2 A) (hPhi : Nat.card (frattini P) ≤ 4) : False := by
  rw [sylow_frattini_card_of_equiv hF hn e P,hF] at hPhi
  have hh : 4 ≤ 2^n := by
    calc
      4 = 2^2 := by decide
      _ ≤ 2^n := Nat.pow_le_pow_right (by decide) (by omega)
  nlinarith

theorem fixing_sylow_inner_of_equiv {A : Type*} [Group A] [Finite A]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) (e : A ≃* Sp F)
    (P : Sylow 2 A) (a : MulAut A) (hfix : ∀ x ∈ P, a x = x) :
    a ∈ (MulAut.conj : A →* MulAut A).range := by
  obtain ⟨x,_,hx⟩ := MulAut.fixing_sylow_inner_of_equiv e
    (DiagramAutomorphisms.aut_fixing_sylow_inner hF hn
      DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram) P a hfix
  exact ⟨x,hx.symm⟩

end Theory.SpecificGroups.SymplecticFour.FrattiniBound
