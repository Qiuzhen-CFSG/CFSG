module
public import Theory.SpecificGroups.GL2.PrimeThreeFiveResidual.Line
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness

/-!
# Marked prime-plane actions

A basis of an elementary abelian group of order p² identifies it with
the additive prime plane and identifies its full automorphism group with
GL₂(p). The evaluation equation preserves the original action, so the
two-core irreducibility calculation applies to an actual Frattini action.

Source application: Aschbacher--Smith 15.4.10, printed p.1159.
-/

public section
open Subgroup Matrix
open scoped IsMulCommutative
namespace Matrix.GeneralLinearGroup.PrimeThreeFiveResidual

private def planeAutAdd {p : ℕ} (a : MulAut (Multiplicative (Fin 2 → ZMod p))) :
    (Fin 2 → ZMod p) ≃+ (Fin 2 → ZMod p) where
  toFun v := (a (Multiplicative.ofAdd v)).toAdd
  invFun v := (a.symm (Multiplicative.ofAdd v)).toAdd
  left_inv v := a.left_inv v
  right_inv v := a.right_inv v
  map_add' v w := a.map_mul v w

private def planeAutLinear (p : ℕ) :
    MulAut (Multiplicative (Fin 2 → ZMod p)) ≃*
      ((Fin 2 → ZMod p) ≃ₗ[ZMod p] (Fin 2 → ZMod p)) where
  toFun a := { planeAutAdd a with map_smul' := ZMod.map_smul (planeAutAdd a) }
  invFun a := a.toAddEquiv.toMultiplicative
  left_inv a := by ext; rfl
  right_inv a := by ext; rfl
  map_mul' a b := by ext; rfl

private def planeActionEquiv (p : ℕ) : GL (Fin 2) (ZMod p) ≃*
    MulAut (Multiplicative (Fin 2 → ZMod p)) :=
  GeneralLinearGroup.toLin.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Fin 2 → ZMod p)).trans
      (planeAutLinear p).symm)

/-- Coordinates of an elementary abelian prime plane and all its automorphisms,
with the evaluation marking needed for restriction to an actual actor. -/
theorem exists_plane_coordinates {p : ℕ} [Fact p.Prime]
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian p V]
    (hc : Nat.card V = p ^ 2) :
    ∃ (c : V ≃* Multiplicative (Fin 2 → ZMod p)) (e : MulAut V ≃* GL (Fin 2) (ZMod p)),
      ∀ a v, planeAction p (e a) (c v) = c (a v) := by
  classical
  have hpow : p ^ Module.finrank (ZMod p) (Additive V) = p ^ 2 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive V)
    change Nat.card V = _ at hsize
    simpa only [Nat.card_zmod, hc] using hsize.symm
  have hdim : Module.finrank (ZMod p) (Additive V) = 2 :=
    Nat.pow_right_injective (Fact.out : p.Prime).one_lt hpow
  let b := Module.finBasisOfFinrankEq (ZMod p) (Additive V) hdim
  let c : V ≃* Multiplicative (Fin 2 → ZMod p) := b.equivFun.toAddEquiv.toMultiplicativeRight
  let e := (MulAut.congr c).trans (planeActionEquiv p).symm
  refine ⟨c, e, ?_⟩
  intro a v
  change planeActionEquiv p ((planeActionEquiv p).symm (MulAut.congr c a)) (c v) = _
  rw [(planeActionEquiv p).apply_symm_apply]
  change c (a (c.symm (c v))) = _
  rw [c.symm_apply_apply]

/-- The original two-core is irreducible on an actual prime plane. -/
theorem core_irreducible_on_plane {p : ℕ} [Fact p.Prime] (hp : p = 3 ∨ p = 5)
    {X V : Type*} [Group X] [Finite X] [Group V] [Finite V] [IsElementaryAbelian p V]
    (hc : Nat.card V = p ^ 2) (hX : IsPPerfect 2 X)
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3) (a : X →* MulAut V)
    (hne : (pCore 2 X).map a ≠ ⊥) (B : Subgroup V)
    (hinv : ∀ x ∈ pCore 2 X, ∀ b ∈ B, a x b ∈ B) : B = ⊥ ∨ B = ⊤ := by
  obtain ⟨c, e, he⟩ := exists_plane_coordinates hc
  let f := e.toMonoidHom.comp a
  have hf : (pCore 2 X).map f ≠ ⊥ := by
    intro hb
    apply hne
    apply eq_bot_iff.mpr
    rintro _ ⟨x, hx, rfl⟩
    apply e.injective
    simpa only [map_one] using mem_bot.mp (hb ▸ mem_map_of_mem f hx)
  have hi : ∀ x ∈ pCore 2 X, ∀ v ∈ B.map c.toMonoidHom,
      planeAction p (f x) v ∈ B.map c.toMonoidHom := by
    rintro x hx v ⟨b, hb, rfl⟩
    change planeAction p (e (a x)) (c b) ∈ _
    rw [he]
    exact mem_map_of_mem c.toMonoidHom (hinv x hx b hb)
  rcases core_irreducible hp hX hX3 f hf _ hi with hb | ht
  · left
    apply Subgroup.map_injective (f := c.toMonoidHom) c.injective
    simpa only [Subgroup.map_bot] using hb
  · right
    apply Subgroup.map_injective (f := c.toMonoidHom) c.injective
    rw [← MonoidHom.range_eq_map, (MonoidHom.range_eq_top (f := c.toMonoidHom)).mpr c.surjective]
    exact ht

end Matrix.GeneralLinearGroup.PrimeThreeFiveResidual
