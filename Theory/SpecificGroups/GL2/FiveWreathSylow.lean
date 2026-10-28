module
public import Theory.SpecificGroups.GL2.FiveWreathSylow.Monomial

/-!
# Sylow two-subgroups of GL₂(5) are C₄ wr C₂

The explicit monomial subgroup has order 32, whereas GL₂(5) has order 480.
Its index is therefore 15, making it Sylow. Sylow conjugacy transports the
literal cyclic-four wreath model to every Sylow two-subgroup. More
generally, an injective map from a group of order 32 has Sylow image and
therefore gives the same group isomorphism directly.

The final theorem is the consumer for the faithful action on the Frattini
quotient of the actual extraspecial group of order 125 in Aschbacher–Smith
J.3.6, printed p.439. That source concludes R ≅ Z₄ wr Z₂; the matrix
construction here supplies this model without a recognition premise.
-/

@[expose] public noncomputable section
namespace Matrix.GeneralLinearGroup.FiveWreathSylow
open scoped Matrix
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem generalLinear_card : Nat.card (GL (Fin 2) (ZMod 5)) = 480 := by
  rw [Matrix.card_GL_field]
  norm_num [Fin.prod_univ_two]

theorem index_of_card32 (T : Subgroup (GL (Fin 2) (ZMod 5))) (hc : Nat.card T = 32) :
    T.index = 15 := by
  have hh := T.card_mul_index
  rw [hc,generalLinear_card] at hh
  omega

def sylowOfCard32 (T : Subgroup (GL (Fin 2) (ZMod 5))) (hc : Nat.card T = 32) :
    Sylow 2 (GL (Fin 2) (ZMod 5)) :=
  (IsPGroup.of_card (p:=2) (n:=5) hc).toSylow (by
    rw [index_of_card32 T hc]
    decide)

def monomialSylow : Sylow 2 (GL (Fin 2) (ZMod 5)) :=
  sylowOfCard32 monomialSubgroup monomialSubgroup_card

@[simp] theorem monomialSylow_coe :
    (monomialSylow : Subgroup (GL (Fin 2) (ZMod 5))) = monomialSubgroup := rfl

def sylowWreathEquiv (S : Sylow 2 (GL (Fin 2) (ZMod 5))) :
    S ≃* RegularWreathProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2)) :=
  (S.equiv monomialSylow).trans wreathSubgroupEquiv.symm

/-- Every actual Sylow two-subgroup of GL₂(5) is the literal C₄ wr C₂. -/
theorem sylow_equiv_wreath (S : Sylow 2 (GL (Fin 2) (ZMod 5))) :
    Nonempty (S ≃* RegularWreathProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2))) :=
  ⟨sylowWreathEquiv S⟩

/-- Apply the model directly to an injective source quotient action of order 32. -/
theorem wreath_equiv_of_injective_card32 {R : Type*} [Group R]
    (f : R →* GL (Fin 2) (ZMod 5)) (hf : Function.Injective f) (hc : Nat.card R = 32) :
    Nonempty (R ≃* RegularWreathProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2))) := by
  have hr : Nat.card f.range = 32 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hc
  exact ⟨(MonoidHom.ofInjective hf).trans (sylowWreathEquiv (sylowOfCard32 f.range hr))⟩

end Matrix.GeneralLinearGroup.FiveWreathSylow
