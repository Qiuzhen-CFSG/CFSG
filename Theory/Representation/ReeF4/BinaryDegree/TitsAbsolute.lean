module

public import Theory.Representation.ReeF4.BinaryDegree.TitsAbsolute.Coinduction
public import Theory.Representation.Quotient
public import Theory.SpecificGroups.ReeF4.DerivedTits
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure


/-!
# Reducing the absolute Tits minimum to binary Ree modules

The certified equivalence between the derived subgroup of `Model 0` and
Parrott's group, together with the certified ambient order bound, gives
index at most two. Coinduction then reduces the absolute degree-26 minimum
to two representation-theoretic inputs for the full binary Ree group:

* an irreducible of degree below 52 is trivial or has degree 26;
* an irreducible of degree 26 stays irreducible on the derived subgroup.

Both inputs remain explicit premises. The theorem below proves their
transfer to the actual Parrott carrier; it does not assert that either
input, or the unconditional Tits degree minimum, has been established.
In particular it does not transfer a full-group degree bound to a subgroup
without a restriction argument.

Sources: Aschbacher--Smith, *The Classification of Quasithin Groups*, printed
p.356 (PDF p.367), and GLS3 §2.8. The group comparison uses the certified
Parrott realization and Bruhat bound in `Theory.SpecificGroups.ReeF4.DerivedTits`.
-/

public section

namespace ReeF4.BinaryDegree.TitsAbsolute

open Representation
universe v

/-- The certified derived-group comparison and ambient order bound give index
at most two in the full binary Ree group. -/
theorem derived_index_le_two : (commutator (Model 0)).index ≤ 2 := by
  obtain ⟨e⟩ := DerivedTits.nonempty_derived_equiv
  have hc : Nat.card (commutator (Model 0)) = 17971200 :=
    (Nat.card_congr e.toEquiv).trans Tits.parrottGroup_card
  have hi := (commutator (Model 0)).card_mul_index
  have hb := DerivedTits.binary_card_le
  rw [hc] at hi
  omega


set_option backward.isDefEq.respectTransparency false in
/-- The two concrete binary-Ree representation inputs imply the absolute
minimum for every faithful irreducible action of the Parrott group. -/
theorem degree_ge_of_binary_ree_inputs
    (hsmall : ∀ (E : Type v) [Field E] [Finite E] [CharP E 2]
      (V : Type v) [AddCommGroup V] [Module (AlgebraicClosure E) V]
      [FiniteDimensional (AlgebraicClosure E) V]
      (τ : Representation (AlgebraicClosure E) (Model 0) V),
      τ.IsIrreducible → Module.finrank (AlgebraicClosure E) V < 52 →
        τ.IsTrivial ∨ Module.finrank (AlgebraicClosure E) V = 26)
    (hrestrict : ∀ (E : Type v) [Field E] [Finite E] [CharP E 2]
      (V : Type v) [AddCommGroup V] [Module (AlgebraicClosure E) V]
      [FiniteDimensional (AlgebraicClosure E) V]
      (τ : Representation (AlgebraicClosure E) (Model 0) V),
      τ.IsIrreducible → Module.finrank (AlgebraicClosure E) V = 26 →
        Representation.IsIrreducible (k := AlgebraicClosure E)
          (G := commutator (Model 0)) (V := V)
          (τ.comp (commutator (Model 0)).subtype))
    (E : Type v) [Field E] [Finite E] [CharP E 2]
    (W : Type v) [AddCommGroup W] [Module (AlgebraicClosure E) W]
    [FiniteDimensional (AlgebraicClosure E) W]
    (σ : Representation (AlgebraicClosure E) Tits.ParrottGroup W)
    (hσ : σ.IsIrreducible) (hf : Function.Injective σ) :
    26 ≤ Module.finrank (AlgebraicClosure E) W := by
  obtain ⟨e⟩ := DerivedTits.nonempty_derived_equiv
  let ρ : Representation (AlgebraicClosure E) (commutator (Model 0)) W :=
    σ.comp e.toMonoidHom
  let : Representation.IsIrreducible (k := AlgebraicClosure E)
      (G := commutator (Model 0)) (V := W) ρ :=
    (Representation.irreducible_comp_surjective_iff
      (F := AlgebraicClosure E) (G := commutator (Model 0))
      (Q := Tits.ParrottGroup) (V := W) e.toMonoidHom e.surjective σ).mpr hσ
  apply minimum_of_small_ambient_catalogue
    (F := AlgebraicClosure E) (G := Model 0) (W := W) (commutator (Model 0)) ρ 26
    derived_index_le_two (hsmall E) (hrestrict E)
  intro ht
  let := ht
  have htr (g : Tits.ParrottGroup) : σ g = 1 := by
    obtain ⟨x, rfl⟩ := e.surjective g
    exact Representation.isTrivial_def ρ x
  have hall (g : Tits.ParrottGroup) : g = 1 := hf ((htr g).trans (map_one σ).symm)
  obtain ⟨g, hg⟩ := exists_ne (1 : Tits.ParrottGroup)
  exact hg (hall g)

end ReeF4.BinaryDegree.TitsAbsolute
