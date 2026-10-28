module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases

/-!
# A twice-transitive spanning orbit over the binary field

If an orbit spans a binary representation and contains every nonzero vector
of a subspace of dimension greater than one, then two-transitivity forces it
to contain every nonzero vector of the representation. Indeed, move two
independent vectors of that subspace to any prescribed distinct orbit points;
their sum is again in the orbit. Thus adjoining zero gives a subspace, which
must be the whole space by the spanning assumption.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma B.4.12(1), printed pp. 96–97.
-/

public section

open Module
namespace Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- A twice-transitive spanning orbit containing a nonzero plane is all nonzero vectors.
The two-transitivity hypothesis is written on the orbit as a set of vectors. -/
theorem orbit_eq_nonzero_of_pair_transitive (ρ : Representation (ZMod 2) G V) (v : V)
    (hspan : Submodule.span (ZMod 2) (Set.range fun g => ρ g v) = ⊤)
    (U : Submodule (ZMod 2) V) (hU : 1 < finrank (ZMod 2) U)
    (hUorb : ∀ u ∈ U, u ≠ 0 → u ∈ Set.range (fun g => ρ g v))
    (htrans : ∀ a ∈ Set.range (fun g => ρ g v),
      ∀ b ∈ Set.range (fun g => ρ g v), a ≠ b →
      ∀ c ∈ Set.range (fun g => ρ g v),
      ∀ d ∈ Set.range (fun g => ρ g v), c ≠ d →
      ∃ g : G, ρ g a = c ∧ ρ g b = d) :
    Set.range (fun g => ρ g v) = {w : V | w ≠ 0} := by
  classical
  let : Nontrivial U := Module.nontrivial_of_finrank_pos (by omega : 0 < finrank (ZMod 2) U)
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  obtain ⟨w, huw⟩ := exists_linearIndependent_pair_of_one_lt_finrank hU hu
  have hw : w ≠ 0 := by simpa using huw.ne_zero (1 : Fin 2)
  have hne : u ≠ w := by
    intro h
    have hi := huw.injective (show (![u,w] : Fin 2 → U) 0 = ![u,w] 1 by simpa using h)
    exact Fin.zero_ne_one hi
  have hu0 : (u : V) ≠ 0 := fun h => hu (Subtype.ext h)
  have hw0 : (w : V) ≠ 0 := fun h => hw (Subtype.ext h)
  have huwne : (u : V) ≠ w := fun h => hne (Subtype.ext h)
  have huorb := hUorb u u.property hu0
  have hworb := hUorb w w.property hw0
  have hsum0 : (u : V) + w ≠ 0 := by
    rw [← ZModModule.sub_eq_add]
    exact sub_ne_zero.mpr huwne
  obtain ⟨t, ht⟩ := hUorb ((u : V) + w) (U.add_mem u.property w.property) hsum0
  change ρ t v = (u : V) + w at ht
  have hv : v ≠ 0 := by
    intro h
    obtain ⟨g,hg⟩ := huorb
    exact hu0 (by simpa [h] using hg.symm)
  let S : Submodule (ZMod 2) V := {
    carrier := {x | x = 0 ∨ x ∈ Set.range (fun g => ρ g v)}
    zero_mem' := Or.inl rfl
    add_mem' := by
      intro a b ha hb
      rcases ha with rfl | ha
      · simpa using hb
      rcases hb with rfl | hb
      · simpa using (Or.inr ha : a = 0 ∨ a ∈ Set.range (fun g => ρ g v))
      by_cases hab : a = b
      · subst b
        exact Or.inl (ZModModule.add_self a)
      · obtain ⟨g, hga, hgb⟩ := htrans u huorb w hworb huwne a ha b hb hab
        right
        refine ⟨g * t, ?_⟩
        change ρ (g * t) v = a + b
        rw [ρ.map_mul, Module.End.mul_apply, ht, map_add, hga, hgb]
    smul_mem' := by
      intro c a ha
      fin_cases c
      · change (0 : ZMod 2) • a = 0 ∨ _
        exact Or.inl (zero_smul _ _)
      · change (1 : ZMod 2) • a = 0 ∨ (1 : ZMod 2) • a ∈ Set.range (fun g => ρ g v)
        change a = 0 ∨ a ∈ Set.range (fun g => ρ g v) at ha
        simpa only [one_smul] using ha }
  have htop : S = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact Submodule.span_le.mpr (fun _ hx => Or.inr hx)
  ext a
  constructor
  · rintro ⟨g, rfl⟩ h
    apply hv
    have he := congrArg (ρ g⁻¹) h
    simpa [← Module.End.mul_apply, ← map_mul] using he
  · intro ha
    have hm : a ∈ S := by rw [htop]; trivial
    exact hm.resolve_left ha
end Representation
