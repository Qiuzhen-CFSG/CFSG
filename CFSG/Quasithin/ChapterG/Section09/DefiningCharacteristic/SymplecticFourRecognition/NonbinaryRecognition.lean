module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Models
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.OrbitDegrees
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.TensorModels
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.AbsoluteCatalogue
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.BinaryDescent

/-!
# Binary spectrum and natural-module recognition for Sp₄(2ⁿ), n ≥ 2

Every faithful irreducible binary representation of the literal derived
symplectic matrix group is quasiequivalent to its natural module, or has
degree at least 16n, or has degree at least 8n with n even. Consequently the
degree window 6n+2 forces genuine natural-module quasiequivalence and degree 4n.

The absolute catalogue includes both four-dimensional basic modules, using
the natural and exceptional graph factors. Binary descent through the actual
Schur field gives periodic tensor parameters. The orbit arithmetic proves
the gap, while a one-factor intertwiner and an actual graph automorphism
give the group and linear isomorphisms in the natural-module conclusion.
The unconditional assembly below discharges the catalogue premise; it needs
no ambient G.9 setup or automorphism-rank hypothesis.

Sources: Aschbacher--Smith, G.9.3(9) and its proof, printed pp.354,356--357;
GLS3, 2.8.6(a), 2.8.8 and Examples 2.8.10(d).
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary

open Representation

variable {F V : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) (Derived F) V}

/-- Convert an intertwining equivalence to a basic twist into genuine
natural-module quasiequivalence, using the corresponding group automorphism. -/
theorem quasiequivalent_of_basicTwist_equiv {j : ℕ}
    (h : Nonempty (ρ.Equiv (restrictScalars (k := ZMod 2) (basicTwist F j)))) :
    Quasiequivalent ρ (binaryNatural F) := by
  obtain ⟨φ⟩ := h
  refine ⟨graphDerived F ^ j, φ.toLinearEquiv, ?_⟩
  intro g v
  exact IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g v

/-- Conditional assembly of the source degree alternatives. The parameter
and one-factor premises must be established by the representation classification. -/
theorem degree_alternatives_of_tensor_parameters {s t a n : ℕ}
    (ht : 0 < t) (ha : 0 < a) (hn : n = s*t)
    (hd : Module.finrank (ZMod 2) V = s*(4^a)^t)
    (hone : a = 1 → t = 1 → ∃ j : Fin (2*n),
      Nonempty (ρ.Equiv (restrictScalars (k := ZMod 2) (basicTwist F j)))) :
    Quasiequivalent ρ (binaryNatural F) ∨
      16*n ≤ Module.finrank (ZMod 2) V ∨
      (Even n ∧ 8*n ≤ Module.finrank (ZMod 2) V) := by
  rcases orbit_degree_alternatives ht ha hn hd with hsingle | hlarge | ⟨heven, hhalf⟩
  · obtain ⟨j, hj⟩ := hone hsingle.1 hsingle.2
    exact Or.inl (quasiequivalent_of_basicTwist_equiv hj)
  · exact Or.inr (Or.inl hlarge)
  · exact Or.inr (Or.inr ⟨heven, hhalf.ge⟩)

/-- The G.9 degree window eliminates both larger alternatives when n≥2,
given the displayed representation-theoretic inputs. -/
theorem small_quasiequivalent_of_tensor_parameters {s t a n : ℕ}
    (ht : 0 < t) (ha : 0 < a) (hn : n = s*t) (hn2 : 2 ≤ n)
    (hd : Module.finrank (ZMod 2) V = s*(4^a)^t)
    (hone : a = 1 → t = 1 → ∃ j : Fin (2*n),
      Nonempty (ρ.Equiv (restrictScalars (k := ZMod 2) (basicTwist F j))))
    (hsmall : Module.finrank (ZMod 2) V ≤ 6*n+2) :
    Quasiequivalent ρ (binaryNatural F) := by
  rcases degree_alternatives_of_tensor_parameters ht ha hn hd hone with h | h | ⟨_, h⟩
  · exact h
  · omega
  · omega

variable [FiniteDimensional (ZMod 2) V] [ρ.IsIrreducible]

/-- The exhaustive binary degree alternative for the actual derived Sp₄(F),
including both basic four-dimensional modules through quasiequivalence. -/
theorem degree_alternatives {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (hρ : Function.Injective ρ) :
    Quasiequivalent ρ (binaryNatural F) ∨
      16*n ≤ Module.finrank (ZMod 2) V ∨
      (Even n ∧ 8*n ≤ Module.finrank (ZMod 2) V) := by
  obtain ⟨s, t, a, _, ht, ha, hnst, hd, hone⟩ :=
    exists_binary_tensor_parameters ρ hn hF hρ (fun e => absoluteTensorCatalogue e hF hn)
  exact degree_alternatives_of_tensor_parameters ht ha hnst hd hone

/-- Every faithful irreducible binary action in the G.9 degree window is
intertwined with the natural action by genuine group and linear isomorphisms. -/
theorem small_quasiequivalent {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (hρ : Function.Injective ρ) (hsmall : Module.finrank (ZMod 2) V ≤ 6*n+2) :
    Quasiequivalent ρ (binaryNatural F) := by
  rcases degree_alternatives hn hF hρ with h | h | ⟨_, h⟩
  · exact h
  · omega
  · omega

/-- The recognized action has exactly the natural binary degree 4n. -/
theorem small_finrank {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (hρ : Function.Injective ρ) (hsmall : Module.finrank (ZMod 2) V ≤ 6*n+2) :
    Module.finrank (ZMod 2) V = 4*n :=
  finrank_of_quasiequivalent hF (small_quasiequivalent hn hF hρ hsmall)

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary
