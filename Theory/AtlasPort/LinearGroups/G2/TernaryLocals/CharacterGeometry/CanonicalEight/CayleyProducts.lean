module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.CanonicalEight.NormLines
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!+# Cayley products for the canonical eight construction

The ordered products `(1,a,b,ab,c,ac,bc,(ab)c)` specify the frame convention.
Changing the sign of `a` changes precisely the odd-indexed products. The
lemmas here reduce the required extension to realization of that sign change
on an actual spanning frame of the canonical lines. They do not assert that
an arbitrary linear sign change preserves octonion multiplication.

The convention agrees with the licensed ATLAS octonion port and the concrete
frame in `ElementaryEight.CayleyFrame`; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. Application: Aschbacher–Smith,
*The Classification of Quasithin Groups*, Theorem 0.1.2(4).
-/

@[expose] public section

namespace Atlas.G2.TernaryLocals.CharacterGeometry.CanonicalEight
open Atlas.SplitOctonion

/-- The parenthesization is part of the frame convention. -/
def cayleyProducts (a b c : V) : Fin 8 → V :=
  ![unit, a, b, mul a b, c, mul a c, mul b c, mul (mul a b) c]

/-- The proposed sign change of the first Cayley generator. -/
def firstSign (i : Fin 8) : ZMod 3 := if i.val % 2 = 0 then 1 else -1

theorem firstSign_cases (i : Fin 8) : firstSign i = 1 ∨ firstSign i = -1 := by
  unfold firstSign
  split <;> simp

/-- Eight independent Cayley products span the actual eight-dimensional algebra. -/
theorem cayleyProducts_span (a b c : V)
    (hlin : LinearIndependent (ZMod 3) (cayleyProducts a b c)) :
    Submodule.span (ZMod 3) (Set.range (cayleyProducts a b c)) = ⊤ :=
  hlin.span_eq_top_of_card_eq_finrank (by simp [V, Carrier])

/-- A selected Cayley basis discharges the spanning premise of the norm-line reduction. -/
theorem selected_span_of_cayleyProducts (E : Subgroup G) (a b c : V)
    (hlin : LinearIndependent (ZMod 3) (cayleyProducts a b c))
    (hsel : ∀ i, cayleyProducts a b c i ∈ selected E) :
    Submodule.span (ZMod 3) (selected E) = ⊤ := by
  apply top_unique
  rw [← cayleyProducts_span a b c hlin]
  exact Submodule.span_mono (by rintro _ ⟨i,rfl⟩; exact hsel i)

/-- Realizing the sign change as an actual automorphism makes it fix all
selected lines, provided the frame exhausts them. -/
theorem mem_candidate_of_cayley_signs (E : Subgroup G) (a b c : V)
    (hexhaust : ∀ x ∈ selected E, ∃ i : Fin 8, ∃ r : ZMod 3,
      x = r • cayleyProducts a b c i)
    (g : G) (hg : ∀ i, g.val (cayleyProducts a b c i) =
      firstSign i • cayleyProducts a b c i) : g ∈ candidate E := by
  intro x hx
  obtain ⟨i,r,rfl⟩ := hexhaust x hx
  rcases firstSign_cases i with hs | hs
  · left
    rw [map_smul, hg, hs, one_smul]
  · right
    rw [map_smul, hg, hs, neg_one_smul, smul_neg]

/-- The geometric Cayley route to the requested normalizer-invariant extension.
Frame existence and multiplicativity of the sign change are explicit premises,
to be proved before this reduction yields the unconditional extension theorem. -/
theorem extension_of_cayley_frame_flip (E : Subgroup G) (hE : Nat.card E = 4)
    (a b c : V) (ha : a ∈ characterSpace E 1)
    (hlin : LinearIndependent (ZMod 3) (cayleyProducts a b c))
    (hsel : ∀ i, cayleyProducts a b c i ∈ selected E)
    (hexhaust : ∀ x ∈ selected E, ∃ i : Fin 8, ∃ r : ZMod 3,
      x = r • cayleyProducts a b c i)
    (g : G) (hg : ∀ i, g.val (cayleyProducts a b c i) =
      firstSign i • cayleyProducts a b c i) :
    ∃ F : Subgroup G, IsElementaryAbelian 2 F ∧ Nat.card F = 8 ∧
      E ≤ F ∧ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (F : Set G) := by
  apply extension_of_span_of_moving_fixed E hE
    (selected_span_of_cayleyProducts E a b c hlin hsel)
  refine ⟨g, mem_candidate_of_cayley_signs E a b c hexhaust g hg, a, ha, ?_⟩
  have hga : g.val a = -a := by simpa [cayleyProducts, firstSign] using hg 1
  have han : a ≠ 0 := selected_ne_zero E (hsel 1)
  intro h
  apply han
  have hz : (2 : ZMod 3) • a = 0 := by
    calc
      _ = a + a := by module
      _ = g.val a + a := congrArg (fun y : V => y + a) h.symm
      _ = 0 := by rw [hga, neg_add_cancel]
  exact (smul_eq_zero.mp hz).resolve_left (by decide)

end Atlas.G2.TernaryLocals.CharacterGeometry.CanonicalEight
