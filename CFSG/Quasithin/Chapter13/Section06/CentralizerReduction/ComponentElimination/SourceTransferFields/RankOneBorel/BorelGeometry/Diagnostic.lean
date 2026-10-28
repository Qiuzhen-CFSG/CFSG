module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry

/-!
# The marked Sylow point is central only in the checked quotient

In the source five-point A₅ module, the involution (12)(34) fixes z and v
and sends a to a+v. Consequently a subgroup containing a lift of that
involution cannot fix a itself. The transport theorem applies to the actual
A5Module.Marking and retains its original action homomorphism.

This is an obstruction to inferring full-Borel fixation from the marked
quotient geometry. It is not a counterexample to the complete 13.6.18
setup, whose additional component and ambient hypotheses are stronger.
The residual/checked fixation in BorelGeometry remains available for an
adequate source route.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the coordinate choices before 13.6.4--5, printed p.926, and the
full-Borel sentence in the proof of 13.6.18, printed p.931.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Diagnostic
variable {G : Type*} [Group G] [Finite G]
open BinaryPermutation.FiveCentralizerGeometry
/-- The source's double transposition in the five-letter A₅ action. -/
def reflection : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩

theorem reflection_involution : reflection ^ 2 = 1 := by decide +kernel

theorem reflection_fixes_z_v : act reflection z = z ∧ act reflection v = v := by
  constructor <;> apply Subtype.ext <;> ext i <;> fin_cases i <;> decide

/-- Centrality modulo the source v-line is strictly weaker than fixation:
the displayed Sylow involution sends a to a+v. -/
theorem reflection_moves_a : act reflection a = a + v ∧ act reflection a ≠ a := by
  constructor
  · apply Subtype.ext
    ext i
    fin_cases i <;> decide
  · intro h
    have he := congrArg (fun x : Space => x.val 0) h
    exact (by decide : (0 : ZMod 2) ≠ 1) he

omit [Finite G] in
/-- In an actual marked action containing that involution, every subgroup
containing the marked Sylow actor fails to centralize the specified a.
This diagnoses the proposed local full-Borel assertion, not the complete
source counterexample setup. -/
theorem not_full_borel_fixation
    {L V T B : Subgroup G} (s : A5Module.Marking L V)
    (t : L) (ht : (t : G) ∈ T) (hT : T ≤ B)
    (hact : s.action t = reflection) :
    ¬ B ≤ centralizer ({A5Module.markedA s} : Set G) := by
  intro hB
  have hc := mem_centralizer_singleton_iff.mp (hB (hT ht))
  have he := s.equivariant t a
  rw [hact] at he
  have hf : MulAut.conj (t : G) (A5Module.markedA s) = A5Module.markedA s :=
    mul_inv_eq_iff_eq_mul.mpr hc
  have hm := s.injective (he.symm.trans hf)
  exact reflection_moves_a.2 (congrArg Multiplicative.toAdd hm)
omit [Finite G] in
/-- The same marked involution obstructs the printed equality of full
Borel images. The actual residual L_v fixes a by the already proved A₅
module calculation; no separate fixation premise is added here. -/
theorem not_full_borel_product_eq
    {L V T B : Subgroup G} (M : Subgroup G) (s : A5Module.Marking L V)
    (t : L) (ht : (t : G) ∈ T) (hT : T ≤ B)
    (hact : s.action t = reflection) :
    B ⊔ (M ⊓ centralizer (V : Set G)) ≠
      Lv L (A5Module.markedV s) ⊔ (M ⊓ centralizer (V : Set G)) := by
  intro he
  apply not_full_borel_fixation s t ht hT hact
  have ha := A5Module.markedA_mem_centralizer s
  have hB : B ≤ Lv L (A5Module.markedV s) ⊔ (M ⊓ centralizer (V : Set G)) :=
    he ▸ (show B ≤ B ⊔ (M ⊓ centralizer (V : Set G)) from le_sup_left)
  apply hB.trans (sup_le ?_ ?_)
  · intro l hl
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp ha.2 l hl)
  · exact inf_le_right.trans (centralizer_le (Set.singleton_subset_iff.mpr ha.1))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Diagnostic
