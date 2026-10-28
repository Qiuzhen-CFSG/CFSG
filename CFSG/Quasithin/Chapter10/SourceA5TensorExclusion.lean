module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Intrinsic
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Normalizer
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SmallSylow
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Cohomology
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.PlaneTerminal
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MSInputs
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Placement
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OriginalConjugateCartan

/-!
# The checked early branches of the chosen A₅ tensor exclusion

The literal tensor model gives the order, centralizers and full-normalizer
action of the original module. In the nonnormal case its order forces the
original Sylow subgroup to have order greater than256. This closes the
small-Sylow alternatives in the F.1.12 application of9.3.1 once that source
application supplies its bound.

The actual quotient L₀/O₂(L₀) also has vanishing first cohomology. The
plane-radical terminal rules out the marked Sp₄ configuration once source
recognition constructs it.

The SL₃(4) Cartan terminal is proved for both natural-action rows. It uses
the actual conjugate factor A ∩ Lᵗ and retains the original model map and
Cartan orbit; it has no coordinate or section-centralization premise.

The general tensor exclusion still requires the local overcomponent branch
of9.3 and the diagonal point-centralizer argument of9.4.1, followed by the
weak-closure conclusions9.4.2–5. Those are not premises hidden in the model,
and the theorem below explicitly retains the bound for the branch it proves.
Source: Aschbacher–Smith Chapter9, printed pp.729–737.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The small-Sylow conclusion of the source amalgam alternatives is
incompatible with the original nonnormal chosen A₅ tensor configuration. -/
theorem source_a5_tensor_exclusion_of_small_sylow
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hT : Nat.card T ≤ 256) : ¬ Nonempty (SourceA5TensorModel D e) := by
  rintro ⟨m⟩
  exact (not_lt_of_ge hT) (m.sylow_card_gt_256 hn)

end CFSG.Quasithin.Chapter10
