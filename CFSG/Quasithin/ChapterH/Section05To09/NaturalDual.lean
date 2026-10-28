module

public import Theory.Representation.BinaryNaturalDual
public import Theory.Representation.BinaryNaturalDual.FiveActors.Hyperplanes
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.GeneratedCore
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.ModelOrbits
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.VectorStabilizers
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.FiveActors
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.FourActors
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceAdaptedPair
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceStabilizers
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceSylowMarking
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceAssembly

/-!
# Natural-plus-dual calculations for H.9

The imports supply the complete coordinate form, orbit, stabilizer and
elementary-actor calculations, including the actual E.3.30 generated cores.
The source model is constructed from the standing group and natural-module
hypotheses. `SourceSetup.adapted_pair` discharges the corrected simultaneous
vector/actor transport on the original module, with the actual residual and
commutator space. `SourceStabilizers` transports the pure split extension and
nonsingular group and complementary-action identifications.
`SourceSylowMarking` proves the unchanged pure-vector Sylow clause on the
source natural summand.

`SourceAssembly` completes H.9.1 on the original group and module, including
the pure quotient's exact action, both commutator spaces, and the separately
named `SourceSetup.lemma_H_9_1_4_adequate`. Its orthogonal decompositions and
natural/dual actions use the literal source summands. The source H.9.2–3
actor families are re-exported through `SourceFiveActors` and
`SourceFourActors`, with the given Sylow marking, actual relative centralizers,
conjugacy classifications, transvections and E.3.30 generated cores.

There is a compatibility problem with the literal fixed-Sylow clauses of
H.9.1. Part (3) fixes `v₁` under `T₁`. Since `T₁` has index two in `T`, its
orbit under `T` consists of two vectors. If an element of `T - T₁` swaps the
summands and fixes `v₁ + v₂`, then these two vectors are precisely `v₁,v₂`.
Their sum is fixed by all of `T`, hence singular by part (2), contrary to
part (4). The theorem below certifies this incompatibility. It is a diagnostic,
not a replacement statement or a proof of all of H.9.1.

Here the group `T` is the source's Sylow two-subgroup, with its restricted
linear action. The quadratic-form premise is exactly the implication from
Sylow fixation to singularity in part (2), extended to zero using `q(0)=0`.
The action on the two summands makes their stabilizer `T₁` an index-two
subgroup. The preserved diagnostic below remains separate from the imported classification results.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.1(2–4),
printed p.390, PDF p.401. The PDF specifies `t ∈ Tᵥ - T₁` and
`Tᵥ := C_T(v) ∈ Syl₂(Mᵥ)`. The corrected contract of 6 October 2026 chooses
an adapted nonsingular vector and transports its actor together with it;
it does not retain the pure-vector marking of part (3) in part (4).
-/

public section

namespace CFSG.Quasithin.ChapterH.NaturalDual

variable {T V : Type*} [Group T] [AddCommGroup V] [Module (ZMod 2) V]

/-- The nonsingular vector in H.9.1(4) cannot be fixed by an element outside
`T₁` in the same Sylow subgroup used to choose `v₁` in part (3).

The hypotheses explicitly exhibit the elementary incompatibility with part
(2); this theorem does not claim the source hypotheses have been assembled. -/
theorem no_outer_fixed_nonsingular_sum
    (ρ : T →* (V ≃ₗ[ZMod 2] V)) (T₁ : Subgroup T) (hindex : T₁.index = 2)
    (U W : Submodule (ZMod 2) V) (hUW : IsCompl U W)
    (q : QuadraticForm (ZMod 2) V)
    (hsingular : ∀ v : V, (∀ t : T, ρ t v = v) → q v = 0)
    {u w : V} (hu : u ∈ U) (hw : w ∈ W)
    (huFixed : ∀ t ∈ T₁, ρ t u = u)
    (hnonsingular : q (u + w) ≠ 0)
    {t : T} (ht : t ∉ T₁)
    (hU : ∀ x ∈ U, ρ t x ∈ W) (hW : ∀ x ∈ W, ρ t x ∈ U) :
    ρ t (u + w) ≠ u + w := by
  intro hfix
  have hswap := (BinaryNaturalDual.swaps_components hUW (ρ t) hU hW hu hw hfix).1
  exact hnonsingular (hsingular (u + w)
    (BinaryNaturalDual.fixed_by_index_two_swap ρ T₁ hindex ht huFixed hswap))

end CFSG.Quasithin.ChapterH.NaturalDual
