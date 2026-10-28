module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ModuleComparison
public import Theory.Representation.BinaryPermutation.CubicFixedSpace.Five

/-!
# The alternating-five fixed-space obstruction

A normal elementary subgroup containing the source seed has no cubic
enlargement of the fixed space of its Sylow two-subgroup: any such element
would centralize the seed, whose actual centralizer is that Sylow subgroup.
The natural alternating-five section gives precisely such an enlargement,
even with central extensions below and above the section.

The theorem retains the actual embedding of A₅ in the core quotient and
the equivariant section map. Deriving these witnesses from an A₅-block in
C.2.7 is a separate obligation; a named block is not identified with an
unrelated permutation action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.2.7(3),
printed p.145, and the module comparison in 15.4.20, printed p.1164.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative

variable {H : Type*} [Group H] [Finite H]

/-- The actual Sylow seed centralizer excludes a natural A₅ central section.
No splitting of either extension around that section is assumed. -/
theorem not_alternatingFive_centralSection
    (V Z : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
    (hc : centralizer (V : Set H) = pCore 2 H) (hZV : Z ≤ V)
    (P : Sylow 2 H) (hCZ : centralizer (Z : Set H) = (P : Subgroup H))
    (f : alternatingGroup (Fin 5) →* (H ⧸ pCore 2 H)) (hf : Function.Injective f)
    (W : Subrepresentation ((coreAction V hc).comp f))
    (q : W.toSubmodule →ₗ[ZMod 2] BinaryPermutation.natural (Fin 5))
    (hq : ∀ g w, q (W.toRepresentation g w) =
      BinaryPermutation.naturalRepresentation (Fin 5) g.val (q w))
    (hker : ∀ g w, q w = 0 → W.toRepresentation g w = w)
    (hquot : ∀ g v, coreAction V hc (f g) v - v ∈ W) : False := by
  let S := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  obtain ⟨g, hg, _, hfix⟩ := BinaryPermutation.CubicFixedSpace.Five.centralSection_enlargement
    (coreAction V hc) f hf W q hq hker hquot S
  exact no_fixedSpace_enlargement V Z hc hZV P hCZ g hg hfix

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve
