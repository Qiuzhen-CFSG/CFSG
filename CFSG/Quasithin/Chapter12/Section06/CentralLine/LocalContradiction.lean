module
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.LocalContradiction.Geometry
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.LocalContradiction.Displacement

/-!
# Local bridges for Lemma 12.6.23

The leaves construct the literal local span and quotient, select a conjugate
actor from W₀, prove its Borel-core containment and r-parameter normalization,
and compare its marked A₅ displacement with the actual centralizer index.
Once C_V(L)=1 is proved, the theorem below turns the orthogonal marking of
V/C_V(L) into an equivariant marking of V itself.

The full centralizer assertion still requires two source steps: deriving the
local structure and marked A₅ summands from Corollary 12.3.2, and deriving the
rank-one actor and index-two centralizer from the Borel and eight-point actions.
The explicit core, residual, and quotient-rank hypotheses in the leaf bridges
must be discharged in that assembly. No theorem here yet asserts C_V(L)=1.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 12.6.23, printed p.829.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter12.Section06.CentralLine.LocalContradiction
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G]

private theorem fixedSeed_eq_bot {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : L ≤ normalizer (V : Set G)) (hz : ZV L V = ⊥) :
    (fixedSeed L V hn).toSubmodule = ⊥ := by
  apply bot_unique
  intro v hv
  have he := (mem_fixedSeed_iff L V hn v).mp hv
  rw [hz, Subgroup.mem_bot] at he
  exact show v = 0 from Subtype.ext he

/-- The six-dimensional equivariant orthogonal coordinates on the original V,
after the central line has been eliminated. -/
theorem orthogonal_of_centralizer_eq_bot {L V : Subgroup G}
    [IsElementaryAbelian 2 V] {hn : L ≤ normalizer (V : Set G)}
    (D : OrthogonalMarking L V hn) (hz : ZV L V = ⊥) :
    ∃ e : Additive V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8),
      (∀ (l : L) v, e (seedRepresentation L V hn l v) =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 8)
          (D.groupEquiv (QuotientGroup.mk' (conjugation L V hn).ker l)) (e v)) ∧
      Module.finrank (ZMod 2) (Additive V) = 6 := by
  let q := ((fixedSeed L V hn).toSubmodule.quotEquivOfEqBot (fixedSeed_eq_bot hn hz)).symm
  refine ⟨q.trans D.coordinates, ?_, ?_⟩
  · intro l v
    exact D.equivariant l (Submodule.Quotient.mk v)
  · exact (q.trans D.coordinates).finrank_eq.trans
      BinaryPermutation.TerminalOrthogonal.Eight.finrank_natural

end CFSG.Quasithin.Chapter12.Section06.CentralLine.LocalContradiction
