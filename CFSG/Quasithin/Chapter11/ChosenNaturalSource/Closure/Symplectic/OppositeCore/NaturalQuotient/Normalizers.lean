module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Pair

/-!
# Normalization by the actual opposite-point stabilizer

W is invariant under the full point normalizer G₁. Its y-conjugate is
therefore invariant under the full normalizer of V₁ʸ. Thus the actual
S=N_M₁(V₁ʸ) preserves both W and Wʸ, hence I, O₂(I), and Q. The same
argument applies to X when the marked opposite point is X-invariant.
Preserving [Q,X₁] is a further assertion, not inferred from preserving Q.
Source: Aschbacher--Smith 11.5.7, printed p.783.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient

private theorem normalizes_core_pair {G : Type*} [Group G]
    (H W : Subgroup G) (y : G)
    (hW : H ≤ normalizer (W : Set G))
    (hZ : H ≤ normalizer (W.map (MulAut.conj y).toMonoidHom : Set G)) :
    H ≤ normalizer (corePair W y : Set G) := by
  have hI : H ≤ normalizer (oppositeJoin W y : Set G) :=
    (le_inf hW hZ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hR : H ≤ normalizer ((oppositeJoin W y).pCoreIn 2 : Set G) :=
    hI.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  exact (le_inf
    ((le_inf hW hR).trans inf_normalizer_le_normalizer_inf)
    ((le_inf hZ hR).trans inf_normalizer_le_normalizer_inf)).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Conjugating the full point normalizer transports the invariance of W. -/
theorem opposite_point_normalizer_normalizes_W (y : G) :
    normalizer (E.V₁.map (MulAut.conj y).toMonoidHom : Set G) ≤
      normalizer ((auxiliaryW E).map (MulAut.conj y).toMonoidHom : Set G) := by
  rw [← map_equiv_normalizer_eq E.V₁ (MulAut.conj y),
    ← map_equiv_normalizer_eq (auxiliaryW E) (MulAut.conj y)]
  exact map_mono (G₁_normalizes_auxiliaryW E)

/-- The full opposite-point stabilizer preserves the actual join. -/
theorem opposite_stabilizer_normalizes_join (y : G) :
    oppositePointStabilizer E y ≤ normalizer (oppositeJoin (auxiliaryW E) y : Set G) :=
  (le_inf ((inf_le_left.trans inf_le_right).trans (G₁_normalizes_auxiliaryW E))
    (inf_le_right.trans (opposite_point_normalizer_normalizes_W E y))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- In particular it preserves the full opposite two-core. -/
theorem opposite_stabilizer_normalizes_core (y : G) :
    oppositePointStabilizer E y ≤
      normalizer ((oppositeJoin (auxiliaryW E) y).pCoreIn 2 : Set G) :=
  (opposite_stabilizer_normalizes_join E y).trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

/-- S preserves the literal core pair, by preserving the two opposite generators. -/
theorem opposite_stabilizer_normalizes_corePair (y : G) :
    oppositePointStabilizer E y ≤ normalizer (corePair (auxiliaryW E) y : Set G) :=
  normalizes_core_pair _ _ _
    ((inf_le_left.trans inf_le_right).trans (G₁_normalizes_auxiliaryW E))
    (inf_le_right.trans (opposite_point_normalizer_normalizes_W E y))

/-- The Cartan's geometric opposite-point invariance supplies its Q-normalization. -/
theorem cartan_normalizes_corePair (y : G) (hXG : E.X ≤ E.G₁)
    (hXpoint : E.X ≤ normalizer (E.V₁.map (MulAut.conj y).toMonoidHom : Set G)) :
    E.X ≤ normalizer (corePair (auxiliaryW E) y : Set G) :=
  normalizes_core_pair _ _ _ (hXG.trans (G₁_normalizes_auxiliaryW E))
    (hXpoint.trans (opposite_point_normalizer_normalizes_W E y))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
