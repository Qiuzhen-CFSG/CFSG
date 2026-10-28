module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootLocalCover

/-!
# Normality of the full local root closure

The marked simple reflection interchanges U and its reflected conjugate.
The full Cartan normalizes both, and U normalizes their join. Thus the
whole marked parabolic normalizes C = ⟨U,Uˢ⟩, directly from its Bruhat
cells. This needs no chosen reflection inside the smaller root group,
no perfectness and no (2B) assumption.

Source: Fong--Seitz I (5B), p.25. This is the relative-normality input
for identifying the actual local cover with an original factor quotient.
-/

public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.LocalCover
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

theorem closure_parabolic_normalizes :
    Q.tits.standardParabolic {Q.simple i} ≤ normalizer (localClosure Q split i : Set (X ⧸ Q.D)) := by
  have hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (localClosure Q split i : Set (X ⧸ Q.D)) :=
    (le_inf (inf_le_left.trans split.normalizes)
      (torus_normalizes_rightConjugate split.U (inf_le_left.trans split.normalizes)
        (representative (Q.simple i)))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hB : Q.tits.B ≤ normalizer (localClosure Q split i : Set (X ⧸ Q.D)) := by
    rw [← split.factorization]
    exact sup_le ((show split.U ≤ localClosure Q split i from le_sup_left).trans
      (localClosure Q split i).le_normalizer) hH
  apply Q.tits.standardParabolic_le _ hB
  intro s hs
  rw [Set.mem_singleton_iff] at hs
  subst s
  apply Q.tits.bruhatCell_subset_of_mem _ hB
    (Q.tits.representative_mem_bruhatCell _ _ (representative_spec _))
  apply mem_normalizer_iff.mpr
  intro x
  have he : rightConjugate (localClosure Q split i)
      (representative (Q.simple i) : X ⧸ Q.D) = localClosure Q split i := by
    change (split.U ⊔ unipotentConjugate split (Q.simple i)).comap
      (MulAut.conj (representative (Q.simple i) : X ⧸ Q.D)).toMonoidHom = _
    rw [← comap_sup_eq _ _ _ (MulAut.conj _).surjective]
    change unipotentConjugate split (Q.simple i) ⊔
      rightConjugate (unipotentConjugate split (Q.simple i)) _ = _
    rw [unipotentConjugate_right split _ _ _ (representative_spec _)]
    have hss : Q.simple i * Q.simple i = 1 := by
      simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2
    rw [hss, unipotentConjugate_one, sup_comm]
    rfl
  exact (SetLike.ext_iff.mp he x).symm
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.LocalCover

