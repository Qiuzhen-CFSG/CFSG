module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorLevi
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.LocalActions

/-!
# The actual root actor is a central cover of its panel image

The opposite Levi argument places R_i ∩ K_i inside H. Its elements
normalize both generating roots. Each of those roots normalizes K_i,
and meets K_i trivially, so their commutators vanish. Thus R_i ∩ K_i
centralizes R_i and has odd order. The final theorem states centrality
for the kernel of the existing, literal rankOneAction.

This proves the central-kernel part of Fong--Seitz I (5C), printed
pp.25--26, with no remainder-containment or regularity premise. It does
not identify the cover with its faithful image: the SU3 versus PSU3
scalar kernel is retained. Rank-one model identification, module
realization and common-field labels remain separate source obligations.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

/-- The kernel of the actual root actor is contained in the actual Cartan. -/
theorem rootActor_inf_localKernel_le_torus :
    rootActor Q split i ⊓ localKernel Q i ≤ Q.tits.B ⊓ Q.tits.N :=
  (le_inf (inf_le_left.trans (rootActor_le_oppositeLevi Q split i))
    (inf_le_right.trans (le_inf (localKernel_le_borel Q i)
      (localKernel_le_conjugate_borel Q i)))).trans
    (oppositeLevi_inf_two_borels_le_torus Q split i)

/-- In particular this kernel has odd order; the scalar kernel is retained. -/
theorem rootActor_inf_localKernel_odd :
    Nat.Coprime 2 (Nat.card (rootActor Q split i ⊓ localKernel Q i : Subgroup (X ⧸ Q.D))) :=
  split.odd.of_dvd_right (card_dvd_of_le (rootActor_inf_localKernel_le_torus Q split i))

private theorem kernel_centralizes_root (A : Subgroup (X ⧸ Q.D))
    (hAP : A ≤ Q.tits.standardParabolic {Q.simple i})
    (hHA : Q.tits.B ⊓ Q.tits.N ≤ normalizer (A : Set (X ⧸ Q.D)))
    (hd : Disjoint A (localKernel Q i)) :
    rootActor Q split i ⊓ localKernel Q i ≤ centralizer (A : Set (X ⧸ Q.D)) := by
  apply le_centralizer_iff.mpr
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  apply le_trans _ hd.le_bot
  apply le_inf
  · exact le_normalizer_iff_commutator_le_left.mp
      ((rootActor_inf_localKernel_le_torus Q split i).trans hHA)
  · exact (commutator_mono le_rfl inf_le_right).trans
      (le_normalizer_iff_commutator_le_right.mp
        (hAP.trans (localKernel_parabolic_normalizes Q i)))

/-- The actual panel kernel is central in R_i. This does not identify R_i
with the faithful panel image, which would lose the SU3 scalar kernel. -/
theorem rootActor_inf_localKernel_centralizes :
    rootActor Q split i ⊓ localKernel Q i ≤ centralizer (rootActor Q split i : Set (X ⧸ Q.D)) := by
  apply le_centralizer_iff.mpr
  apply sup_le
  · apply le_centralizer_iff.mp
    exact kernel_centralizes_root Q split i _
      (le_sup_left.trans (rootActor_le_endpoint Q split i))
      (torus_normalizes_simpleRoot Q split i) (simpleRoot_disjoint_localKernel Q split i)
  · apply le_centralizer_iff.mp
    exact kernel_centralizes_root Q split i _
      (le_sup_right.trans (rootActor_le_endpoint Q split i))
      (torus_normalizes_rightConjugate _ (torus_normalizes_simpleRoot Q split i) _)
      ((oppositeRoot_disjoint_borel Q split i).mono_right (localKernel_le_borel Q i))

/-- The central-cover statement uses the existing actual rank-one action. -/
theorem rankOneAction_ker_le_center :
    (rankOneAction Q split i).ker ≤ center (rankOne Q split i) := by
  intro k hk
  rw [rankOneAction_ker] at hk
  apply mem_center_iff.mpr
  intro r
  apply Subtype.ext
  exact rootActor_inf_localKernel_centralizes Q split i ⟨k.property,hk⟩ r r.property

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
