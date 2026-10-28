module
public import Theory.SpecificGroups.SL2.AbelianRadicalActors
public import Theory.SpecificGroups.Alternating.FiveMarkedExtension
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import GorensteinWalter.PSL2PerfectOfCard
/-!
# The marked five-point quotient of a prime SL₂ residual

Combine the elementary lift obstruction with a specified PSL₂-to-A₅
comparison. An elementary actor with image of order four lies outside the
simple socle; the faithful conjugation action on that socle identifies the
whole radical quotient with S₅ and preserves the actor's outer position.
Abelianness of the actual radical is an explicit structural premise.

The prime is kept symbolic at the field-instance boundary. This avoids
expanding arithmetic in a concrete ZMod field while matching the generic
SL₂ structure theorem with the canonical ZMod matrix-group instances.

Source: Aschbacher--Smith A.3.21(a), p.55, and E.1.14(7), p.214.
-/
public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SL2.PrimeMarkedFive
variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

/-- The actual radical quotient is S₅ with the original actor outside A₅. -/
theorem exists_marked_equiv (ho : Odd p) (hl : 3 < p)
    (e : solvableResidual H ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (hres : pResidual 2 H = solvableResidual H)
    (eA : GorensteinWalter.PSL2 (ZMod p) ≃* alternatingGroup (Fin 5))
    [IsMulCommutative (solvableRadical H)]
    (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hcard : Nat.card (A.map (QuotientGroup.mk' (solvableRadical H))) = 4) :
    ∃ f : (H ⧸ solvableRadical H) ≃* Equiv.Perm (Fin 5),
      (generalizedFitting (H ⧸ solvableRadical H)).map f.toMonoidHom =
        alternatingGroup (Fin 5) ∧
      ¬ (A.map (QuotientGroup.mk' (solvableRadical H))).map f.toMonoidHom ≤
        alternatingGroup (Fin 5) := by
  have hF : Nat.card (ZMod p) = p := by simp only [Nat.card_eq_fintype_card, ZMod.card]
  obtain ⟨_, hs, ⟨es⟩, _⟩ := ResidualTwoExtension.radical_quotient_structure
    (hF.symm ▸ ho) (hF.symm ▸ hl) e hres
  let Q := H ⧸ solvableRadical H
  let : IsSimpleGroup (generalizedFitting Q) := hs
  let : Group.IsPerfect (GorensteinWalter.PSL2 (ZMod p)) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three (ZMod p) (hF.symm ▸ hl)
  let : Group.IsPerfect (generalizedFitting Q) :=
    Group.IsPerfect.ofSurjective (f := es.symm.toMonoidHom) es.symm.surjective
  have hC := SimpleSocle.centralizer_eq_bot
    (Group.IsPerfect.not_isMulCommutative (generalizedFitting Q))
  have hout := AbelianRadicalActors.actor_not_le_socle
    (hF.symm ▸ ho) (hF.symm ▸ hl) e hres A hcard
  exact Theory.SpecificGroups.Alternating.FiveMarkedExtension.exists_marked_equiv
    (generalizedFitting Q) (es.trans eA) hC _ hout

end Theory.SpecificGroups.SL2.PrimeMarkedFive
