module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.ThreeAlternatives.ExtraspecialBranch.Faithfulness
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.ThreeAlternatives.ExtraspecialBranch.RcCyclicity
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.ThreeAlternatives.ExtraspecialBranch.ThetaGeneration

/-!
# The complete extraspecial alternative in 15.3.7

Geometry identifies the intrinsic quotient with the supplied Heisenberg
model and proves the literal central-preimage equality. Faithfulness
constructs the actual cyclic action required by 14.1.17(4) and proves that
every Sylow three-subgroup of M ∩ Mc is cyclic.

RcCyclicity embeds the faithful center-fixing action in an actual dihedral
Sylow two-group and excludes elementary four-subgroups. ThetaGeneration
places all cubic elements in the residual and lifts its Heisenberg
generators through the two-core, using two-perfectness to obtain equality.

The theorem below assembles all five source conclusions. Only the preceding
A.1.24 branch data remain explicit; the parent ThreeAlternatives assembly
supplies those data from its model dichotomy.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma 15.3.7,
printed p.1122 (PDF p.1139).
-/

namespace CFSG.Quasithin.Chapter15.Section03.ThreeAlternatives
variable {G : Type*} [Group G] [Finite G]
variable {M Mc V : Subgroup G} {T : Sylow 2 G} {d : NaturalOrthogonalAction M V}

/-- The complete extraspecial branch of 15.3.7 from the corresponding
A.1.24 output for the actual star residual. -/
public theorem extraspecialAlternative_of_star_model (h : SourceInputs M Mc V T d)
    (hcard : Nat.card (star M (residualY M Mc)) = 27)
    (hextra : IsExtraspecial 3 (star M (residualY M Mc)))
    (he : Nonempty (star M (residualY M Mc) ≃* HeisenbergPrime 3)) :
    ExtraspecialAlternative M Mc V d := by
  let := hextra
  exact ⟨ExtraspecialBranch.extraspecial_quotient_model he,
    ExtraspecialBranch.extraspecial_centralPreimage_eq h,
    ExtraspecialBranch.extraspecial_rc_image_cyclic h hcard,
    ExtraspecialBranch.extraspecial_residual_eq_theta h he,
    ExtraspecialBranch.intersection_sylow_three_cyclic h
      (IsExtraspecial.isPGroup 3 (star M (residualY M Mc)))⟩

end CFSG.Quasithin.Chapter15.Section03.ThreeAlternatives
