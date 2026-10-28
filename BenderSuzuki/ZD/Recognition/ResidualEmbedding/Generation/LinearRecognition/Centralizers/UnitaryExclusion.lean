module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Contracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.Endgame
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.ModelBounds

/-!
# The unitary branch of GLS4, Chapter 2, Section 13

The uniform unitary branch is impossible under the preceding local,
shearing and fusion conclusions. Even order supplies an involution in the
pair stabilizer. `SecondCentralizer` constructs its cyclic subgroup and
second distinguished centralizer. `LocalTwoStructure` proves the centralizer
Sylow bound and constructs the commuting homocyclic subgroups using the
source subgroup-join normalizer.

The actual special or projective unitary cover supplies both automorphism
bounds through `ModelBounds`. The maximal abelian two-subgroup argument in
`Endgame` then forces n = 2 and the contradiction 64 ≤ |Q| ≤ 32. All geometric
and model premises of that endgame are discharged here; the earlier-source
local, shearing and fusion conclusions remain the explicit assembly inputs.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Section 13, Lemmas 13.2–13.4 and
(13A)–(13C); Chapter 4, Lemmas 3.4–3.6.
-/

namespace BenderSuzuki.ZD
open Subgroup UnitaryExclusion

/-- The Section 13 unitary alternative is impossible. The cyclic subgroup,
second centralizer, local Sylow bound, homocyclic construction and intrinsic
automorphism bounds are proved from the stated inputs, with no additional
geometric or model witness assumed. The preceding local recognition, shearing
and fusion conclusions remain for the Proposition 13.1 assembly owner. -/
public theorem proper_residualGenerated_unitary_centralizers_false
    {G : Type*} [Group G] [Finite G]
    {Z : Set G} {M : Subgroup G} {z t : G} {n : ℕ}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hshear : ResidualCentralizerShearing Z M t)
    (hfusion : ∀ v : G, PFAppendixIII.IsInvolution v → v ∉ Z →
      ∃ d ∈ residualPairStabilizer M t, IsConj v d)
    (hn : 2 ≤ n) (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n) : False := by
  have hlocalTwo : ∀ u ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution u →
      CentralizerTwoBound Z u ∧ Nonempty (LargeAbelianData M n) := by
    intro u huD hu
    obtain ⟨d⟩ := secondCentralizerData_of_minimalCounterexample h r hz hzM ht htM
      hL hlocal hshear hn hcard e hunitary u huD hu
    exact local_consequences_of_source h r ha hz hzM ht htM hL heven
      hlocal hshear hfusion hn hcard e hunitary huD hu d
  obtain ⟨u, huorder⟩ := exists_prime_orderOf_dvd_card'
    (G := residualPairStabilizer M t) 2 heven.two_dvd
  have hu : PFAppendixIII.IsInvolution (u : G) :=
    (orderOf_eq_prime_iff.mp ((Subgroup.orderOf_coe u).trans huorder)).symm
  obtain ⟨hlarge⟩ := (hlocalTwo u u.property hu).2
  exact exclusion_of_local_data h.disconnected hn hcard hfusion hlarge
    (fun v hvD hv => (hlocalTwo v hvD hv).1)
    (fun v hvD hv => automorphismBounds_of_unitaryCentralizerCover hn (hunitary v hvD hv).2)

end BenderSuzuki.ZD
