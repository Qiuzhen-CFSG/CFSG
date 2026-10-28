module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoCores.Transport
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.BorelOvergroups
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Normalizers
public import CFSG.Quasithin.MainConverse.EvenLinearLocal.LinearThreeGeometry.Centralizers

/-!
# Self-centralizing cores of all PSL₃ Borel overgroups

Every proper overgroup of the standard Borel lies in a full point or line
parabolic, by the concrete matrix coverage theorem. Those parabolics have
self-centralizing two-cores. Since the overgroup contains the standard Sylow
two-subgroup, it inherits this property, including when it equals the Borel.
Sylow conjugacy covers every marking, and the actual field witness and group
isomorphism in `ClassicalGroup.IsPSL` transport the result to the source group.
No simplicity or nonabelianity assumption is needed.

Source: Aschbacher--Smith, the characteristic-two paragraph of 15.3.43,
printed p.1140, and A.2.3--4, p.33. This is the linear branch of the
rank-two parabolic-core calculation, not the entire numbered theorem.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
namespace LinearThreeCores
open Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry

/-- The intrinsic calculation over any actual finite field of order `2 ^ n`,
including the binary field. -/
theorem borelOvergroupCores (F : Type*) [Field F] [Finite F]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n) :
    BorelOvergroupCores PSL(3,F) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  apply borelOvergroupCores_of_standard (unipotentSylow F hn hF)
  intro Q hBQ hQ
  have hB : borel F ≤ Q := by
    change normalizer (unipotent F : Set PSL(3,F)) ≤ Q at hBQ
    rwa [normalizer_unipotent F hn hF] at hBQ
  have hTQ : (unipotentSylow F hn hF : Subgroup PSL(3,F)) ≤ Q :=
    (unipotent_le_borel F).trans hB
  rcases BorelOvergroups.overgroup_borel F Q hB hQ.ne with hp | hl
  · exact core_of_sylow_overgroup_le (unipotentSylow F hn hF) Q (pointParabolic F)
      hTQ hp (MainConverse.LinearThreeGeometry.parabolic_characteristicTwo F true)
  · exact core_of_sylow_overgroup_le (unipotentSylow F hn hF) Q (lineParabolic F)
      hTQ hl (MainConverse.LinearThreeGeometry.parabolic_characteristicTwo F false)
end LinearThreeCores

/-- Every proper overgroup of a Sylow normalizer in the actual PSL₃ model
has a self-centralizing two-core, including the normalizer itself. -/
theorem linearThree_borelOvergroupCores {H : Type*} [Group H] [Finite H]
    {n : ℕ} (hn : 1 < n) (hm : ClassicalGroup.IsPSL H 3 (2 ^ n)) :
    BorelOvergroupCores H := by
  obtain ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ := hm
  exact borelOvergroupCores_of_mulEquiv e
    (LinearThreeCores.borelOvergroupCores F (lt_trans Nat.zero_lt_one hn) hF)
end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
