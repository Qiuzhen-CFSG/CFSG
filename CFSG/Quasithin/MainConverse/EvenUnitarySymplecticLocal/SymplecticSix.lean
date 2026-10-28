module

public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.Defs
public import Theory.SpecificGroups.SymplecticSix.FixedRadical
public import Theory.SpecificGroups.SymplecticSix.EvenProjective
public import Theory.SpecificGroups.SymplecticSix.FieldTransport
public import Theory.SpecificGroups.SymplecticSix.OrderRank
public import Theory.SpecificGroups.SymplecticSix.ParabolicRanks
public import Theory.SpecificGroups.SymplecticSix.ParabolicCores
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.Quasithin.EvenCharacteristic

/-!
# Local conditions for the PSp₆(2) converse

Every matrix two-local stabilizes a nonzero totally isotropic subspace,
constructed as the radical of the fixed space of its defining two-subgroup.
The ambient order settles the odd ranks away from three. The three-rank
calculation for the actual full isotropic-subspace stabilizers over `ZMod 2`
therefore proves QT. Self-centralizing two-cores in these stabilizers give condition E:
an ambient Sylow subgroup contained in the two-local is also Sylow in the
covering stabilizer, so the intrinsic core-centralizer bound descends.

The matrix group has trivial center in characteristic two, and entrywise
field transport identifies every order-two coefficient field with `ZMod 2`.
These proved equivalences connect the calculations to `ClassicalGroup.PSp 3 F`.
The unconditional results below discharge the stabilizer premises of the
retained conditional interfaces. They establish both local conditions for
every coefficient field of order two, without QT, K, E, or local-classification
assumptions.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Theorem
0.1.2(2), printed p.4, repeated as Theorem 0.1.1(2), printed p.482,
`refs/quasithin.pdf` (1 March 2004 manuscript).
-/

namespace CFSG.Quasithin.MainConverse.SymplecticSix

open Theory.SpecificGroups.SymplecticSix
open Theory.GroupTheory

variable {F : Type*} [Field F] [Finite F]

/-- The exact projective carrier is equivalent to the binary matrix group.
The comparison uses entrywise field transport and the proved trivial center. -/
public noncomputable def projectiveEquivBinaryMatrix (hF : Nat.card F = 2) :
    ClassicalGroup.PSp 3 F ≃* Sp (ZMod 2) :=
  (pspFieldEquivZModTwo F hF).trans EvenProjective.equiv.symm

/-- The unconditional odd-rank branches away from three, on the exact quotient. -/
public theorem projective_odd_primeRank_le_two_of_ne_three
    (hF : Nat.card F = 2) {p : ℕ} (hp : p.Prime) (ho : Odd p) (h3 : p ≠ 3) :
    primeRank p (ClassicalGroup.PSp 3 F) ≤ 2 := by
  rw [primeRank_equiv p (projectiveEquivBinaryMatrix hF)]
  exact odd_primeRank_le_two_of_ne_three (Nat.card_zmod 2) hp ho h3

/-- Fixed-radical coverage reduces the binary matrix QT clause to the
three-ranks of its full isotropic stabilizers. -/
public theorem binary_twoLocal_rank_of_stabilizer_threeRank
    (hrank : ∀ W : Submodule (ZMod 2) (Vector (ZMod 2)), W ≠ ⊥ →
      (∀ x ∈ W, ∀ y ∈ W, form (ZMod 2) x y = 0) →
      primeRank 3 (stabilizer W) ≤ 2)
    (M : Subgroup (Sp (ZMod 2))) (hM : IsTwoLocal M)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) : primeRank p M ≤ 2 := by
  by_cases h3 : p = 3
  · subst p
    obtain ⟨W, hW, _, hiso, hMW⟩ := TwoLocalCover.twoLocal_stabilizes_isotropic M hM
    exact (primeRank_le_of_injective 3 (Subgroup.inclusion hMW)
      (Subgroup.inclusion_injective hMW)).trans (hrank W hW hiso)
  · exact (primeRank_le_of_injective p M.subtype M.subtype_injective).trans
      (odd_primeRank_le_two_of_ne_three (Nat.card_zmod 2) hp ho h3)

/-- Conditional QT assembly for every coefficient field of order two.
Only the full binary stabilizers' three-ranks remain to be calculated. -/
public theorem projective_quasithin_of_binary_stabilizer_threeRank
    (hF : Nat.card F = 2)
    (hrank : ∀ W : Submodule (ZMod 2) (Vector (ZMod 2)), W ≠ ⊥ →
      (∀ x ∈ W, ∀ y ∈ W, form (ZMod 2) x y = 0) →
      primeRank 3 (stabilizer W) ≤ 2) :
    IsQuasithin (ClassicalGroup.PSp 3 F) := by
  apply isQuasithin_of_equiv (projectiveEquivBinaryMatrix hF).symm
  exact isQuasithin_iff_twoLocal.mpr fun M hM p hp ho =>
    binary_twoLocal_rank_of_stabilizer_threeRank hrank M hM hp ho

/-- The requested local-rank clause, with precisely the remaining binary
isotropic-stabilizer three-rank premise. -/
public theorem projective_twoLocal_rank_of_binary_stabilizer_threeRank
    (hF : Nat.card F = 2)
    (hrank : ∀ W : Submodule (ZMod 2) (Vector (ZMod 2)), W ≠ ⊥ →
      (∀ x ∈ W, ∀ y ∈ W, form (ZMod 2) x y = 0) →
      primeRank 3 (stabilizer W) ≤ 2)
    (M : Subgroup (ClassicalGroup.PSp 3 F)) (hM : IsTwoLocal M)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) : primeRank p M ≤ 2 :=
  isQuasithin_iff_twoLocal.mp
    (projective_quasithin_of_binary_stabilizer_threeRank hF hrank) M hM p hp ho

/-- A binary two-local containing an ambient Sylow inherits the intrinsic
core-centralizer bound from its covering isotropic stabilizer. -/
public theorem binary_twoLocal_core_of_stabilizer_core
    (hcore : ∀ W : Submodule (ZMod 2) (Vector (ZMod 2)), W ≠ ⊥ →
      (∀ x ∈ W, ∀ y ∈ W, form (ZMod 2) x y = 0) →
      Subgroup.centralizer (pCore 2 (stabilizer W) : Set (stabilizer W)) ≤
        pCore 2 (stabilizer W))
    (T : Sylow 2 (Sp (ZMod 2))) (M : Subgroup (Sp (ZMod 2)))
    (hM : IsTwoLocal M) (hTM : (T : Subgroup (Sp (ZMod 2))) ≤ M) :
    Subgroup.centralizer (pCore 2 M : Set M) ≤ pCore 2 M := by
  obtain ⟨W, hW, _, hiso, hMW⟩ := TwoLocalCover.twoLocal_stabilizes_isotropic M hM
  have hTW := hTM.trans hMW
  have hsub : ((T.subtype hTW) : Subgroup (stabilizer W)) ≤
      M.subgroupOf (stabilizer W) := fun _ hx => hTM hx
  have hc := Subgroup.centralizer_pCore_le_of_sylow_le
    (T.subtype hTW) (M.subgroupOf (stabilizer W)) hsub (hcore W hW hiso)
  exact HasCharacteristicTwo.of_equiv (Subgroup.subgroupOfEquivOfLe hMW) hc

/-- Conditional E assembly. Normality and the centralizer are intrinsic
to each stabilizer; no ambient normality or assumed local classification enters. -/
public theorem projective_evenCharacteristic_of_binary_stabilizer_core
    (hF : Nat.card F = 2)
    (hcore : ∀ W : Submodule (ZMod 2) (Vector (ZMod 2)), W ≠ ⊥ →
      (∀ x ∈ W, ∀ y ∈ W, form (ZMod 2) x y = 0) →
      Subgroup.centralizer (pCore 2 (stabilizer W) : Set (stabilizer W)) ≤
        pCore 2 (stabilizer W)) :
    IsEvenCharacteristic (ClassicalGroup.PSp 3 F) := by
  intro T M hM hTM
  let e := projectiveEquivBinaryMatrix hF
  let S : Sylow 2 (Sp (ZMod 2)) := T.mapSurjective (f := e.toMonoidHom) e.surjective
  apply (Theory.Quasithin.centralizer_pCore_map_le_iff 2 e M).mp
  exact binary_twoLocal_core_of_stabilizer_core hcore S (M.map e.toMonoidHom)
    (Theory.Quasithin.isTwoLocal_map e hM.1) (Subgroup.map_mono hTM)

/-- The requested maximal-two-local centralizer clause, conditional only
on the remaining intrinsic core calculation in binary isotropic stabilizers. -/
public theorem projective_maximalTwoLocal_core_of_binary_stabilizer_core
    (hF : Nat.card F = 2)
    (hcore : ∀ W : Submodule (ZMod 2) (Vector (ZMod 2)), W ≠ ⊥ →
      (∀ x ∈ W, ∀ y ∈ W, form (ZMod 2) x y = 0) →
      Subgroup.centralizer (pCore 2 (stabilizer W) : Set (stabilizer W)) ≤
        pCore 2 (stabilizer W))
    (T : Sylow 2 (ClassicalGroup.PSp 3 F))
    (M : Subgroup (ClassicalGroup.PSp 3 F)) (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup (ClassicalGroup.PSp 3 F)) ≤ M) :
    Subgroup.centralizer (pCore 2 M : Set M) ≤ pCore 2 M :=
  projective_evenCharacteristic_of_binary_stabilizer_core hF hcore T M hM hTM

/-- Every binary matrix two-local has odd prime ranks at most two. The
three-rank branch uses the actual isotropic-stabilizer calculation. -/
public theorem binary_twoLocal_rank
    (M : Subgroup (Sp (ZMod 2))) (hM : IsTwoLocal M)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) : primeRank p M ≤ 2 :=
  binary_twoLocal_rank_of_stabilizer_threeRank stabilizer_threeRank_le_two M hM hp ho

/-- The exact central quotient over every field of order two is quasithin. -/
public theorem projective_quasithin (hF : Nat.card F = 2) :
    IsQuasithin (ClassicalGroup.PSp 3 F) :=
  projective_quasithin_of_binary_stabilizer_threeRank hF stabilizer_threeRank_le_two

/-- The source QT clause on every two-local of the actual projective carrier. -/
public theorem projective_twoLocal_rank (hF : Nat.card F = 2)
    (M : Subgroup (ClassicalGroup.PSp 3 F)) (hM : IsTwoLocal M)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) : primeRank p M ≤ 2 :=
  isQuasithin_iff_twoLocal.mp (projective_quasithin hF) M hM p hp ho

/-- A binary matrix two-local containing an ambient Sylow two-subgroup
has self-centralizing intrinsic two-core. -/
public theorem binary_twoLocal_core
    (T : Sylow 2 (Sp (ZMod 2))) (M : Subgroup (Sp (ZMod 2)))
    (hM : IsTwoLocal M) (hTM : (T : Subgroup (Sp (ZMod 2))) ≤ M) :
    Subgroup.centralizer (pCore 2 M : Set M) ≤ pCore 2 M :=
  binary_twoLocal_core_of_stabilizer_core ParabolicCores.centralizer_pCore_le T M hM hTM

/-- The exact central quotient over every field of order two has even
characteristic, with all stabilizer-core premises discharged. -/
public theorem projective_evenCharacteristic (hF : Nat.card F = 2) :
    IsEvenCharacteristic (ClassicalGroup.PSp 3 F) :=
  projective_evenCharacteristic_of_binary_stabilizer_core hF ParabolicCores.centralizer_pCore_le

/-- The source E clause: the two-core is self-centralizing inside every
maximal two-local containing the specified ambient Sylow two-subgroup. -/
public theorem projective_maximalTwoLocal_core (hF : Nat.card F = 2)
    (T : Sylow 2 (ClassicalGroup.PSp 3 F))
    (M : Subgroup (ClassicalGroup.PSp 3 F)) (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup (ClassicalGroup.PSp 3 F)) ≤ M) :
    Subgroup.centralizer (pCore 2 M : Set M) ≤ pCore 2 M :=
  projective_evenCharacteristic hF T M hM hTM

end CFSG.Quasithin.MainConverse.SymplecticSix
