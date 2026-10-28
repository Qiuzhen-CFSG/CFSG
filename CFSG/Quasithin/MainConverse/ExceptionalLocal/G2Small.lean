module

public import CFSG.Quasithin.MainConverse.ExceptionalLocal.SmallOrders
public import CFSG.Quasithin.MainConverse.ExceptionalLocal.G2Small.BinaryCover
public import CFSG.Quasithin.MainConverse.ExceptionalLocal.G2Small.TernaryCover.Complete
public import CFSG.Quasithin.MainConverse.Transport
public import Theory.AtlasPort.LinearGroups.G2.BinaryThreeRank
public import Theory.AtlasPort.LinearGroups.G2.BinarySmallLocals
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals
public import Theory.AtlasPort.LinearGroups.G2.FieldTransport
public import Theory.GroupTheory.TwoLocalConjugateCover

/-!
# Quasithinness and even characteristic for the small G₂ models

The explicit nonabelian Sylow three-subgroup in full G₂(2) bounds the
three-rank of the actual commutator subgroup and all its subgroups. Together
with the already proved bounds away from three, this establishes QT for
G₂(2)′. No exceptional isomorphism, simplicity, or local-characteristic
hypothesis enters this argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Theorem
0.1.2(1,4), printed pp.3–4, repeated as Theorem 0.1.1 on pp.481–482.
This module proves the QT and even-characteristic conditions for G₂(2)′
and G₂(3), with transport to any isomorphic group.

Both restricted binary parabolics have self-centralizing two-cores.
The binary conjugacy cover identifies maximal two-locals with conjugates of
these restrictions, proving even characteristic in the actual derived carrier.

For G₂(3), the complete cover uses three actual two-locals: the involution
normalizer and both elementary-eight normalizers, including the all-norm-one
Cayley-frame eight. Their orders are not divisible by 27, and their intrinsic
two-cores are self-centralizing. Rank monotonicity gives the local three-rank
bound; maximality turns each covering inclusion into equality and transports
the core condition. Field equivalence transports these results to every
`ClassificationModels.IsG2At G 3`. The older two-member conditional reductions
are preserved, while the final assembly uses the complete three-member cover.
-/

namespace CFSG.Quasithin.MainConverse.ExceptionalLocal

/-- Three-rank at most two in any copy of the actual binary derived group. -/
public theorem g2_binary_derived_three_primeRank_le_two
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* commutator (Atlas.G2.Model (ZMod 2))) : primeRank 3 G ≤ 2 := by
  rw [Theory.GroupTheory.primeRank_equiv 3 e]
  exact (Theory.GroupTheory.primeRank_le_of_injective 3
    (commutator (Atlas.G2.Model (ZMod 2))).subtype Subtype.val_injective).trans
      Atlas.G2.BinaryThreeRank.primeRank_le_two

/-- In particular every maximal two-local has three-rank at most two;
the bound holds for every subgroup. -/
public theorem g2_binary_derived_subgroup_three_primeRank_le_two
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (M : Subgroup G) : primeRank 3 M ≤ 2 :=
  (Theory.GroupTheory.primeRank_le_of_injective 3 M.subtype M.subtype_injective).trans
    (g2_binary_derived_three_primeRank_le_two e)

/-- The actual commutator of the binary octonion automorphism group is quasithin. -/
public theorem g2_binary_derived_quasithin
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* commutator (Atlas.G2.Model (ZMod 2))) : IsQuasithin G :=
  g2_binary_derived_quasithin_of_three_local_rank e
    (fun M _ => g2_binary_derived_subgroup_three_primeRank_le_two e M)

open Atlas.G2.BinaryParabolicPair in
/-- Conditional binary even-characteristic assembly with an explicit first
local input. The following theorem supplies it from the concrete proof. -/
public theorem g2_binary_derived_evenCharacteristic_of_sylow_local_conjugacy
    (hfirst : HasCharacteristicTwo derivedFirst)
    (hcover : ∀ (T : Sylow 2 DerivedModel) (M : Subgroup DerivedModel),
      IsMaximalTwoLocal M → (T : Subgroup DerivedModel) ≤ M →
      ∃ g : DerivedModel,
        M = derivedFirst.map (MulAut.conj g).toMonoidHom ∨
        M = derivedSecond.map (MulAut.conj g).toMonoidHom)
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* commutator (Atlas.G2.Model (ZMod 2))) : IsEvenCharacteristic G := by
  apply evenCharacteristic_of_model_equiv e
  intro T M hM hTM
  obtain ⟨g, h | h⟩ := hcover T M hM hTM
  · rw [h]
    exact (Theory.Quasithin.centralizer_pCore_map_le_iff 2
      (MulAut.conj g) derivedFirst).mpr hfirst
  · rw [h]
    exact (Theory.Quasithin.centralizer_pCore_map_le_iff 2
      (MulAut.conj g) derivedSecond).mpr derivedSecond_centralizer_pCore

open Atlas.G2.BinaryParabolicPair in
/-- Both local core calculations are discharged. The only remaining binary
input is coverage of maximal two-locals containing a Sylow subgroup. -/
public theorem g2_binary_derived_evenCharacteristic_of_local_cover
    (hcover : ∀ (T : Sylow 2 DerivedModel) (M : Subgroup DerivedModel),
      IsMaximalTwoLocal M → (T : Subgroup DerivedModel) ≤ M →
      ∃ g : DerivedModel,
        M = derivedFirst.map (MulAut.conj g).toMonoidHom ∨
        M = derivedSecond.map (MulAut.conj g).toMonoidHom)
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* commutator (Atlas.G2.Model (ZMod 2))) : IsEvenCharacteristic G :=
  g2_binary_derived_evenCharacteristic_of_sylow_local_conjugacy
    derivedFirst_centralizer_pCore hcover e

/-- Every copy of the actual binary derived group has even characteristic.
The concrete parabolic cover discharges the final local premise. -/
public theorem g2_binary_derived_evenCharacteristic
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* commutator (Atlas.G2.Model (ZMod 2))) : IsEvenCharacteristic G :=
  g2_binary_derived_evenCharacteristic_of_local_cover
    Atlas.G2.BinaryParabolicPair.binary_sylow_maximalTwoLocal_conjugate e

/-- QT and even characteristic for the actual commutator of G₂(2),
transported along an actual group isomorphism. -/
public theorem g2_binary_derived_quasithin_evenCharacteristic
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  ⟨g2_binary_derived_quasithin e, g2_binary_derived_evenCharacteristic e⟩

open Atlas.G2.TernaryLocals

private theorem g2_three_equiv_ternary {G : Type*} [Group G]
    (hG : ClassificationModels.IsG2At G 3) : Nonempty (G ≃* Atlas.G2.Model (ZMod 3)) := by
  obtain ⟨F, hF, hfin, hq, ⟨e⟩⟩ := hG
  let := Fintype.ofFinite F
  let eF : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three (by
    simpa only [Nat.card_eq_fintype_card] using hq)
  exact ⟨e.trans (Atlas.G2.fieldEquiv eF.symm)⟩

/-- Conditional ternary three-rank reduction. The two local order bounds and
coverage of arbitrary nonidentity two-subgroup normalizers remain inputs. -/
public theorem g2_three_local_three_rank_of_normalizer_cover
    (horder : ∀ i, ¬ 3^3 ∣ Nat.card (localSubgroup i))
    (hcover : ∀ R : Subgroup (Atlas.G2.Model (ZMod 3)), R ≠ ⊥ → IsPGroup 2 R →
      ∃ i g, Subgroup.normalizer (R : Set (Atlas.G2.Model (ZMod 3))) ≤
        (localSubgroup i).map (MulAut.conj g).toMonoidHom)
    {G : Type*} [Group G] [Finite G] (hG : ClassificationModels.IsG2At G 3)
    (M : Subgroup G) (hM : IsMaximalTwoLocal M) : primeRank 3 M ≤ 2 := by
  obtain ⟨e⟩ := g2_three_equiv_ternary hG
  rw [Theory.GroupTheory.primeRank_equiv 3 (e.subgroupMap M)]
  apply Theory.GroupTheory.primeRank_le_of_twoLocal_conjugate_cover localSubgroup 3 2
      (fun i => primeRank_le_two_of_cube_not_dvd (horder i)) ?_ _
      (Theory.Quasithin.isTwoLocal_map e hM.1)
  rintro N ⟨R, hR, hp, rfl⟩
  exact hcover R hR hp

/-- Conditional ternary even-characteristic reduction. Maximality makes the
covering inclusion an equality, allowing the intrinsic two-core to transport. -/
public theorem g2_three_evenCharacteristic_of_normalizer_cover
    (hcore : ∀ i, HasCharacteristicTwo (localSubgroup i))
    (hcover : ∀ R : Subgroup (Atlas.G2.Model (ZMod 3)), R ≠ ⊥ → IsPGroup 2 R →
      ∃ i g, Subgroup.normalizer (R : Set (Atlas.G2.Model (ZMod 3))) ≤
        (localSubgroup i).map (MulAut.conj g).toMonoidHom)
    {G : Type*} [Group G] [Finite G] (hG : ClassificationModels.IsG2At G 3) :
    IsEvenCharacteristic G := by
  obtain ⟨e⟩ := g2_three_equiv_ternary hG
  intro T M hM _
  apply (Theory.Quasithin.centralizer_pCore_map_le_iff 2 e M).mp
  apply Theory.GroupTheory.centralizer_pCore_le_of_twoLocal_conjugate_cover
      localSubgroup localSubgroup_isTwoLocal hcore ?_ _
      (Theory.Quasithin.isMaximalTwoLocal_map e hM)
  rintro N ⟨R, hR, hp, rfl⟩
  exact hcover R hR hp

/-- Conditional final ternary assembly. It needs only a cover of maximal
two-locals, the two local order bounds, and their intrinsic core centralizers. -/
public theorem g2_three_quasithin_evenCharacteristic_of_maximal_local_cover
    (horder : ∀ i, ¬ 3^3 ∣ Nat.card (localSubgroup i))
    (hcore : ∀ i, HasCharacteristicTwo (localSubgroup i))
    (hcover : ∀ M : Subgroup (Atlas.G2.Model (ZMod 3)), IsMaximalTwoLocal M →
      ∃ i g, M ≤ (localSubgroup i).map (MulAut.conj g).toMonoidHom)
    {G : Type*} [Group G] [Finite G] (hG : ClassificationModels.IsG2At G 3) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  have hn : ∀ R : Subgroup (Atlas.G2.Model (ZMod 3)), R ≠ ⊥ → IsPGroup 2 R →
      ∃ i g, Subgroup.normalizer (R : Set (Atlas.G2.Model (ZMod 3))) ≤
        (localSubgroup i).map (MulAut.conj g).toMonoidHom := by
    intro R hR hp
    have hl : IsTwoLocal (Subgroup.normalizer (R : Set (Atlas.G2.Model (ZMod 3)))) :=
      ⟨R,hR,hp,rfl⟩
    obtain ⟨M,hRM,hM⟩ := Finite.exists_le_maximal hl
    obtain ⟨i,g,hMg⟩ := hcover M hM
    exact ⟨i,g,hRM.trans hMg⟩
  exact ⟨g2_three_quasithin_of_three_local_rank hG
      (g2_three_local_three_rank_of_normalizer_cover horder hn hG),
    g2_three_evenCharacteristic_of_normalizer_cover hcore hn hG⟩

private theorem g2_three_twoLocal_threeFamily_cover
    (M : Subgroup (Atlas.G2.Model (ZMod 3))) (hM : IsTwoLocal M) :
    ∃ (i : Fin 3) (g : Atlas.G2.Model (ZMod 3)),
      M ≤ (CayleyEight.localFamily i).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨N, hMN, hN⟩ := Finite.exists_le_maximal hM
  obtain ⟨i, g, hNg⟩ := TernaryCover.maximalTwoLocal_threeFamily_cover N hN
  exact ⟨i, g, hMN.trans hNg⟩

/-- Every maximal two-local in G₂(3) has three-rank at most two.
All three representatives in the complete cover satisfy the order bound. -/
public theorem g2_three_local_three_rank
    {G : Type*} [Group G] [Finite G] (hG : ClassificationModels.IsG2At G 3)
    (M : Subgroup G) (hM : IsMaximalTwoLocal M) : primeRank 3 M ≤ 2 := by
  obtain ⟨e⟩ := g2_three_equiv_ternary hG
  rw [Theory.GroupTheory.primeRank_equiv 3 (e.subgroupMap M)]
  exact Theory.GroupTheory.primeRank_le_of_twoLocal_conjugate_cover
    CayleyEight.localFamily 3 2
    (fun i => primeRank_le_two_of_cube_not_dvd
      (CayleyEight.localFamily_three_cube_not_dvd_card i))
    g2_three_twoLocal_threeFamily_cover _ (Theory.Quasithin.isTwoLocal_map e hM.1)

/-- G₂(3) has even characteristic. The complete three-member cover and
the intrinsic core calculations discharge every local premise. -/
public theorem g2_three_evenCharacteristic
    {G : Type*} [Group G] [Finite G] (hG : ClassificationModels.IsG2At G 3) :
    IsEvenCharacteristic G := by
  obtain ⟨e⟩ := g2_three_equiv_ternary hG
  intro T M hM _
  apply (Theory.Quasithin.centralizer_pCore_map_le_iff 2 e M).mp
  exact Theory.GroupTheory.centralizer_pCore_le_of_twoLocal_conjugate_cover
    CayleyEight.localFamily CayleyEight.localFamily_isTwoLocal
    CayleyEight.localFamily_centralizer_pCore g2_three_twoLocal_threeFamily_cover _
    (Theory.Quasithin.isMaximalTwoLocal_map e hM)

/-- The complete local three-rank bound and the existing bounds away from
three establish quasithinness of every copy of G₂(3). -/
public theorem g2_three_quasithin
    {G : Type*} [Group G] [Finite G] (hG : ClassificationModels.IsG2At G 3) :
    IsQuasithin G :=
  g2_three_quasithin_of_three_local_rank hG (g2_three_local_three_rank hG)

/-- QT and even characteristic for G₂(3), assembled using all three
proved local normalizers and their exhaustive maximal-two-local cover. -/
public theorem g2_three_quasithin_evenCharacteristic
    {G : Type*} [Group G] [Finite G] (hG : ClassificationModels.IsG2At G 3) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  ⟨g2_three_quasithin hG, g2_three_evenCharacteristic hG⟩

end CFSG.Quasithin.MainConverse.ExceptionalLocal
