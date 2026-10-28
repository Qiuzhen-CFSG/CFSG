module

public import Theory.Representation.BinaryNaturalDual.FiveActors.Classification
public import Theory.Representation.BinaryNaturalDual.FiveActors.ModuleGeometry
public import Theory.Representation.BinaryNaturalDual.FiveActors.Hyperplanes

/-!
# Complete coordinate classification of degree-five elementary actors

The sharp outer rank bound removes the innerness premise from radical
placement. The radical has order 64, so equal orders turn rank-six
containment into equality, while rank-five containment has relative index
two. These give exhaustive conjugacy statements with actual conjugators.
Placement also discharges the hypothesis of the generated-core transport.

The outer-involution fixed space and its centralizer commutator are
identified with the standard representation subspaces, so the existing
natural-module decomposition uses the literal centralizer and commutator.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.2(1–5),
printed pp.390–391 (PDF pp.401–402). The representation statements take
`CoordinateAction 5` explicitly; its construction and transport to arbitrary
source modules belong to the H.9 assembly.
-/

public section

open Theory.GroupTheory
open scoped IsMulCommutative
namespace BinaryNaturalDual.FiveActors

private theorem elementary_card (A : Subgroup M) [IsElementaryAbelian 2 A] :
    Nat.card A = 2 ^ primeRank 2 A := by
  have hc : Nat.card A = 2 ^ Module.finrank (ZMod 2) (Additive A) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
  let : IsElementaryAbelian 2 (⊤ : Subgroup A) :=
    IsElementaryAbelian.of_surjective (Subgroup.topEquiv (G := A)).symm.toMonoidHom
      (Subgroup.topEquiv (G := A)).symm.surjective
  have hlo := IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup A)
    ((Subgroup.card_top (G := A)).trans hc)
  have hhi := IsElementaryAbelian.primeRank_le_of_card_le A hc.le
  rw [le_antisymm hhi hlo]
  exact hc

/-- Every elementary actor of rank at least five is conjugate into the
radical at any prescribed three-space; innerness is proved, not assumed. -/
theorem exists_conjugate_le_radical_of_high_rank
    (A : Subgroup M) [IsElementaryAbelian 2 A] (hA : 5 ≤ primeRank 2 A)
    (U : Submodule (ZMod 2) X) (hU : Module.finrank (ZMod 2) U = 3) :
    ∃ a : M, A.map (MulAut.conj a).toMonoidHom ≤ radicalActor U :=
  Classification.exists_conjugate_le_radicalActor A
    (ModuleGeometry.high_rank_inner A hA) hA U hU

theorem exists_conjugate_eq_radicalActor_of_rank_six (A : Subgroup M) [IsElementaryAbelian 2 A]
    (hA : primeRank 2 A = 6) (U : Submodule (ZMod 2) X)
    (hU : Module.finrank (ZMod 2) U = 3) :
    ∃ a : M, A.map (MulAut.conj a).toMonoidHom = radicalActor U := by
  obtain ⟨a, ha⟩ := exists_conjugate_le_radical_of_high_rank A (by omega) U hU
  refine ⟨a, Subgroup.eq_of_le_of_card_ge ha ?_⟩
  rw [radicalActor_card U hU,
    Subgroup.card_map_of_injective (MulAut.conj a).injective, elementary_card, hA]
  decide

theorem exists_conjugate_hyperplane_of_rank_five (A : Subgroup M) [IsElementaryAbelian 2 A]
    (hA : primeRank 2 A = 5) (U : Submodule (ZMod 2) X)
    (hU : Module.finrank (ZMod 2) U = 3) :
    ∃ a : M, A.map (MulAut.conj a).toMonoidHom ≤ radicalActor U ∧
      (A.map (MulAut.conj a).toMonoidHom).relIndex (radicalActor U) = 2 := by
  obtain ⟨a, ha⟩ := exists_conjugate_le_radical_of_high_rank A (by omega) U hU
  refine ⟨a, ha, ?_⟩
  have hm := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup M)
    (A.map (MulAut.conj a).toMonoidHom) (radicalActor U) bot_le ha
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left,
    radicalActor_card U hU, Subgroup.card_map_of_injective (MulAut.conj a).injective,
    elementary_card, hA] at hm
  omega

theorem rank_six_iff_conjugate_radical (A : Subgroup M) [IsElementaryAbelian 2 A]
    (U : Submodule (ZMod 2) X) (hU : Module.finrank (ZMod 2) U = 3) :
    primeRank 2 A = 6 ↔ ∃ a : M, A.map (MulAut.conj a).toMonoidHom = radicalActor U := by
  refine ⟨fun h => exists_conjugate_eq_radicalActor_of_rank_six A h U hU, ?_⟩
  rintro ⟨a, ha⟩
  have hc := radicalActor_card U hU
  rw [← ha, Subgroup.card_map_of_injective (MulAut.conj a).injective,
    elementary_card] at hc
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc

theorem elementary_card_64_iff_conjugate_radical (A : Subgroup M)
    (U : Submodule (ZMod 2) X) (hU : Module.finrank (ZMod 2) U = 3) :
    (IsElementaryAbelian 2 A ∧ Nat.card A = 64) ↔
      ∃ a : M, A.map (MulAut.conj a).toMonoidHom = radicalActor U := by
  constructor
  · rintro ⟨hA, hc⟩
    let := hA
    apply (rank_six_iff_conjugate_radical A U hU).mp
    rw [elementary_card] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc
  · rintro ⟨a, ha⟩
    let e : A ≃* radicalActor U :=
      (A.equivMapOfInjective _ (MulAut.conj a).injective).trans
        (MulEquiv.subgroupCongr ha)
    exact ⟨IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective,
      (Nat.card_congr e.toEquiv).trans (radicalActor_card U hU)⟩

theorem rank_five_iff_conjugate_hyperplane (A : Subgroup M) [IsElementaryAbelian 2 A]
    (U : Submodule (ZMod 2) X) (hU : Module.finrank (ZMod 2) U = 3) :
    primeRank 2 A = 5 ↔ ∃ a : M,
      A.map (MulAut.conj a).toMonoidHom ≤ radicalActor U ∧
      (A.map (MulAut.conj a).toMonoidHom).relIndex (radicalActor U) = 2 := by
  refine ⟨fun h => exists_conjugate_hyperplane_of_rank_five A h U hU, ?_⟩
  rintro ⟨a, ha, hi⟩
  have hc := radicalActor_hyperplane_card U hU _ ha hi
  rw [Subgroup.card_map_of_injective (MulAut.conj a).injective, elementary_card] at hc
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc

/-- The actual linear E.3.30 core is full for every elementary actor of
rank at least five. No placement or fixed-space premise remains. -/
theorem generatedCore_eq_top_of_high_rank (d : CoordinateAction 5)
    (A : Subgroup M) [IsElementaryAbelian 2 A] (hA : 5 ≤ primeRank 2 A) :
    generatedCore (d.representation.comp A.subtype) 3 = ⊤ := by
  obtain ⟨a, ha⟩ := exists_conjugate_le_radical_of_high_rank A hA U₀ finrank_U₀
  exact generatedCore_eq_top_of_conjugate_radical d U₀ finrank_U₀ A a ha

open BinaryNaturalDual.AdaptedPair ModuleGeometry

private theorem cyclic_cases (t : M) (ht : t ^ 2 = 1) (hout : t ∉ L)
    (a : M) (ha : a ∈ Subgroup.zpowers t) : a = 1 ∨ a = t := by
  classical
  have ho : orderOf t = 2 := orderOf_eq_prime ht (fun h => hout (h ▸ L.one_mem))
  rw [mem_zpowers_iff_mem_range_orderOf, ho] at ha
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
  have hnlt := Finset.mem_range.mp hn
  interval_cases n <;> simp

theorem outer_fixed_eq_cyclic_fixedSpace (d : CoordinateAction 5)
    (t : M) (ht : t ^ 2 = 1) (hout : t ∉ L) :
    fixedSpace (linearAction d t) =
      Representation.BinaryOffender.fixedSpace d.representation (Subgroup.zpowers t) := by
  ext v
  simp only [mem_fixedSpace, Representation.BinaryOffender.fixedSpace,
    Representation.mem_invariants]
  change linearAction d t v = v ↔ ∀ a : Subgroup.zpowers t, d.representation a.val v = v
  constructor
  · intro hv a
    rcases cyclic_cases t ht hout a.val a.property with h | h
    · simp [h]
    · simpa [h] using hv
  · intro hv
    exact hv ⟨t, Subgroup.mem_zpowers t⟩

theorem outer_fixed_eq_cyclic_commutator (d : CoordinateAction 5)
    (t : M) (ht : t ^ 2 = 1) (hout : t ∉ L) :
    fixedSpace (linearAction d t) =
      Representation.BinaryOffender.subspaceCommutator d.representation ⊤ (Subgroup.zpowers t) := by
  rw [fixed_eq_displacement d t ht hout]
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact Submodule.subset_span ⟨t, Subgroup.mem_zpowers t, v, Submodule.mem_top, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, _, rfl⟩
    rcases cyclic_cases t ht hout a ha with rfl | rfl
    · simp
    · exact ⟨v, rfl⟩

theorem ambientCommutator_eq_subspaceCommutator (d : CoordinateAction 5) (t : M) :
    ambientCommutator d t = Representation.BinaryOffender.subspaceCommutator
      d.representation (fixedSpace (linearAction d t)) (innerCentralizer t) := by
  rw [ambientCommutator_eq_span, Representation.BinaryOffender.subspaceCommutator]
  congr 1
  ext z
  constructor
  · rintro ⟨a, v, hv, hz⟩
    exact ⟨a.val, a.property, v, hv, hz.symm⟩
  · rintro ⟨a, ha, v, hv, hz⟩
    exact ⟨⟨a, ha⟩, v, hv, hz.symm⟩

end BinaryNaturalDual.FiveActors
