module
public import CFSG.Quasithin.ChapterC.Section06.Original.Definitions
public import CFSG.Quasithin.MainConverse.RankOneSections.Linear
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.GroupTheory.PrimeRankCubeFree
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# The original C.6 quotient models are SQTK

Binary PSL₂ has cyclic odd Sylow subgroups. Two-group kernels and
quotients preserve odd-prime ranks, while Dickson's theorem supplies its
full known-simple section catalogue. The S₃ and wreath rows are solvable
of orders six and seventy-two, so their odd-prime ranks are at most two.
These facts discharge the local SQTK input of the actual C.5 producer.
Source: Aschbacher--Smith C.6.1(i), printed pp.164--165.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.Section06.Original
variable {A : Type*} [Group A] [Finite A]

private theorem constructed_known (h : IsKGroup KnownSimple.IsConstructedCarrier A) :
    IsKGroup KnownSimple.IsKnownSimple A := by
  intro S _ hs U f hf
  let : Finite S := Finite.of_surjective f hf
  exact ⟨inferInstance,hs,(h S hs U f hf).isKnownSimpleCarrier⟩

private theorem solvable_known [Group.IsSolvable A] : IsKGroup KnownSimple.IsKnownSimple A :=
  constructed_known (MainConverse.solvable_isKGroup_constructed A)

private theorem linear_rank {n : ℕ} (h : ClassicalGroup.IsPSL A 2 (2^n))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) : primeRank p A ≤ 1 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [←Nat.card_eq_fintype_card] using hF)
  let f := e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm
  rw [primeRank_equiv p f]
  exact Matrix.SL2.binary_odd_primeRank_le_one ho

private theorem cubic_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  exact Group.isSolvable_of_isSolvable_injective
    (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))

private theorem wreath_solvable : Group.IsSolvable CubicWreath := by
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := cubic_solvable
  let C := Multiplicative (ZMod 2)
  let f : CubicWreath →* C := RegularWreathProduct.rightHom
  let c : C := Multiplicative.ofAdd 1
  have hcoord : ∀ i : C, i = 1 ∨ i = c := by decide
  let j : f.ker →* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := {
    toFun := fun x => (x.val.left 1,x.val.left c)
    map_one' := rfl
    map_mul' := fun x y => by
      have hx : x.val.right = 1 := x.property
      ext <;> simp [RegularWreathProduct.mul_left,hx] }
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply RegularWreathProduct.ext
    · funext i
      rcases hcoord i with rfl | rfl
      · exact congrArg Prod.fst hxy
      · exact congrArg Prod.snd hxy
    · exact x.property.trans y.property.symm
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hj
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [range_subtype])

private theorem rank_of_card_dvd (h : Nat.card A ∣ 72)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) : primeRank p A ≤ 2 := by
  apply primeRank_le_two_of_cube_not_dvd
  intro hh
  have hd : p^3 ∣ 72 := hh.trans h
  have hp := (Fact.out : p.Prime).two_le
  have hle := Nat.le_of_dvd (by decide : 0 < 72) hd
  have hp5 : p < 5 := by
    by_contra! hh
    have hc := Nat.pow_le_pow_left hh 3
    norm_num at hc
    omega
  interval_cases p
  all_goals solve | norm_num at hd | norm_num at ho

theorem QuotientModels.sqtk (h : QuotientModels A) : IsSQTK KnownSimple.IsKnownSimple A := by
  let Q := pCore 2 A
  let B := A ⧸ Q
  have hKQ : IsKGroup KnownSimple.IsKnownSimple Q := by
    let : Group.IsNilpotent Q := pCore_isPGroup.isNilpotent
    exact solvable_known
  have hB : IsSQTK KnownSimple.IsKnownSimple B := by
    change (∃ n : ℕ, ClassicalGroup.IsPSL (pResidual 2 B) 2 (2^n)) ∨
      Nonempty (B ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (B ≃* CubicWreath) at h
    rcases h with hn | he | he
    · obtain ⟨n,hn⟩ := hn
      have hKL : IsKGroup KnownSimple.IsKnownSimple (pResidual 2 B) :=
        constructed_known (MainConverse.psl2_isKGroup_constructed hn)
      have hKB : IsKGroup KnownSimple.IsKnownSimple B := by
        apply IsKGroup.of_normal_quotient (pResidual 2 B) hKL
        let : Group.IsNilpotent (B ⧸ pResidual 2 B) := (isPGroup_quotient_pResidual 2).isNilpotent
        exact solvable_known
      refine ⟨?_,hKB⟩
      intro p hp ho
      let : Fact p.Prime := ⟨hp⟩
      rw [←ResidualCentralizerRank.primeRank_residual (q := 2) (Nat.coprime_two_left.mpr ho)]
      exact (linear_rank hn ho).trans (by decide)
    · let e := Classical.choice he
      let : Group.IsSolvable (Equiv.Perm (Fin 3)) := cubic_solvable
      let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      refine ⟨?_,solvable_known⟩
      intro p hp ho
      let : Fact p.Prime := ⟨hp⟩
      apply rank_of_card_dvd (p := p) ?_ ho
      rw [Nat.card_congr e.toEquiv]
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
    · let e := Classical.choice he
      let : Group.IsSolvable CubicWreath := wreath_solvable
      let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      refine ⟨?_,solvable_known⟩
      intro p hp ho
      let : Fact p.Prime := ⟨hp⟩
      apply rank_of_card_dvd (p := p) ?_ ho
      rw [Nat.card_congr e.toEquiv,RegularWreathProduct.card]
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
  refine ⟨?_,IsKGroup.of_normal_quotient Q hKQ hB.isKGroup⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  rw [←primeRank_quotient_eq_of_isTwoGroup p ho Q pCore_isPGroup]
  exact hB.stronglyQuasithin p hp ho

/-- The linear residual preserves the rank-one bound through both two-layers. -/
theorem linear_core_odd_rank {n p : ℕ} [Fact p.Prime] (ho : Odd p)
    (h : ClassicalGroup.IsPSL (pResidual 2 (A ⧸ pCore 2 A)) 2 (2^n)) :
    primeRank p A ≤ 1 := by
  rw [←primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 A) pCore_isPGroup,
    ←ResidualCentralizerRank.primeRank_residual (q := 2) (Nat.coprime_two_left.mpr ho)]
  exact linear_rank h ho

/-- Both non-linear quotient alternatives make the original group solvable. -/
theorem cubic_models_solvable
    (h : Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty ((A ⧸ pCore 2 A) ≃* CubicWreath)) : Group.IsSolvable A := by
  have hq : Group.IsSolvable (A ⧸ pCore 2 A) := by
    rcases h with he | he
    · let : Group.IsSolvable (Equiv.Perm (Fin 3)) := cubic_solvable
      exact Group.isSolvable_of_isSolvable_injective (f := (Classical.choice he).toMonoidHom) (Classical.choice he).injective
    · let : Group.IsSolvable CubicWreath := wreath_solvable
      exact Group.isSolvable_of_isSolvable_injective (f := (Classical.choice he).toMonoidHom) (Classical.choice he).injective
  let := hq
  let : Group.IsNilpotent (pCore 2 A) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 A)).mpr ⟨inferInstance,inferInstance⟩
end CFSG.Quasithin.ChapterC.Section06.Original
