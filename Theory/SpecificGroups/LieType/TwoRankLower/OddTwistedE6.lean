module
public import Theory.GroupTheory.IndependentInvolutionsRank
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.TwistedE6.Projection
/-!
# An elementary eight in odd-characteristic twisted E6

The three graph-fixed sign actors independently invert the fixed-field part
of the paired root coordinate and the two remaining fixed root coordinates.
Their images commute and square to one. Faithfulness of the existing signed
chart proves independence in the literal central quotient.
Source: Aschbacher--Smith A.2.12, printed p.36, and A.2.17, p.39.
-/
public noncomputable section
open TwistedE6 TwistedE6.FoldedSubsystem
open ExceptionalSplit.OddRankFour
namespace TwistedE6.RankFour.TwoRank
attribute [local instance] Classical.decEq
variable (p : ℕ) [Fact p.Prime] (m : ℕ)
private def actorIndex : Fin 3 → Fin 4 := ![1,3,2]
private def actor (i : Fin 3) : definingCharacteristicSubgroup p m := foldedSignActor p m (actorIndex i)
private def parameter : (Fin 3 → Multiplicative (FixedField p m)) →* Parameters p m where
  toFun a := (Multiplicative.ofAdd ((a 0).toAdd : CoefficientField p m),a 1,a 2)
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem parameter_injective : Function.Injective (parameter p m) := by
  intro a b h
  have h0 : a 0 = b 0 := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg (fun z : Parameters p m => z.1.toAdd) h
  have h1 : a 1 = b 1 := congrArg (fun z : Parameters p m => z.2.1) h
  have h2 : a 2 = b 2 := congrArg (fun z : Parameters p m => z.2.2) h
  funext i
  fin_cases i <;> assumption

private theorem actor_commute (i j : Fin 3) : Commute (actor p m i) (actor p m j) := by
  apply ambientInclusion_injective p m
  simp only [map_mul,actor,foldedSignActor_coroot]
  let C := Subgroup.closure (Set.range (nativeCoroot (CoefficientField p m)))
  have hn (i : Fin 6) : nativeCoroot (CoefficientField p m) i ∈ C := Subgroup.subset_closure ⟨i,rfl⟩
  let : IsMulCommutative C := Subgroup.isMulCommutative_closure (by
    rintro x ⟨k,rfl⟩ y ⟨l,rfl⟩
    exact elementaryCoroot_commute _ _)
  let : CommGroup C := IsMulCommutative.instCommGroup
  have hm (i : Fin 3) :
      (![nativeCoroot (CoefficientField p m) 0 * nativeCoroot (CoefficientField p m) 5,
        nativeCoroot (CoefficientField p m) 1 * nativeCoroot (CoefficientField p m) 4,
        nativeCoroot (CoefficientField p m) 2,nativeCoroot (CoefficientField p m) 3] (actorIndex i)) ∈ C := by
    fin_cases i
    · exact C.mul_mem (hn 1) (hn 4)
    · exact hn 3
    · exact hn 2
  exact congrArg (fun z : C => z.val.val) (mul_comm (⟨_,hm i⟩:C) (⟨_,hm j⟩:C))

private theorem actor_chart (i : Fin 3) (a : Fin 3 → Multiplicative (FixedField p m)) :
    actor p m i * chartCover p m (parameter p m a) * (actor p m i)⁻¹ =
      chartCover p m (parameter p m (CoordinateInversion.invertCoordinate i a)) := by
  apply ambientInclusion_injective p m
  simp only [map_mul,map_inv,chartCover_native,actor,foldedSignActor_coroot]
  have hmul (x y : splitCarrier (CoefficientField p m)) : (x*y).val=x.val*y.val := rfl
  have hinv (x : splitCarrier (CoefficientField p m)) : (x⁻¹).val=x.val⁻¹ := rfl
  have hpair := congrArg Subtype.val (E6.coroot_pair_chart (CoefficientField p m)
    (nativeParameters p m (parameter p m a)))
  have htwo := congrArg Subtype.val (E6.coroot_three_chart (CoefficientField p m)
    (nativeParameters p m (parameter p m a)))
  have hthree := congrArg Subtype.val (E6.coroot_two_chart (CoefficientField p m)
    (nativeParameters p m (parameter p m a)))
  simp only [hmul,hinv] at hpair htwo hthree
  fin_cases i
  · change (E6.coroot (CoefficientField p m) 1 * E6.coroot (CoefficientField p m) 4).val *
      (E6.chart (CoefficientField p m) (nativeParameters p m (parameter p m a))).val *
      (E6.coroot (CoefficientField p m) 1 * E6.coroot (CoefficientField p m) 4).val⁻¹ = _
    simp only [hmul]
    rw [hpair]
    congr 2
    funext k
    fin_cases k <;> simp [nativeParameters,parameter,CoordinateInversion.invertCoordinate,Fin.ext_iff]
    change Multiplicative.ofAdd (-((a 0).toAdd : CoefficientField p m)) =
      Multiplicative.ofAdd (fieldTwist p m (-((a 0).toAdd : CoefficientField p m)))
    rw [map_neg (fieldTwist p m)]
    congr 2
    exact ((a 0).toAdd).property.symm
  · change (E6.coroot (CoefficientField p m) 3).val *
      (E6.chart (CoefficientField p m) (nativeParameters p m (parameter p m a))).val *
      (E6.coroot (CoefficientField p m) 3).val⁻¹ = _
    rw [htwo]
    congr 2
  · change (E6.coroot (CoefficientField p m) 2).val *
      (E6.chart (CoefficientField p m) (nativeParameters p m (parameter p m a))).val *
      (E6.coroot (CoefficientField p m) 2).val⁻¹ = _
    rw [hthree]
    congr 2

/-- The literal twisted E6 model contains an elementary eight in odd characteristic. -/
theorem three_le (hp : p ≠ 2) : 3 ≤ primeRank 2 (Model p m) := by
  let j := (chartModel p m).comp (parameter p m)
  let d : Fin 3 → Model p m := fun i => toModel p m (actor p m i)
  refine IndependentInvolutions.three_le_of_coordinate_actors j
    ((chartModel_injective p m hp).comp (parameter_injective p m))
    (Multiplicative.ofAdd (1 : FixedField p m)) ?_ d ?_ ?_ ?_ id Function.injective_id
  · intro h
    have he : (-1 : CoefficientField p m)=1 := congrArg
      (fun z : Multiplicative (FixedField p m) => (z.toAdd : CoefficientField p m)) h
    exact coefficient_two_ne_zero p m hp (by linear_combination -he)
  · intro i
    change (toModel p m (actor p m i)) ^ 2 = 1
    rw [← map_pow,actor,foldedSignActor_square,map_one]
  · intro i k
    exact (actor_commute p m i k).map (toModel p m)
  · intro i a
    change toModel p m (actor p m i) * toModel p m (chartCover p m (parameter p m a)) *
      (toModel p m (actor p m i))⁻¹ = _
    rw [← map_inv,← map_mul,← map_mul,actor_chart]
    rfl
end TwistedE6.RankFour.TwoRank
