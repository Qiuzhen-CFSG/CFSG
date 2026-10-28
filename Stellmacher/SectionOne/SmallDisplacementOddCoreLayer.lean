module
public import Stellmacher.SectionOne.LemmaOneSeven
public import Stellmacher.SectionOne.RankOneLocalSL2Coordinate

/-!
# Small displacement and the one-seven odd-core layer

In the faithful finite binary action of Section One, an elementary actor
inside a Sylow subgroup whose total displacement has order at most two
lies in the odd-core layer of the acting group. For each nonidentity actor,
involution rank-nullity bounds its fixed index by two, so its cyclic
subgroup is an offender. Their join lies in the one-seven normal product.
The quotient of that product by its ambient odd-core intersection is a
two-group, and normality puts its image in the quotient two-core.

The original action and Sylow are retained. This is the (1.7) step needed
for the final Frattini/mixed-line action in Stellmacher (9.3), printed p.50
of `refs/files/stellmacher-n-group.pdf`; it uses only the proved small-m
one-seven factor structure, with no unrestricted (1.6) dependency.
-/

namespace Stellmacher.SectionOne
universe u

private theorem small_displacement_le_oneJ
    {X V : Type u} [Group X] [Finite X] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [Nontrivial V] [MulDistribMulAction X V]
    (S : Sylow 2 X) (Y : Subgroup X) [IsElementaryAbelian 2 Y]
    (hle : Y ≤ (S : Subgroup X))
    (hsmall : Nat.card (commutatorAction Y V) ≤ 2) :
    Y ≤ oneJ (V := V) (S : Subgroup X) := by
  intro y hy
  by_cases hone : y = 1
  · subst y
    exact Subgroup.one_mem _
  let Z := Subgroup.zpowers y
  have hZY : Z ≤ Y := Subgroup.zpowers_le.mpr hy
  have hy2 : y ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) y hy
  have hZcard : Nat.card Z = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hy2 hone]
  have hcomm : commutatorAction Z V ≤ commutatorAction Y V := by
    rw [commutatorAction_eq_closure, Subgroup.closure_le]
    rintro _ ⟨actor, vector, rfl⟩
    exact Subgroup.subset_closure ⟨⟨actor, hZY actor.property⟩, vector, Subgroup.mem_top vector, rfl⟩
  have hbound := (Subgroup.card_le_of_le hcomm).trans hsmall
  let actor : Z := ⟨y,Subgroup.mem_zpowers y⟩
  have hactor : actor ≠ 1 ∧ actor ^ 2 = 1 :=
    ⟨fun h => hone (congrArg Subtype.val h), Subtype.ext hy2⟩
  have hproduct := (card_two_action_fixed_commutator_card_data (U := V) actor hactor hZcard).1
  have hA : oneA (V := V) (S : Subgroup X) Z := by
    refine ⟨hZY.trans hle, IsElementaryAbelian.zpowers_of_pow_eq_one hy2, ?_⟩
    unfold m
    have hfixedPositive : (0 : ℚ) < Nat.card (FixedPoints.subgroup Z V) :=
      Nat.cast_pos.mpr Nat.card_pos
    have hactorPositive : (0 : ℚ) < Nat.card Z := Nat.cast_pos.mpr Nat.card_pos
    apply (div_le_one (mul_pos hfixedPositive hactorPositive)).mpr
    rw [hZcard, hproduct, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hbound) (by positivity)
  exact (le_sSup hA : Z ≤ oneJ (V := V) (S : Subgroup X)) (Subgroup.mem_zpowers y)

/-- An elementary actor with displacement of order at most two lies in the odd-core layer. -/
public theorem oneSeven_small_displacement_le_oddCoreLayer
    {X V : Type u} [Group X] [Finite X] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [Nontrivial V] [MulDistribMulAction X V]
    (h : Hypotheses X V) (S : Sylow 2 X) (Y : Subgroup X)
    [IsElementaryAbelian 2 Y]
    (hle : Y ≤ (S : Subgroup X))
    (hsmall : Nat.card (commutatorAction Y V) ≤ 2) :
    Y.map (QuotientGroup.mk' (pPrimeCore 2 X)) ≤ pCore 2 (X ⧸ pPrimeCore 2 X) := by
  let E := oneSevenGenerated (G := X) (V := V)
  let F := oneSevenFactors (G := X) (V := V)
  have hYJ := small_displacement_le_oneJ S Y hle hsmall
  have hYE : Y ≤ E := by
    rw [(oneSeven_global_identification h S).1] at hYJ
    exact hYJ.trans inf_le_right
  obtain ⟨hnormal, hprod, _⟩ := oneSeven_global_product h S
  have hF : ∀ D ∈ F, IsOneSevenFactor (V := V) D :=
    fun D hD => (mem_oneSevenFactors_iff D).mp hD
  have hp := oneSevenFactor_oddCore_quotient_isPGroup E F hprod hF
  exact (Subgroup.map_mono hYE).trans
    (le_sSup ⟨hnormal.map _ (QuotientGroup.mk'_surjective _), hp⟩)

end Stellmacher.SectionOne
