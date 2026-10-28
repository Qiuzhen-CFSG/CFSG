module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSourceRankOne.FourFixed
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSourceRankOne.OddCore

/-!
# The rank-one two-point branch of the selected-circle argument

An elementary eight in C_M(u) acts on the odd core of C_G(u). Coprime
fixed-point generation uses actor subgroups with cyclic quotient; each has
order at least four and therefore a unique fixed coset. Their centralizers
lie in M, so the odd core lies in M as well. The solvable-circle supplement
then puts the whole C_G(u) in M, a contradiction.

Source: GLS4, Chapter 2, proof of Lemma 16.3(a). The elementary eight is the
precise earlier-source input supplied by Chapter 1, Lemma 4.10.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Hyperplane fixed-point generation absorbs every odd subgroup normalized
by an elementary eight in M, when the original two-point group has rank one. -/
public theorem oddSubgroup_le_of_elementary_eight_of_pair_rank_one
    (ha : ResidualAction Z M) {t : G} (htM : t ∉ M)
    (hrank : ¬ TwoRankAtLeastTwo (residualPairStabilizer M t))
    (E N : Subgroup G) [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (hEM : E ≤ M) (hN : Odd (Nat.card N)) (hEN : E ≤ normalizer N) : N ≤ M := by
  let : CommGroup E := IsMulCommutative.instCommGroup
  let : Fact (IsPGroup 2 E) := ⟨IsElementaryAbelian.isPGroup 2 E⟩
  let : MulDistribMulAction E N := conjMulDistribMulActionOfLeNormalizer E N hEN
  have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup_action
    (G := N) (A := E) 2 hN.coprime_two_left
  have htop : (⊤ : Subgroup N) ≤ M.comap N.subtype := by
    rw [← hgen]
    refine iSup₂_le fun Y hY => ?_
    have hquot : Nat.card (E ⧸ Y) ≤ 2 := by
      apply Nat.le_of_dvd (by decide)
      rw [← hY.exponent_eq_card]
      exact (Group.exponent_quotient_dvd Y).trans (IsElementaryAbelian.exponent_dvd_p 2 E)
    have hprod := card_eq_card_quotient_mul_card_subgroup Y
    rw [hE] at hprod
    let A := Y.map E.subtype
    let : IsElementaryAbelian 2 Y := {
      toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun y =>
        Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 E) (y : E))) }
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.map E.subtype
    have hA : 4 ≤ Nat.card A := by
      rw [card_map_of_injective E.subtype_injective]
      nlinarith
    have hAC := elementary_centralizer_le_of_pair_rank_one ha htM hrank A hA
      ((map_subtype_le Y).trans hEM)
    intro x hx
    apply hAC
    rintro a ⟨y,hy,rfl⟩
    have he := congrArg Subtype.val (hx ⟨y,hy⟩)
    change (y : G) * (x : G) * (y : G)⁻¹ = x at he
    exact mul_inv_eq_iff_eq_mul.mp he
  intro x hx
  exact htop (mem_top (⟨x,hx⟩ : N))

/-- The rank-one branch of Lemma 16.3 after the earlier rank-two-centralizer
lemma supplies the elementary eight in the actual C_M(u). -/
public theorem involutionCentralizer_circle_nonsolvable_of_eight_of_pair_rank_one
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {t u : G} (htM : t ∉ M)
    (hrank : ¬ TwoRankAtLeastTwo (residualPairStabilizer M t))
    (hu : PFAppendixIII.IsInvolution u) (huM : u ∈ M)
    (hC : ¬ centralizer ({u} : Set G) ≤ M)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (hEB : E ≤ centralizer ({u} : Set G)) (hEM : E ≤ M) :
    ¬ Group.IsSolvable (localCircle Z (centralizer ({u} : Set G))) := by
  intro hsol
  let B := centralizer ({u} : Set G)
  let N := (pPrimeCore 2 B).map B.subtype
  have hN : Odd (Nat.card N) := by
    rw [card_map_of_injective B.subtype_injective]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))
  have hEN : E ≤ normalizer N :=
    hEB.trans (B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pPrimeCore 2 B)))
  have hNM := oddSubgroup_le_of_elementary_eight_of_pair_rank_one ha htM hrank E N hE hEM hN hEN
  exact hC ((involutionCentralizer_le_oddCore_sup_intersection h r ha hu huM hC hsol).trans
    (sup_le hNM inf_le_right))

end BenderSuzuki.ZD
