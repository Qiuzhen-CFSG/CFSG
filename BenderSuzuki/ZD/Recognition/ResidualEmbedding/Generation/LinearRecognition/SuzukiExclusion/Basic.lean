module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Setup
public import Theory.SpecificGroups.Suzuki.SubgroupParameters

/-!
# Cardinalities and the even centralizer in the Suzuki branch

The supplied centralizer-closure equalities put every involution of the
pair stabilizer in `J = C_G(L)`, so Cauchy's theorem makes `J` even.
The actual Suzuki order formula identifies the number of points moved by
any such involution with `|L|`. Double transitivity also gives the point
stabilizer formula `|M| = q^3(q^2-q+1)|D|`.

These are inputs to the regularity argument and the primitive-prime
obstruction, not assertions of regularity or of Proposition 14.1.
Source: GLS4, Chapter 2, Lemmas 12.10, 12.14, 14.2(b) and equation (14A),
`refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ} (d : Context Z M z t m)
include d

public theorem Context.involution_mem_centralizer {u : G}
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u) :
    u ∈ centralizer (residualGenerated M z t : Set G) := by
  rw [mem_centralizer_iff]
  intro x hx
  have hxC := centralizerClosure_le Z u ((d.centralizers u huD hu).symm ▸ hx)
  exact mem_centralizer_singleton_iff.mp hxC

public theorem Context.centralizer_even :
    Even (Nat.card (centralizer (residualGenerated M z t : Set G))) := by
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card'
    (G := residualPairStabilizer M t) 2 d.even_pair.two_dvd
  have hui : PFAppendixIII.IsInvolution (u : G) := IsInvolution.map_of_injective
    (orderOf_eq_prime_iff.mp hu).symm (residualPairStabilizer M t).subtype
    Subtype.val_injective
  have huJ := d.involution_mem_centralizer u.property hui
  exact even_iff_two_dvd.mpr (by
    have hd := (centralizer (residualGenerated M z t : Set G)).orderOf_dvd_natCard huJ
    rwa [orderOf_eq_prime hui.sq_eq_one hui.ne_one] at hd)

public theorem Context.card_residualGenerated :
    Nat.card (residualGenerated M z t) =
      ((2 ^ (2 * m + 1)) ^ 2 + 1) * (2 ^ (2 * m + 1)) ^ 2 *
        (2 ^ (2 * m + 1) - 1) := by
  rw [Nat.card_congr d.model.toEquiv]
  exact MatrixGroups.suzukiMatrixGroup_card m (by have := d.parameter_pos; omega)

public theorem Context.card_movedPoints {u : G}
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u) :
    Nat.card {beta : G ⧸ M // u • beta ≠ beta} = Nat.card (residualGenerated M z t) := by
  classical
  let : Fintype (G ⧸ M) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    d.degree, d.fixed u huD hu, d.card_residualGenerated]
  rw [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]
  ring

public theorem Context.card_pointStabilizer :
    Nat.card M = (2 ^ (2 * m + 1)) ^ 3 *
      ((2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1) *
        Nat.card (residualPairStabilizer M t) := by
  let alpha : G ⧸ M := QuotientGroup.mk 1
  have hmove : t⁻¹ • alpha ≠ alpha := by
    intro heq
    apply d.t_not_mem_M
    have hh : t ∈ MulAction.stabilizer G alpha := (inv_smul_eq_iff.mp heq).symm
    rwa [baseCoset_stabilizer M] at hh
  have hc := Converse.card_stabilizer_eq_twoPoint_mul d.action.two_transitive hmove
  rw [← rightConjugate_stabilizer, baseCoset_stabilizer M, d.degree] at hc
  change Nat.card M = Nat.card (residualPairStabilizer M t) * _ at hc
  rw [hc]
  set q := 2 ^ (2 * m + 1)
  have hq : 1 ≤ q := Nat.one_le_two_pow
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have heq : (q ^ 2 + 1) * (q ^ 2 * (q - 1) + 1) - 1 =
      q ^ 3 * (q ^ 2 - q + 1) := by
    have hh : (q ^ 2 + 1) * (q ^ 2 * (q - 1) + 1) =
        q ^ 3 * (q ^ 2 - q + 1) + 1 := by
      zify [hq, hq2]
      ring
    omega
  rw [heq, Nat.mul_comm]

end BenderSuzuki.ZD.SuzukiExclusion
