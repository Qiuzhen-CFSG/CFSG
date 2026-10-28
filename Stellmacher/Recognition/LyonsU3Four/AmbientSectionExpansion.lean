module

public import Stellmacher.Recognition.LyonsU3Four.AmbientSectionPreliminaries
public import Theory.Character.ModularBlock.CartanReindex
public import Theory.Character.RealOrderFourIntegral

/-!
# Ordered genuine integral ambient section expansions

We retain the actual odd-core quotient of the involution centralizer, choose a
nonprincipal complement character of order five, and relabel the genuine local
Brauer family by its powers `[0, 1, 2, 4, 3]`. Central-involution decomposition
then gives integral coefficients in precisely this ordered family.

At an order-four element, fusion with the inverse gives an integral ordinary
value. The actual local principal Brauer family is a singleton with value one
on odd elements, so this value is the coefficient throughout its two-section.
These two constructions establish equation (3.1) without additional identities
for Gram matrices, contributions, congruences or Galois actions.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), pp. 373–374,
equation (3.1).
-/

public section
noncomputable section
open ModularBlock PrincipalBlockConstruction

namespace Stellmacher.Recognition.LyonsU3Four
attribute [local instance] Fintype.ofFinite
private theorem exists_fiveLinear_ordered : ∃ (χ : FiveLinearIndex) (e : Fin 5 ≃ FiveLinearIndex),
    orderOf χ = 5 ∧ ∀ i, e i = χ ^ GeneralizedDecompositionData.basicExponent i := by
  have : Nontrivial FiveLinearIndex := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [fiveLinearIndex_card]; decide)
  obtain ⟨χ, hne⟩ := exists_ne (1 : FiveLinearIndex)
  have hp : χ ^ 5 = 1 := by
    apply MonoidHom.ext
    intro x
    change χ x ^ 5 = 1
    have hx : x ^ 5 = 1 := by
      simpa [FiveComplement, Nat.card_eq_fintype_card] using (pow_card_eq_one' (x := x))
    rw [← map_pow, hx, map_one]
  have hχ : orderOf χ = 5 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp (orderOf_dvd_of_pow_eq_one hp) with he | he
    · exact False.elim (hne (orderOf_eq_one_iff.mp he))
    · exact he
  let f : Fin 5 → FiveLinearIndex := fun i => χ ^ GeneralizedDecompositionData.basicExponent i
  have hi : Function.Injective f := by
    intro i j hij
    have he := ((isOfFinOrder_iff_pow_eq_one.mpr ⟨5, by decide, hp⟩).pow_inj_mod).mp
      (show χ ^ GeneralizedDecompositionData.basicExponent i =
        χ ^ GeneralizedDecompositionData.basicExponent j from hij)
    rw [hχ] at he
    fin_cases i <;> fin_cases j <;>
      first | rfl | norm_num [GeneralizedDecompositionData.basicExponent] at he
  let e := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hi, by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, fiveLinearIndex_card]⟩)
  exact ⟨χ, e, hχ, fun _ => rfl⟩

variable {G : Type*} [Group G] [Finite G]
open Subgroup Cartan

/-- Construct the actual quotient coordinates and genuine family in Lyons’s order. -/
theorem exists_fiveSectionModel_brauerData
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S)
    (b : PrincipalCongruenceBlockData G) {z : G} (hz : z ∈ centerImage S) (hz1 : z ≠ 1) :
    ∃ M : FiveSectionModel S z, Nonempty (M.BrauerData b) := by
  obtain ⟨β, α, hβ, hα, e, he⟩ := exists_orderFifteen_centralizerFive_equiv S h d hz hz1
  obtain ⟨χ, en, hχ, hen⟩ := exists_fiveLinear_ordered
  let M : FiveSectionModel S z := ⟨hz, β, hβ, α, hα, e, he, χ, hχ, en, hen⟩
  obtain ⟨a, hd, hc, hv⟩ := involutionCentralizer_principal_decomposition_of_equiv
    S h β hβ α hα z e (CompatibleBrauerBlock.localData b _)
  let σ : Fin 5 ≃ Fin 5 := en.trans fiveLinearEnumeration.symm
  refine ⟨M, ⟨⟨a.reindex σ, (fun i => hd (σ i)), ?_, ?_⟩⟩⟩
  · intro i k
    rw [PrincipalDecompositionData.reindex_cartan, hc]
    simp only [Equiv.apply_eq_iff_eq]
  · intro i v hvodd
    change BrauerCharacter.value _ (a.family.rep (σ i)) v = _
    rw [hv _ v hvodd]
    have hσ : fiveLinearEnumeration (σ i) = χ ^ GeneralizedDecompositionData.basicExponent i := by
      simpa only [σ, Equiv.trans_apply, Equiv.apply_symm_apply] using hen i
    rw [hσ, M.mu_apply]
    rfl
end Stellmacher.Recognition.LyonsU3Four

namespace Stellmacher.Recognition.LyonsU3Four
open Subgroup ModularBlock PrincipalBlockConstruction Cartan
open ModularBlock.TwoSectionContribution
attribute [local instance] Fintype.ofFinite Classical.propDecidable
variable {G : Type*} [Group G] [Finite G]

/-- Genuine integral expansions on both nonidentity two-sections, with the
involution basis ordered as the powers `[0, 1, 2, 4, 3]` of an order-five character. -/
theorem exists_ordered_ambient_section_expansion
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S)
    (b : PrincipalCongruenceBlockData G) (t : S) (ht : orderOf t = 4) :
    ∃ M : FiveSectionModel S ((t : G)^2), ∃ _a : M.BrauerData b,
      ∃ c : GeneralizedDecompositionData {i // i ∈ b.block},
        c.Equation3_1 (fun j g => b.chi j.val (ConjClasses.mk g))
          (t : G) ((t : G)^2) M.mu := by
  have hz := orderFour_square_mem_centerImage S h t ht
  obtain ⟨M, ⟨a⟩⟩ := exists_fiveSectionModel_brauerData S h d b hz.1 hz.2
  have htG : orderOf (t : G) = 4 := (Subgroup.orderOf_coe t).trans ht
  have ht4 : (t : G)^4 = 1 := by rw [← htG]; exact pow_orderOf_eq_one _
  have hz2 : ((t : G)^2)^2 = 1 := by simpa only [← pow_mul] using ht4
  let χ : {j // j ∈ b.block} → ClassFunction G := fun j g => b.chi j.val (ConjClasses.mk g)
  have hχ (j : {j // j ∈ b.block}) : IsCharacter (χ j) := by
    obtain ⟨n, ρ, hρ⟩ := (b.complete.1 j.val).1
    exact ⟨n, ρ, by funext g; dsimp only [χ]; rw [hρ]; rfl⟩
  have hm (j : {j // j ∈ b.block}) :
      ∃ i ∈ b.block, ∀ g, χ j g = b.chi i (ConjClasses.mk g) :=
    ⟨j.val, j.property, fun _ => rfl⟩
  choose cZ hcZ _ using fun j => exists_int_of_sq_eq_one b (χ j) (hχ j) (hm j)
    ((t : G)^2) hz2 a.decomposition
  have hfuse : IsConj (t : G) (t : G)⁻¹ :=
    order_four_isConj_of_automizer_eq_fifteen S h d.automizer_fifteen htG
      (by simpa only [orderOf_inv] using htG)
  choose cT hcT using fun j => (hχ j).exists_int_of_fourth_power_of_isConj_inv
    (t : G) ht4 hfuse
  let C := centralizer ({(t : G)} : Set G)
  let l := CompatibleBrauerBlock.localData b C
  obtain ⟨aT, hdT, _⟩ := orderFourCentralizer_principal_cartan S d t ht l
  have hN : Odd (Nat.card (pPrimeCore 2 C)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := C))
  have hQ : IsPGroup 2 (C ⧸ pPrimeCore 2 C) :=
    IsPGroup.of_card (n := 4) (by simpa using d.orderFour_quotient_card t ht)
  let c : GeneralizedDecompositionData {j // j ∈ b.block} := ⟨cT, fun i j => cZ j i⟩
  refine ⟨M, a, c, ?_, ?_⟩
  · intro j v hv
    obtain ⟨u, hu, hue⟩ := exists_complex b (χ j) (hm j) (t : G) ⟨2, ht4⟩ aT
    have hu0 : u 0 = (cT j : ℂ) := by
      simpa only [Fin.sum_univ_one, hdT, Nat.cast_one, mul_one, hcT j] using hue.symm
    have hvone := brauerValue_eq_one_of_oddNormal_twoGroup l aT.family
      (pPrimeCore 2 C) hN hQ hdT v hv
    change χ j ((t : G) * (v : G)) = (cT j : ℂ)
    calc
      _ = u 0 * BrauerCharacter.value l (aT.family.rep 0) v := by
        simpa only [Fin.sum_univ_one] using hu v hv
      _ = _ := by rw [hvone, mul_one, hu0]
  · intro j v hv
    exact (hcZ j v hv).trans (Finset.sum_congr rfl (fun i _ => by rw [a.value i v hv]))
end Stellmacher.Recognition.LyonsU3Four
