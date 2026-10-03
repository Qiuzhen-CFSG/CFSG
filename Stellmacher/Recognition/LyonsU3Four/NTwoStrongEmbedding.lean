module

public import Stellmacher.Recognition.LyonsU3Four
public import Stellmacher.Recognition.LyonsU3Four.InvolutionFusion
public import Theory.GroupTheory.ZStar.OddCore
public import Theory.Character.SchurDegreeTwelve
public import Stellmacher.Recognition.LyonsU3Four.ActionIndexFromLocalData
public import BenderSuzuki.SE.SimpleOddCore

/-!
# Assembly of the N2 Lyons strong-embedding argument

The ambient character calculation supplies a rational irreducible character of
degree twelve and the centralizer order formula. A separate coprime-action
argument supplies a fourth-power divisor of every nontrivial centralizer index.
Schur's bound then forces the centralizer equality and hence strong embedding.

The centralizer of the Sylow center is normal in its normalizer. Triviality of the
normalizer odd core implies that this normal centralizer also has trivial odd
core; this is the input supplied by the simple strong-embedding odd-core theorem. Involution fusion transports the result
to every involution centralizer.

The N2 hypothesis supplies the local data and hence the action-index obstruction.
The remaining explicit inputs are the ambient character and its order formula.
Source: Lyons, *A Characterization of the Group U₃(4)* (1972), §§4–5,
pp. 380–386; the numerical assembly adapts the saved earlier Lyons proof.
-/

namespace Stellmacher.Recognition.LyonsU3Four

open Subgroup

/-- The numerical inputs in §5 force the involution centralizer to centralize
the entire Sylow center. The index here is the actual subgroup index. -/
public theorem centralizer_eq_of_numerical_inputs
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {z : G} (hz : z ∈ centerImage S)
    (hformula : Nat.card G * Nat.card (Subgroup.centralizer (centerImage S : Set G)) ^ 2 =
      195 * Nat.card (Subgroup.centralizer ({z} : Set G)) ^ 3)
    (hbound : Nat.card G ∣ schurBound)
    (hindex : Subgroup.centralizer ({z} : Set G) ≠
        Subgroup.centralizer (centerImage S : Set G) →
      ∃ p : ℕ, p.Prime ∧ p ^ 4 ∣
        (Subgroup.centralizer (centerImage S : Set G)).relIndex
          (Subgroup.centralizer ({z} : Set G))) :
    Subgroup.centralizer ({z} : Set G) =
      Subgroup.centralizer (centerImage S : Set G) := by
  let C := Subgroup.centralizer ({z} : Set G)
  let D := Subgroup.centralizer (centerImage S : Set G)
  have hDC : D ≤ C := Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hz)
  have hcard : Nat.card D * D.relIndex C = Nat.card C := by
    have heq := (D.subgroupOf C).card_mul_index
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv] at heq
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := hindex hne
  exact no_prime_fourth_dvd_index (Nat.card G) (Nat.card C) (Nat.card D)
    (D.relIndex C) Nat.card_pos hcard hformula hbound p hp hpdvd

/-- The centralizer equality makes every involution centralizer core-free.
The normalizer odd-core input is supplied by the simple strong-embedding
theorem; normality is needed only inside that normalizer. -/
public theorem involutionCentralizer_oddCore_eq_bot_of_centralizer_eq_and_normalizer_core
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S)
    (hcent : ∀ z ∈ centerImage S, z ≠ 1 →
      centralizer ({z} : Set G) = centralizer (centerImage S : Set G))
    (hMcore : pPrimeCore 2 (normalizer (centerImage S : Set G)) = ⊥)
    {x : G} (hx : orderOf x = 2) :
    pPrimeCore 2 (centralizer ({x} : Set G)) = ⊥ := by
  let M := normalizer (centerImage S : Set G)
  let D := centralizer (centerImage S : Set G)
  have hDM : D ≤ M := Subgroup.centralizer_le_normalizer _
  have hDcore : pPrimeCore 2 D = ⊥ := by
    have hsub : pPrimeCore 2 (D.subgroupOf M) = ⊥ :=
      Glauberman.ZStar.pPrimeCore_subgroup_eq_bot_of_normal hMcore _
        (normal_subgroupOf_centralizer_normalizer _)
    let e : D.subgroupOf M ≃* D := subgroupOfEquivOfLe hDM
    have he := pPrimeCore_map_iso 2 e
    rw [hsub, Subgroup.map_bot] at he
    exact he.symm
  obtain ⟨z, hz, hz1, hxz⟩ := involution_isConj_centerImage S h hx
  have hzcore : pPrimeCore 2 (centralizer ({z} : Set G)) = ⊥ := by
    rw [hcent z hz hz1]
    exact hDcore
  obtain ⟨g, hg⟩ := isConj_iff.mp hxz
  let e := MulAut.conj g
  have hex : e x = z := hg
  have heC : (centralizer ({x} : Set G)).map e.toMonoidHom =
      centralizer ({z} : Set G) := by
    apply le_antisymm
    · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom, hex] using
        map_centralizer_le_centralizer_image ({x} : Set G) e.toMonoidHom
    · intro a ha
      refine ⟨e.symm a, ?_, e.apply_symm_apply a⟩
      apply mem_centralizer_singleton_iff.mpr
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply, hex] using
        mem_centralizer_singleton_iff.mp ha
  let eC : centralizer ({x} : Set G) ≃* centralizer ({z} : Set G) :=
    ((centralizer ({x} : Set G)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr heC)
  apply (Subgroup.map_eq_bot_iff_of_injective
    (H := pPrimeCore 2 (centralizer ({x} : Set G))) (f := eC.toMonoidHom) eC.injective).mp
  rw [pPrimeCore_map_iso 2 eC, hzcore]

/-- Final assembly from the two independent missing mathematical inputs.
The degree-twelve character discharges Schur's bound rather than assuming it. -/
public theorem centralizer_eq_and_stronglyEmbedded_of_character_and_index
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S)
    (hchar : ∃ χ : ClassFunction G, IsIrreducibleCharacter χ ∧ χ 1 = 12 ∧
      ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ))
    (hformula : ∀ z ∈ centerImage S, z ≠ 1 →
      Nat.card G * Nat.card (centralizer (centerImage S : Set G)) ^ 2 =
        195 * Nat.card (centralizer ({z} : Set G)) ^ 3)
    (hindex : ∀ z ∈ centerImage S, z ≠ 1 →
      centralizer ({z} : Set G) ≠ centralizer (centerImage S : Set G) →
        ∃ p : ℕ, p.Prime ∧ p ^ 4 ∣
          (centralizer (centerImage S : Set G)).relIndex
            (centralizer ({z} : Set G))) :
    (∀ z ∈ centerImage S, z ≠ 1 →
      centralizer ({z} : Set G) = centralizer (centerImage S : Set G)) ∧
    IsStronglyEmbedded (normalizer (centerImage S : Set G)) := by
  obtain ⟨χ, hχ, hdegree, hrat⟩ := hchar
  have hbound : Nat.card G ∣ schurBound :=
    hχ.card_dvd_degree_twelve_bound S h.card hdegree hrat
  have hcent : ∀ z ∈ centerImage S, z ≠ 1 →
      centralizer ({z} : Set G) = centralizer (centerImage S : Set G) := by
    intro z hz hz1
    exact centralizer_eq_of_numerical_inputs S hz (hformula z hz hz1) hbound
      (hindex z hz hz1)
  exact ⟨hcent, stronglyEmbedded_of_centralizer_eq S h hcent⟩

/-- Strong embedding kills the normalizer odd core, and centralizer normality
and involution fusion then kill every involution-centralizer odd core. -/
public theorem involutionCentralizer_oddCore_eq_bot_of_centralizer_eq
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S)
    (hcent : ∀ z ∈ centerImage S, z ≠ 1 →
      centralizer ({z} : Set G) = centralizer (centerImage S : Set G))
    {x : G} (hx : orderOf x = 2) :
    pPrimeCore 2 (centralizer ({x} : Set G)) = ⊥ := by
  have hM := stronglyEmbedded_of_centralizer_eq S h hcent
  have hMB : BenderSuzuki.IsStronglyEmbedded
      (normalizer (centerImage S : Set G)) := by
    let M := normalizer (centerImage S : Set G)
    refine ⟨hM.1, hM.2.1, ?_⟩
    intro g hg x hxM hxright
    have hginv : g⁻¹ ∉ M := fun hi => hg (by simpa using M.inv_mem hi)
    apply hM.2.2 g⁻¹ hginv x
    refine ⟨hxM, ?_⟩
    simpa [BenderSuzuki.PFchapter1section1.rightConjugate, Subgroup.conjBy] using hxright
  exact involutionCentralizer_oddCore_eq_bot_of_centralizer_eq_and_normalizer_core S h hcent
    (BenderSuzuki.IsStronglyEmbedded.pPrimeCore_eq_bot_of_isSimple hMB) hx

/-- For the actual N2 consumer the coprime-action index obstruction follows
from local solvability. Only the ambient character calculation remains an input. -/
public theorem centralizer_eq_and_stronglyEmbedded_of_isNTwoGroup_and_character
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (h : SylowStructure S)
    (hchar : ∃ χ : ClassFunction G, IsIrreducibleCharacter χ ∧ χ 1 = 12 ∧
      ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ))
    (hformula : ∀ z ∈ centerImage S, z ≠ 1 →
      Nat.card G * Nat.card (centralizer (centerImage S : Set G)) ^ 2 =
        195 * Nat.card (centralizer ({z} : Set G)) ^ 3) :
    (∀ z ∈ centerImage S, z ≠ 1 →
      centralizer ({z} : Set G) = centralizer (centerImage S : Set G)) ∧
    IsStronglyEmbedded (normalizer (centerImage S : Set G)) := by
  have d := localCentralizerData_of_isNTwoGroup hN S h
  exact centralizer_eq_and_stronglyEmbedded_of_character_and_index S h hchar hformula
    (fun _ hz hz1 hne =>
      exists_prime_fourth_pow_dvd_centralizer_relIndex_of_local_data S h d hz hz1 hne)

/-- The N2 character calculation also yields the odd-core vanishing required
by the rank-two recognition consumer, for every ambient involution. -/
public theorem involutionCentralizer_oddCore_eq_bot_of_isNTwoGroup_and_character
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (h : SylowStructure S)
    (hchar : ∃ χ : ClassFunction G, IsIrreducibleCharacter χ ∧ χ 1 = 12 ∧
      ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ))
    (hformula : ∀ z ∈ centerImage S, z ≠ 1 →
      Nat.card G * Nat.card (centralizer (centerImage S : Set G)) ^ 2 =
        195 * Nat.card (centralizer ({z} : Set G)) ^ 3)
    {x : G} (hx : orderOf x = 2) :
    pPrimeCore 2 (centralizer ({x} : Set G)) = ⊥ := by
  exact involutionCentralizer_oddCore_eq_bot_of_centralizer_eq S h
    (centralizer_eq_and_stronglyEmbedded_of_isNTwoGroup_and_character
      hN S h hchar hformula).1 hx

end Stellmacher.Recognition.LyonsU3Four
