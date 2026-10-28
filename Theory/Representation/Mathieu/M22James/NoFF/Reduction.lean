module
public import Theory.Representation.Mathieu.M22James.NoFF.AmbientInvolutions
public import Theory.ElementaryAbelian.Injective
public import Theory.Representation.BinaryOffender.RestrictionComparison
/-!
# Reducing actual triple Mathieu offenders to a unitary fixed space

The ambient rank bound and outer involution displacement force every offender
into the genuine cover. Inside the cover, displacement four and two-rank four
force order sixteen and equality of the offender fixed space with an involution
fixed space. Native involution fusion conjugates that involution to the checked
generator B, retaining the literal six-dimensional field action.
Source: Aschbacher--Smith H.12.1(12), printed pp.394--395. The final matrix
obstruction is proved separately in `Fixer` and discharged in the no-FF assembly.
-/
public section
open Sporadic.Mathieu Theory.GroupTheory
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open Representation Representation.BinaryOffender
open Sporadic.Mathieu.M22TripleCover.Unitary
namespace Sporadic.Mathieu.M22TripleCover.NoFF
noncomputable section
private lemma elementary_rank_le {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} (hA : IsElementaryTwo A) {r : ℕ} (hr : primeRank 2 G ≤ r) :
    rank A ≤ r := by
  have hc := (primeRank_le_iff_elementary_card_le G).mp hr A hA.2
  have hh := Nat.log_mono_right (b := 2) hc
  simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh

private lemma fixedCodim_le_of_mem {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G) {t : G} (ht : t ∈ A) :
    fixedCodim ρ (Subgroup.zpowers t) ≤ fixedCodim ρ A := by
  have h := Submodule.finrank_mono (fixedSpace_antitone ρ (Subgroup.zpowers_le.mpr ht))
  have hA := fixedCodim_add_finrank ρ A
  have ht := fixedCodim_add_finrank ρ (Subgroup.zpowers t)
  omega

lemma inner_offender_fixed_representative {A : Subgroup M22TripleCover}
    (hA : IsOffender binaryRepresentation A) :
    ∃ B : Subgroup M22TripleCover, Nat.card B = 16 ∧
      (∀ a : B, a.val ^ 2 = 1) ∧
      ∀ a : B, ∀ v : Vector, fieldAction coreGeneratorB v = v → fieldAction a.val v = v := by
  let : IsElementaryAbelian 2 A := hA.1.2
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1.1
  have hto : orderOf t = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian t ht) ht1
  obtain ⟨c, hc⟩ := isConj_iff.mp (involutions_isConj t coreGeneratorB hto coreGeneratorB_order)
  let B := A.map (MulAut.conj c).toMonoidHom
  have hB : IsOffender binaryRepresentation B := by
    refine ⟨hA.1.map_conj c, ?_⟩
    change fixedCodim binaryRepresentation (A.map _) ≤ rank (A.map _)
    rw [fixedCodim_map_conj, rank_map_conj]
    exact hA.2
  let : IsElementaryAbelian 2 B := hB.1.2
  have hBt : coreGeneratorB ∈ B := ⟨t, ht, hc⟩
  have hdimB : fixedCodim binaryRepresentation B = 4 := by
    have hle := fixedCodim_le_of_mem binaryRepresentation B hBt
    rw [binaryCodim_involution coreGeneratorB coreGeneratorB_order] at hle
    have hr := elementary_rank_le hB.1 twoRank_le_four
    have hh := hB.2
    omega
  have hrank : rank B = 4 := by
    have hr := elementary_rank_le hB.1 twoRank_le_four
    have hh := hB.2
    rw [hdimB] at hh
    omega
  have hfix : fixedSpace binaryRepresentation B =
      fixedSpace binaryRepresentation (Subgroup.zpowers coreGeneratorB) := by
    apply Submodule.eq_of_le_of_finrank_eq
      (fixedSpace_antitone binaryRepresentation (Subgroup.zpowers_le.mpr hBt))
    have h₁ := fixedCodim_add_finrank binaryRepresentation B
    have h₂ := fixedCodim_add_finrank binaryRepresentation (Subgroup.zpowers coreGeneratorB)
    rw [hdimB] at h₁
    rw [binaryCodim_involution coreGeneratorB coreGeneratorB_order] at h₂
    omega
  refine ⟨B, ?_, ?_, ?_⟩
  · rw [hB.1.card_eq_two_pow_rank, hrank]
    norm_num
  · exact fun a => elemPow_eq_one_of_isElementaryAbelian a.val a.property
  · intro a v hv
    have hinter (g : M22TripleCover) (w : BinarySpace) :
        fieldAction g (binaryCoordinates w) = binaryCoordinates (binaryRepresentation g w) := by
      change binaryCoordinates (binaryRepresentation g
        (binaryCoordinates.symm (binaryCoordinates w))) = _
      rw [binaryCoordinates.symm_apply_apply]
    have hbv : binaryCoordinates.symm v ∈ fixedSpace binaryRepresentation B := by
      rw [hfix, mem_fixedSpace_zpowers_iff]
      apply binaryCoordinates.injective
      rw [← hinter, binaryCoordinates.apply_symm_apply]
      exact hv
    have hh : binaryCoordinates (binaryRepresentation a.val (binaryCoordinates.symm v)) =
        binaryCoordinates (binaryCoordinates.symm v) := congrArg binaryCoordinates (hbv a)
    rw [← hinter, binaryCoordinates.apply_symm_apply] at hh
    exact hh


lemma ambient_offender_le_cover {A : Subgroup actionGroup} (hA : IsOffender Ambient.binaryAction A) :
    A ≤ coverSubgroup := by
  let : IsElementaryAbelian 2 A := hA.1.2
  intro t ht
  by_contra ho
  have ht1 : t ≠ 1 := fun he => ho (he ▸ coverSubgroup.one_mem)
  have hto : orderOf t = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian t ht) ht1
  have hle := fixedCodim_le_of_mem Ambient.binaryAction A ht
  rw [outer_binaryCodim t hto ho] at hle
  have hr := elementary_rank_le hA.1 ambient_twoRank_le_five
  have hh := hA.2
  omega

lemma ambient_not_isFFModule_of_inner (hinner : ¬ IsFFModule binaryRepresentation) :
    ¬ IsFFModule Ambient.binaryAction := by
  rintro ⟨A, hA⟩
  have hcover := ambient_offender_le_cover hA
  have hi : Function.Injective coverInclusion := Subgroup.inclusion_injective _
  let B := A.comap coverInclusion
  have hm : B.map coverInclusion = A := by
    apply Subgroup.map_comap_eq_self
    simpa only [coverInclusion_range] using hcover
  let : IsElementaryAbelian 2 A := hA.1.2
  let f : B →* A := (coverInclusion.comp B.subtype).codRestrict A (fun b => b.property)
  have hfi : Function.Injective f := fun _ _ he => Subtype.ext (hi (congrArg Subtype.val he))
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective f hfi
  apply hinner
  refine ⟨B, ⟨?_, inferInstance⟩, ?_⟩
  · intro hb
    rw [hb, Subgroup.map_bot] at hm
    exact hA.1.1 hm.symm
  · have he := fixedCodim_map_equivariant binaryRepresentation Ambient.binaryAction coverInclusion
      (LinearEquiv.refl _ _) (fun _ _ => rfl) B
    rw [hm] at he
    rw [he, ← rank_map_injective coverInclusion hi B, hm]
    exact hA.2
end
end Sporadic.Mathieu.M22TripleCover.NoFF
