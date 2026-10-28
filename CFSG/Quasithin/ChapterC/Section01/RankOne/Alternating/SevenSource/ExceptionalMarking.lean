module
public import CFSG.Quasithin.ChapterB.Section02.UniqueOffender
public import Theory.Representation.BinaryAlternatingSevenControl.Offenders
public import CFSG.Quasithin.ChapterB.Section02.BaumannNormalizerImage

/-!
# The original exceptional A₇ Thompson and Baumann images

The unique best offender in a Sylow subgroup fixes a plane. The full Sylow
fixes only a line, so its pointwise stabilizer of that plane is exactly the
four-group offender. B.2.20 therefore identifies the images of J(T) and
Baum(T) in the original action quotient, before any block assumption.

Source: Aschbacher–Smith C.1.24, printed p.131, exceptional A₇ case.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
open Representation.BinaryAlternatingSevenControl
local notation "A7" => alternatingGroup (Fin 7)

private theorem sylow_card (P : Sylow 2 A7) : Nat.card P = 8 := by
  rw [P.card_eq_multiplicity,nat_card_alternatingGroup,Nat.card_eq_fintype_card]
  norm_num [Nat.factorial]
  rw [show (2520 : ℕ).factorization 2 = 3 by
    rw [show 2520 = 2^3*315 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow]
    simp [Nat.prime_two.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]]
  norm_num

/-- The plane fixer inside the original Sylow is the unique best offender. -/
theorem exceptional_sylow_plane_kernel
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) A7 W) (hρ : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) W = 4)
    (P : Sylow 2 A7) (A : Subgroup A7) (hAP : A ≤ P) (hA : IsBestOffender ρ A) :
    (P : Subgroup A7) ⊓ subspaceKernel ρ (fixedSpace ρ A) ⊤ = A := by
  let B := (P : Subgroup A7) ⊓ subspaceKernel ρ (fixedSpace ρ A) ⊤
  have hAB : A ≤ B := fun a ha => ⟨hAP ha,mem_top _,fun v hv => hv ⟨a,ha⟩⟩
  have hBP : B ≤ P := inf_le_left
  obtain ⟨_,hAc,hAd⟩ := best_dimensions ρ hρ hd hA
  have hproper : B ≠ (P : Subgroup A7) := by
    intro he
    have hfix : fixedSpace ρ A ≤ fixedSpace ρ P := by
      intro v hv p
      have hp : (p : A7) ∈ B := he.symm ▸ p.property
      exact hp.2.2 v hv
    have hh := Submodule.finrank_mono hfix
    rw [hAd,sylow_fixed_finrank ρ hρ hd P] at hh
    omega
  have hBc : Nat.card B ≤ 4 := by
    have hdiv : Nat.card B ∣ 8 := sylow_card P ▸ card_dvd_of_le hBP
    have hle : Nat.card B ≤ 8 := sylow_card P ▸ card_le_of_le hBP
    have hne : Nat.card B ≠ 8 := fun he => hproper
      (eq_of_le_of_card_ge hBP (by rw [sylow_card P,he]))
    exact (by decide : ∀ n ∈ Finset.range 9, n ∣ 8 → n ≠ 8 → n ≤ 4)
      _ (Finset.mem_range.mpr (by omega)) hdiv hne
  exact (eq_of_le_of_card_ge hAB (by rw [hAc]; exact hBc)).symm

variable {G : Type*} [Group G] [Finite G]

/-- No block hypothesis occurs: the actual four-dimensional action and
Thompson movement identify both original images. -/
theorem exceptional_thompson_baumann_images
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* A7) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (hd : Module.finrank (ZMod 2) (Additive U) = 4)
    (T : Sylow 2 G) (hUT : U ≤ T)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ q.ker) :
    ∃ A : Subgroup A7,
      A ≤ (T : Subgroup G).map q ∧
      IsBestOffender (NormalElementaryQuotient.representation U q hq hk) A ∧
      (elementaryAbelianMaxJ (T : Subgroup G)).map q = A ∧
      (ChapterB.baumann (T : Subgroup G)).map q = A := by
  let ρ := NormalElementaryQuotient.representation U q hq hk
  have hρ := NormalElementaryQuotient.representation_injective U q hq hk
  let P := T.mapSurjective (f := q) hq
  obtain ⟨A,hAP,hA,hunique,_⟩ := exists_unique_best_and_generation ρ hρ hd P
  have hfix : ((T : Subgroup G) ⊓ centralizer
      (U ⊓ centralizer (A.comap q : Set G) : Set G)).map q ≤ A := by
    apply le_trans ?_ (exceptional_sylow_plane_kernel ρ hρ hd P A hAP hA).le
    rintro a ⟨g, hg, rfl⟩
    refine ⟨mem_map_of_mem q hg.1,mem_top _,?_⟩
    intro v hv
    have hvm : v ∈ fixedSpace ρ ((A.comap q).map q) := by
      rw [map_comap_eq_self_of_surjective hq]
      exact hv
    have hvC := (NormalElementaryQuotient.mem_fixedSpace_image U q hq hk (A.comap q) v).mp hvm
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply]
    rw [←hg.2 v.toMul ⟨v.toMul.property,hvC⟩,mul_inv_cancel_right]
  have huniq : ∀ B ∈ elementaryAbelianMaxSubgroups (T : Subgroup G),
      B.map q ≠ ⊥ → B.map q = A := by
    intro B hB hne
    exact hunique (B.map q) (map_mono hB.1)
      (Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
        U q hq hk (T : Subgroup G) B hUT hB hne)
  obtain ⟨hJq,hBq⟩ := ChapterB.thompson_baumann_image_of_unique_maximum_image
    U (T : Subgroup G) q A hUT hJ huniq hfix
  exact ⟨A,hAP,hA,hJq,hBq⟩

end CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
