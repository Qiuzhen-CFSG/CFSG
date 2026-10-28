module

public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.OmegaNormalizer.Models
public import BenderSuzuki.SE.Models
public import BenderSuzuki.External.Huppert.II.theorem_10_4
public import Theory.GroupTheory.SylowNormalizerOvergroup

/-!
# The marked omega subgroup of a recognized simple Bender group

The simple Bender alternatives retain their actual field and group maps.
For each alternative, the existing Sylow coordinates identify the first
omega with the embedded Sylow center and give its exact field order.
The unitary fixed-field convention is converted by the proved quadratic
Frobenius theorem, with the original Hermitian form retained.

Source: Aschbacher--Smith I.8.3, printed p.430, and the rank-one geometry
used in Proposition 2.2.2, printed pp.519--520.
-/

public section
open Subgroup Theory.GroupTheory
open BenderSuzuki BenderSuzuki.MatrixGroups
open BenderSuzuki.PFAppendixIII
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter2.BenderFusion.GoodCentralizers
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The existing simple Bender recognition gives the Chapter 2 model predicate
on the same carrier, retaining the actual unitary form and field exponent. -/
theorem classificationModel_of_simpleBender (h : IsSimpleBenderGroup G) :
    ClassificationModels.IsBenderModel G := by
  rcases h with ⟨⟨n, hn, e⟩⟩ | ⟨⟨m, hm, e⟩⟩ |
    ⟨⟨n, hn, E, hE, hfin, J, _, hc, hf, e⟩⟩
  · apply ClassificationModels.IsBenderModel.linear n hn
    exact ⟨BinaryGaloisField n, inferInstance, inferInstance,
      (by simpa [BinaryGaloisField] using GaloisField.card 2 n (by omega)), e⟩
  · exact .suzuki m hm e
  · let : Field E := hE
    let : Finite E := hfin
    exact .unitary n hn ⟨E, hE, hfin, J, hc,
      BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J (2 ^ n) hc hf, e⟩

/-- Recognition supplies one source exponent, together with the exact omega
and embedded center of the original Sylow subgroup. -/
theorem exponent_and_omega_of_simpleBender (h : IsSimpleBenderGroup G)
    (T : Sylow 2 G) :
    ∃ n : ℕ, 2 ≤ n ∧ IsSimpleBenderGroupAtExponent n G ∧
      omegaOneAmbient (T : Subgroup G) = (center T).map (T : Subgroup G).subtype ∧
      Nat.card (omegaOneAmbient (T : Subgroup G)) = 2 ^ n := by
  rcases h with ⟨⟨n, hn, ⟨e⟩⟩⟩ | ⟨⟨m, hm, ⟨e⟩⟩⟩ |
    ⟨⟨n, hn, E, hE, hfin, J, hJ, hc, hf, ⟨e⟩⟩⟩
  · let F := BinaryGaloisField n
    let R := T.mapSurjective (f := e.toMonoidHom) e.surjective
    let a : Multiplicative F ≃* T :=
      (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive R).trans
        (e.subgroupMap (T : Subgroup G)).symm
    have ht2 (x : T) : x ^ 2 = 1 := by
      apply a.symm.injective
      rw [map_pow, map_one]
      change 2 • (a.symm x).toAdd = 0
      exact (two_nsmul _).trans (CharTwo.add_self_eq_zero _)
    let : IsMulCommutative T := ⟨⟨fun x y => a.symm.injective (by
      rw [map_mul, map_mul, mul_comm])⟩⟩
    have hw : omegaOneAmbient (T : Subgroup G) = T := by
      apply le_antisymm (omegaOneAmbient_le _)
      intro x hx
      exact (omegaOneAmbient_le_iff _ _).mp le_rfl x hx
        (congrArg Subtype.val (ht2 ⟨x, hx⟩))
    refine ⟨n, hn, .isPSL2 ⟨e⟩, ?_, ?_⟩
    · rw [center_eq_top, ← MonoidHom.range_eq_map, (T : Subgroup G).range_subtype, hw]
    · rw [hw, ← Nat.card_congr a.toEquiv, Nat.card_congr Multiplicative.toAdd]
      simpa [F, BinaryGaloisField] using GaloisField.card 2 n (by omega)
  · exact ⟨2 * m + 1, by omega, .isSuzuki ⟨m, rfl, ⟨e⟩⟩,
      suzukiSylow_omega_eq_center (by omega) e T,
      suzukiSylow_omega_card (by omega) e T⟩
  · let : Field E := hE
    let : Finite E := hfin
    obtain ⟨hz, _, ho⟩ := HermitianForm.SylowOmega.omega_of_projective_equiv
      J hn hc hf hJ e T
    exact ⟨n, hn, .isPSU3 ⟨E, hE, hfin, J, hJ, hc, hf, ⟨e⟩⟩, hz, ho⟩

omit [Finite G] in
private theorem rankOne_of_bender (h : ClassificationModels.IsBenderModel G) :
    ChapterF.Source.IsRankOneModel G := by
  cases h with
  | linear n hn e => exact .linear n (by omega) e
  | unitary n hn e => exact .projective_unitary n (by omega) e
  | suzuki m hm e => exact .suzuki m e

/-- The full normalizer of the marked first omega is the original Sylow
normalizer. This uses the existing unique proper Sylow-overgroup geometry. -/
theorem normalizer_omega_eq (h : IsSimpleBenderGroup G) (T : Sylow 2 G)
    (hw : omegaOneAmbient (T : Subgroup G) = (center T).map (T : Subgroup G).subtype) :
    normalizer (omegaOneAmbient (T : Subgroup G) : Set G) = normalizer (T : Set G) := by
  let : IsSimpleGroup G := h.isSimple
  have hm := classificationModel_of_simpleBender h
  have hf := OmegaNormalizerModels.of_bender_model hm T
  have hne : omegaOneAmbient (T : Subgroup G) ≠ ⊥ := by
    intro he
    have hh := hf.size
    rw [he] at hh
    simp at hh
  have hN : normalizer (T : Set G) ≤
      normalizer (omegaOneAmbient (T : Subgroup G) : Set G) := by
    rw [hw]
    exact normalizer_le_normalizer_characteristic_image (T : Subgroup G) (center T)
  have hr := (rankOne_of_bender hm).rankOneSylowFacts T
  exact SylowCenterAction.normalizer_eq_of_unique_maximal T _ hne
    (omegaOneAmbient_le _) hN hr.proper hr.unique_maximal

end CFSG.Quasithin.Chapter2.BenderFusion.GoodCentralizers
