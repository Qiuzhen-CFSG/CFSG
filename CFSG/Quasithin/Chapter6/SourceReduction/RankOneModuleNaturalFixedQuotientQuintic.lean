module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientDegreeFour
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldTorus
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeConstruction
public import Theory.GroupTheory.PResidual.PrimeToPerfect
import all CFSG.Quasithin.Chapter6.Section01.SourceHStarLeftCartanOvergroup

/-!
# The original quintic residual in the Hermitian degree-four case

The literal subgroup X=O^{5′}(N_L(T∩L)) is two-perfect and normalized
by the original Sylow subgroup. Its image lies in the preimage of the
order-five torus. The norm-one action of this torus fixes the actual
omega-center, giving XT≤C_G(Ω₁Z(T)). No replacement actor is chosen.

The outside-component classification and fusion contradiction remain
separate source obligations.
Source: Aschbacher--Smith 6.1.4, printed pp.665--666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- The actual quintic residual used in the final Hermitian source branch. -/
abbrev quinticResidual (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  (primeToResidual 5 (localBorel T L)).map (localBorel T L).subtype

/-- Prime-to-five residuals are two-perfect, through the original inclusion. -/
theorem quinticResidual_twoPerfect (T : Sylow 2 G) (L : Subgroup G) :
    IsPPerfect 2 (quinticResidual T L) := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact (isPPerfect_primeToResidual (G := localBorel T L) 5 2 (by decide)).of_surjective
    ((primeToResidual 5 (localBorel T L)).equivMapOfInjective
      (localBorel T L).subtype (localBorel T L).subtype_injective).toMonoidHom
    ((primeToResidual 5 (localBorel T L)).equivMapOfInjective
      (localBorel T L).subtype (localBorel T L).subtype_injective).surjective

omit [Finite G] in
/-- The full original Borel normalizer preserves the quintic residual. -/
theorem quinticResidual_normalized (T : Sylow 2 G) (L : Subgroup G) :
    normalizer (localBorel T L : Set G) ≤ normalizer (quinticResidual T L : Set G) :=
  normalizer_le_normalizer_characteristic_image (localBorel T L)
    (primeToResidual 5 (localBorel T L))

omit [Finite G] in
/-- The original Sylow normalizes X, using only normalization of L. -/
theorem sylow_normalizes_quinticResidual
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (T : Subgroup G) ≤ normalizer (quinticResidual T L : Set G) :=
  (RankOneGeneric.sylow_normalizes_left_borel hTL).trans (quinticResidual_normalized T L)

/-- The actual order-five torus is contained in X, and XT is its product
with the original T. This product centralizes the actual omega-center. -/
theorem original_hermitian_quintic_torus
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2)) :
    ∃ D : Subgroup G, Nat.card D = 5 ∧ D ≤ localBorel T L ∧
      D ≤ quinticResidual T L ∧
      quinticResidual T L ≤ ((T : Subgroup G) ⊓ L) ⊔ D ∧
      quinticResidual T L ⊔ (T : Subgroup G) = D ⊔ (T : Subgroup G) ∧
      quinticResidual T L ⊔ (T : Subgroup G) ≤ omegaCentralizer T := by
  let hi := h.reduced_enlargement.rankOneInput hout
  obtain ⟨A,B,c⟩ := RankOneGeneric.exists_left_cartan_pair hi
  obtain ⟨he,D,E,hDE,hD,hE,hDC⟩ :=
    c.hermitian_torus_factors hi 2 hm h.omega_le_reduced_enlargement
  have hn : n = 4 := by omega
  have hD5 : Nat.card D = 5 := by norm_num at hD ⊢; exact hD
  have hDA : D ≤ A := hDE ▸ le_sup_left
  have hDB : D ≤ localBorel T L := hDA.trans c.left_le
  let U := (T : Subgroup G) ⊓ L
  let C := localBorel T L
  let K := U ⊔ D
  have hUC : U ≤ C := le_inf inf_le_right U.le_normalizer
  have hKC : K ≤ C := sup_le hUC hDB
  have hKN : C ≤ normalizer (K : Set G) := C.le_normalizer.trans
    (Prime.cartan_subgroup_preimage_normalized c hi.sylow_normalizes hi.linear hDA)
  let : (K.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer hKN
  have hdis (Y : Subgroup G) (hc : Odd (Nat.card Y)) : Disjoint U Y := by
    obtain ⟨k,hk⟩ := (T.isPGroup'.to_le (show U ≤ (T : Subgroup G) from inf_le_left)).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hk]; exact (Nat.coprime_two_left.mpr hc).pow_left k)
  have hAc : Nat.card A = 15 := by simpa [hn] using c.left_card hi.linear hi.sylow_normalizes
  have hCc : Nat.card C = Nat.card U * 15 := by
    change Nat.card (localBorel T L) = _
    rw [←c.left_sup_intersection hi.sylow_normalizes]
    rw [card_sup_eq_mul_of_normalizes_of_disjoint U A
      (c.left_le.trans inf_le_right) (hdis A (by rw [hAc]; decide)),hAc]
  have hKc : Nat.card K = Nat.card U * 5 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint U D
      (hDB.trans inf_le_right) (hdis D (by rw [hD5]; decide)),hD5]
  have hindex : (K.subgroupOf C).index = 3 := by
    have hc := (K.subgroupOf C).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hKC).toEquiv,hKc,hCc] at hc
    have hh := Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := U))
      (by simpa only [mul_assoc] using hc)
    omega
  have hXK : quinticResidual T L ≤ K := by
    have hr := map_mono (f := C.subtype)
      (primeToResidual_le (p := 5) (K.subgroupOf C) (by rw [hindex]; decide))
    rwa [map_subgroupOf_eq_of_le hKC] at hr
  have hDX : D ≤ quinticResidual T L := by
    intro d hd
    let dC : C := ⟨d,hDB hd⟩
    have hp : dC^(5^1) = 1 := by
      apply Subtype.ext
      simpa only [pow_one,hD5,Subgroup.coe_pow,Subgroup.coe_one] using
        congrArg Subtype.val (pow_card_eq_one' (x := (⟨d,hd⟩ : D)))
    exact mem_map_of_mem C.subtype (mem_primeToResidual_of_pow hp)
  have hjoin : quinticResidual T L ⊔ (T : Subgroup G) = D ⊔ (T : Subgroup G) := by
    apply le_antisymm (sup_le (hXK.trans (sup_le (inf_le_left.trans le_sup_right) le_sup_left)) le_sup_right)
    exact sup_le (hDX.trans le_sup_left) le_sup_right
  refine ⟨D,hD5,hDB,hDX,hXK,hjoin,?_⟩
  rw [hjoin]
  exact sup_le hDC sylow_le_omegaCentralizer

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
