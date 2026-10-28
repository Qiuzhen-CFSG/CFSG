module
public import CFSG.Quasithin.Chapter10.SourceA5WeakClosureAssembly
public import Theory.SpecificGroups.Alternating.FiveFixedQuotientDegree
public import Theory.GroupTheory.PairNormalizerIndex

/-!
# Noncentral normalizing elements in the original small offender

For the original moved factor W=[V,L], the A₅ quotient forces
|W:C_W(L)|≥16. This remains true on every literal conjugate factor.
The original maximal local group permutes the two factors, so the
normalizer of W has index at most two in every subgroup of M.
Consequently an offender of corank at most two meets that normalizer
outside the fixed subgroup of its conjugated component.

These are the size and element-selection steps in 10.2.12. They require
no chosen A₅ module model and no Baumann-normalizer escape hypothesis.
The subsequent fixed-space identity and the model-dependent lower bound
remain separate source obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
10.2.12, printed p.754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE ChapterB
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

private theorem source_uniqueness :
    Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- Elementary structure on the literal moved factor, inherited from the original full module. -/
theorem source_full_moved_elementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) := by
  let := D.fullModule_elementary (source_uniqueness D)
  have hLV : L ≤ normalizer (D.fullModule : Set G) :=
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule
  exact offender_elementary_of_le (le_normalizer_iff_commutator_le_left.mp hLV)

/-- The original moved factor has binary fixed quotient of rank at least four. -/
theorem source_a5_full_moved_fixed_quotient_card
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    16 ≤ (centralizer (L : Set G)).relIndex ⁅D.fullModule,L⁆ := by
  let := D.fullModule_elementary (source_uniqueness D)
  have hLV : L ≤ normalizer (D.fullModule : Set G) :=
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule :=
    le_normalizer_iff_commutator_le_left.mp hLV
  let : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) := offender_elementary_of_le hWV
  let := Chapter1.mem_L_isPerfect D.maximal.1
  apply alternatingGroup.FiveChiefDegree.centralizer_relIndex_ge_sixteen
    L ⁅D.fullModule,L⁆ D.faithful.1.2.1 e
    ((IsElementaryAbelian.isPGroup 2 D.fullModule).to_le hWV)
    (normalizer_commutator_ge_right _ _)
  intro hz
  exact source_full_moved_ne_bot D
    (commutator_eq_bot_of_iterated_eq_bot D.fullModule L hz)

/-- Literal conjugation preserves the full fixed quotient, not only the factor order. -/
theorem source_a5_conjugate_full_moved_fixed_quotient_card
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (g : G) :
    16 ≤ (centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)).relIndex
      ((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom) := by
  rw [← Theory.Quasithin.map_centralizer (MulAut.conj g) L, relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  exact source_a5_full_moved_fixed_quotient_card D e

/-- Any subgroup of the original M has factor-normalizer index at most two. -/
theorem source_nonnormal_moved_normalizer_index_le_two
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {A : Subgroup G} (hAM : A ≤ D.maximalLocal) :
    (normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)).relIndex A ≤ 2 := by
  obtain ⟨t,_,_,_,_,hpair⟩ := source_nonnormal_fullModule_pair D hn
  by_cases hAN : A ≤ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)
  · rw [relIndex_eq_one.mpr hAN]
    decide
  · obtain ⟨a,ha,han⟩ := Set.not_subset.mp hAN
    exact (normalizer_relIndex_eq_two_of_pair A ⁅D.fullModule,L⁆
      ((⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
      (fun m hm => hpair m (hAM hm)) a ha
      (fun he => han (mem_normalizer_iff_map_conj_eq.mpr he))).le

/-- Each conjugate factor of a small offender contains a noncentral element
normalizing the original first factor, exactly as selected on p.754. -/
theorem source_a5_small_offender_exists_noncentral_normalizing_element
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {g : G} (hsmall : subgroupCorank
      (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 2) :
    ∃ b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom,
      b ∈ D.maximalLocal ∧ b ∈ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) ∧
      b ∉ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G) := by
  let V := D.fullModule.map (MulAut.conj g).toMonoidHom
  let W := (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom
  let A := W ⊓ D.maximalLocal
  let N := normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)
  let B := A ⊓ N
  let C := centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)
  let := D.fullModule_elementary (source_uniqueness D)
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  have hidx (P Q : Subgroup G) : P.relIndex Q ≠ 0 := by
    change Nat.card (Q ⧸ P.subgroupOf Q) ≠ 0
    exact Nat.card_ne_zero.mpr ⟨inferInstance,inferInstance⟩
  have hLV : L ≤ normalizer (D.fullModule : Set G) :=
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule
  have hWV : W ≤ V := map_mono (le_normalizer_iff_commutator_le_left.mp hLV)
  have hMV : D.maximalLocal.relIndex V ≤ 4 := by
    have he : D.maximalLocal.relIndex V = 2 ^ subgroupCorank V (V ⊓ D.maximalLocal) := by
      rw [subgroupCorank_eq_quotient_finrank, relIndex_eq_two_pow_quotient_finrank V D.maximalLocal]
      congr 1
      rw [inf_subgroupOf_left]
    rw [he]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hsmall)
  have hAW : A.relIndex W ≤ 4 := by
    rw [show A = W ⊓ D.maximalLocal from rfl, inf_relIndex_left]
    exact (relIndex_le_of_le_right hWV (hidx _ _)).trans hMV
  have hBA : B.relIndex A ≤ 2 := by
    rw [show B = A ⊓ N from rfl, inf_relIndex_left]
    exact source_nonnormal_moved_normalizer_index_le_two D hn (show A ≤ D.maximalLocal from inf_le_right)
  have hBW : B.relIndex W ≤ 8 := by
    rw [← relIndex_mul_relIndex B A W inf_le_left inf_le_left]
    exact Nat.mul_le_mul hBA hAW
  have hCW : 16 ≤ C.relIndex W := source_a5_conjugate_full_moved_fixed_quotient_card D e g
  have hnBC : ¬ B ≤ C := by
    intro hBC
    have hi := relIndex_le_of_le_left hBC (hidx B W)
    omega
  obtain ⟨b,hb,hbc⟩ := Set.not_subset.mp hnBC
  exact ⟨b,hb.1.1,hb.1.2,hb.2,hbc⟩

/-- The actual attained offender now carries the noncentral normalizing element
needed by the fixed-space argument, with all original source markings retained. -/
theorem source_a5_small_offender_configuration_with_normalizing_element
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcent : ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 →
      centralizer ({v} : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hBJ : B.map H.subtype ≤ localJoin T L) :
    ∃ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) ∧
      D.fullModule = ⁅D.fullModule,L⁆ ⊔
        (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ∧
      ∃ g ∉ D.maximalLocal,
        ⁅D.fullModule,D.fullModule.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
        subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
          (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 2 ∧
        ¬ localOrbit T L ≤ D.maximalLocal.map (MulAut.conj g).toMonoidHom ∧
        ∃ b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom,
          b ∈ D.maximalLocal ∧
          b ∈ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) ∧
          b ∉ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G) := by
  obtain ⟨t,ht,htn,hpair,g,hg,hcomm,hsmall,horbit⟩ :=
    source_a5_small_offender_configuration D e hn hcent hH B hBM hHall hBJ
  exact ⟨t,ht,htn,hpair,g,hg,hcomm,hsmall,horbit,
    source_a5_small_offender_exists_noncentral_normalizing_element D e hn hsmall⟩

end CFSG.Quasithin.Chapter10
