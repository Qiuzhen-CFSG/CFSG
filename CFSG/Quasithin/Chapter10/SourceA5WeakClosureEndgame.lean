module
public import CFSG.Quasithin.Chapter10.SourceA5WeakClosureBounds
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.Completion

/-!
# The weak-closure endgame for the chosen A₅ module

Small-corank commutation forces w>1; the deleted module forces w>2.
The actual Hall-placement upper bound therefore excludes the deleted
alternative and gives w=n(H)=2 with the literal natural SL₂(4) marking.
The completed component-normalizer theorem discharges N_G(L)≤M internally.

Chosen quotient irreducibility, separate-factor centralization, point-centralizer
control and the original Hall placement are earlier source inputs. This is the
source implication in 10.2.12–13, not the final A₅ contradiction: the natural
case's stronger generation bound still has its own producer.
Source: Aschbacher--Smith, printed pp.754–755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
local instance (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- Commuting small-corank conjugates exclude every attained offender at that bound. -/
theorem source_globalW_gt_of_small_conjugates_commute
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (k : ℕ)
    (hc : ∀ g ∉ D.maximalLocal,
      subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
        (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ k →
      ⁅D.fullModule,D.fullModule.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    (k : ℕ∞) < globalW D.fullModule (T : Subgroup G) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  by_contra! hw
  obtain ⟨g,hg⟩ := exists_isWOffenderAt_of_globalW_ne_top
    (source_fullModule_weakClosure_hypotheses D) (ne_top_of_le_ne_top (by simp) hw)
  have he := hg.2
  unfold offenderNormalizer at he
  rw [source_fullModule_normalizer D] at he
  have hs : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ k := by
    exact_mod_cast (he ▸ hw)
  have hgm : g ∉ D.maximalLocal := by
    intro hm
    apply hg.1
    have hmap : D.fullModule.map (MulAut.conj g).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hm)
    rw [hmap]
    exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer _)
  exact hg.1 (hc g hgm hs)

/-- The chosen original A₅ module has weak-closure parameter greater than one. -/
theorem source_a5_globalW_gt_one
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal) :
    1 < globalW D.fullModule (T : Subgroup G) :=
  source_globalW_gt_of_small_conjugates_commute D 1
    (fun _ _ hs => source_a5_corank_one_conjugates_commute D e hi hn ht htn hcross hcent (source_a5_component_normalizer_le D e hn) hs)

/-- The deleted alternative has weak-closure parameter greater than two. -/
theorem source_a5_deleted_globalW_gt_two
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (f : alternatingGroup (Fin 5) ≃* alternatingGroup (Fin 5))
    (c : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (Representation.OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal) :
    2 < globalW D.fullModule (T : Subgroup G) :=
  source_globalW_gt_of_small_conjugates_commute D 2
    (fun _ _ hs => source_a5_deleted_corank_two_conjugates_commute D e hi f c hn ht htn
      hcross hcent (source_a5_component_normalizer_le D e hn) hs)

/-- Actual Hall placement contradicts the deleted alternative. -/
theorem source_a5_deleted_hall_placement_contradiction
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (f : alternatingGroup (Fin 5) ≃* alternatingGroup (Fin 5))
    (c : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (Representation.OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hBJ : B.map H.subtype ≤ localJoin T L) : False :=
  (not_lt_of_ge (source_a5_globalW_le_two_of_hall_placement D e hn hcent hH B hBM hHall hBJ))
    (source_a5_deleted_globalW_gt_two D e hi f c hn ht htn hcross hcent)

local instance originalWeakClosureFieldFourAlgebra :
    Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

/-- The original Hall-placement upper bound removes the deleted alternative
and leaves the literal natural marking and the attained value w=2. -/
theorem source_a5_natural_and_parameters_eq_two_of_hall_placement
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hBJ : B.map H.subtype ≤ localJoin T L) :
    globalW D.fullModule (T : Subgroup G) = 2 ∧ generationParameter H = 2 ∧
      ∃ f : alternatingGroup (Fin 5) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1),
      Nonempty (Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
        (sourceMovedFixed D)
        (Representation.SL2.BinarySmall.natural.comp
          (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) := by
  have hlo := source_a5_globalW_gt_one D e hi hn ht htn hcross hcent
  have hw : globalW D.fullModule (T : Subgroup G) = 2 := by
    obtain ⟨g,hcomm,he,hsmall⟩ := source_a5_small_offender_of_hall_placement D e hn hcent hH B hBM hHall hBJ
    rw [he] at hlo ⊢
    have hn : 1 < subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) := by exact_mod_cast hlo
    have heq : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) = 2 := by omega
    rw [heq]
    rfl
  have hb := source_a5_hstar_generation_bound_of_hall_placement D e hn hH B hBM hHall hBJ
  have hg := source_a5_hstar_globalW_le_generation D e hcent hH hb
  rw [hw] at hg
  have hge : 2 ≤ generationParameter H := by exact_mod_cast hg
  refine ⟨hw,le_antisymm hb hge,?_⟩
  rcases source_a5_original_module_alternatives_of_irreducible D e hi with hnat | ⟨_,f,⟨c⟩⟩
  · exact hnat
  · exact (source_a5_deleted_hall_placement_contradiction D e hi f c hn ht htn hcross hcent
      hH B hBM hHall hBJ).elim

end CFSG.Quasithin.Chapter10
