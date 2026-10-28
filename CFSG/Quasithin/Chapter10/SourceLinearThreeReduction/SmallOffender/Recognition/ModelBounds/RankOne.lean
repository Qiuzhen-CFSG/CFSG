module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.RankOne.Kernel
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Contracts
public import CFSG.Quasithin.ChapterE.Section03.Parameters.SectionNormalizer
public import CFSG.Quasithin.ChapterE.Section04.AlternatingFive
public import Theory.Representation.SL2NaturalOffenders.NormalizerRank

/-!
# Full local bounds for the original natural rank-one section

The actual stabilizer of the moved factor normalizes L. Its kernel on the
central quotient is the centralizer of the whole moved factor, so its full
induced automizer embeds in the natural linear normalizer. This gives
rank at most n, while the literal fixed quotient has order 2^(2n).
For n>2 these inequalities supply every field of LargeModuleBounds.

No fixed-kernel vanishing or replacement of the local automizer by L is
assumed. Source: Aschbacher--Smith 10.1.1(1) and10.2.12, pp.741,754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 ChapterE PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Full local rank bound on the original central extension of a natural rank-one module. -/
theorem rank_one_local_rank
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (c : letI : Algebra (ZMod 2) F := ZMod.algebra _ 2
      BinaryConjugationSection L ⁅D.fullModule,L⁆ (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
        (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = 2^n) :
    primeRank 2 (inducedAutomizer ⁅D.fullModule,L⁆ D.maximalLocal) ≤ n := by
  let : Algebra (ZMod 2) F := ZMod.algebra _ 2
  let W := ⁅D.fullModule,L⁆
  let Z := W ⊓ centralizer (L : Set G)
  let H := D.maximalLocal ⊓ normalizer (W : Set G)
  let N := normalizer (L : Set G) ⊓ normalizer (W : Set G)
  let := source_full_moved_elementary D
  have hHL : H ≤ normalizer (L : Set G) :=
    source_original_moved_stabilizer_le_component_normalizer D ht htn hcross
  have hHZ : H ≤ normalizer (Z : Set G) :=
    (le_inf hHL inf_le_right).trans (source_original_moved_fixed_normalizer D)
  have hk : commutatorPreimage H W Z ≤ centralizer (W : Set G) := by
    have hh : commutatorPreimage H W Z ≤ commutatorPreimage N W Z :=
      le_commutatorPreimage ((commutatorPreimage_le _ _ _).trans (le_inf hHL inf_le_right))
        (commutator_commutatorPreimage_le _ _ _ hHZ)
    change commutatorPreimage H W Z ≤ commutatorPreimage
      (normalizer (L : Set G) ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
      ⁅D.fullModule,L⁆ (sourceMovedFixed D) at hh
    rw [RankOne.moved_normalizer_quotient_kernel D e c] at hh
    exact hh.trans inf_le_right
  obtain ⟨_,f,hf,_,_⟩ := exists_local_section_normalizer L W Z D.maximalLocal
    SL2.BinarySmall.natural (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) c
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) hHL hHZ hk
  let : Finite (Module.End (ZMod 2) (Fin 2 → F)) :=
    Finite.of_injective (fun x : Module.End (ZMod 2) (Fin 2 → F) =>
      (x : (Fin 2 → F) → (Fin 2 → F))) DFunLike.coe_injective
  exact (Theory.GroupTheory.primeRank_le_of_injective 2 f hf).trans (SL2NaturalOffenders.natural_normalizer_rank hn hcard)

/-- The quotient order is the actual two-dimensional field space. -/
theorem rank_one_fixed_quotient_card
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (c : letI : Algebra (ZMod 2) F := ZMod.algebra _ 2
      BinaryConjugationSection L ⁅D.fullModule,L⁆ (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
        (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    {n : ℕ} (hcard : Nat.card F = 2^n) :
    (centralizer (L : Set G)).relIndex ⁅D.fullModule,L⁆ = 2^(2*n) := by
  let : Algebra (ZMod 2) F := ZMod.algebra _ 2
  let W := ⁅D.fullModule,L⁆
  let Z := W ⊓ centralizer (L : Set G)
  let := c.kernel_normal
  have he : Z.relIndex W = Nat.card (Fin 2 → F) := Nat.card_congr c.quotientEquiv.toEquiv
  rw [show Z = W ⊓ centralizer (L : Set G) from rfl, inf_relIndex_left] at he
  rw [he,Nat.card_fun,Nat.card_fin,hcard,←pow_mul,Nat.mul_comm n 2]

/-- Every larger rank-one natural row supplies all literal local bounds. -/
theorem rank_one_large_bounds
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (c : letI : Algebra (ZMod 2) F := ZMod.algebra _ 2
      BinaryConjugationSection L ⁅D.fullModule,L⁆ (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
        (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcross : ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {n : ℕ} (hn : 2 < n) (hcard : Nat.card F = 2^n) : Nonempty (LargeModuleBounds D) := by
  let : Algebra (ZMod 2) F := ZMod.algebra _ 2
  let := source_full_moved_elementary D
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp hnon
  have hr := rank_one_local_rank D e c ht htn (hcross t ht htn) (by omega : 2 ≤ n) hcard
  have hc := rank_one_fixed_quotient_card D e c hcard
  refine ⟨⟨2*n,by omega,hc.ge,n,hr,?_,?_,hcross⟩⟩
  · exact (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : n < 2*n)).trans_le
      (hc ▸ Nat.le_of_dvd Nat.card_pos
        ((centralizer (L : Set G)).relIndex_dvd_card ⁅D.fullModule,L⁆))
  · have hm := moduleA_le_primeRank
      ((automizerRepresentation ⁅D.fullModule,L⁆).comp
        (inducedAutomizer ⁅D.fullModule,L⁆ D.maximalLocal).subtype)
      ((automizerRepresentation_injective _).comp Subtype.val_injective)
    have hr' : (primeRank 2 (inducedAutomizer ⁅D.fullModule,L⁆ D.maximalLocal) : ℕ∞) ≤ (n : ℕ∞) :=
      by exact_mod_cast hr
    exact (hm.trans hr').trans_lt (by exact_mod_cast (show n < 2*n-2 by omega))

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
