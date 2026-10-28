module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.ActionKernel
public import CFSG.Quasithin.ChapterE.Section03.Parameters.SectionNormalizer
public import CFSG.Quasithin.ChapterE.Section04.AlternatingFive
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# The full local action on a natural linear-three central section

The kernel on the natural head equals the kernel on the whole moved factor.
Consequently the full local automizer embeds in GL₃(2), including every
normalizing actor and the possible central fixed part. The actual equality
GL₃(2)=SL₃(2) gives two-rank at most two and the same bound on moduleA.

Source: Aschbacher--Smith 10.2.12, printed pp.754--755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- Every original local actor has faithful action on the natural head. -/
theorem local_section_kernel (m : SourceLinearThreeGeometry T D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    commutatorPreimage
      (D.maximalLocal ⊓ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
      ⁅D.fullModule,L⁆ (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) =
    (D.maximalLocal ⊓ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) ⊓
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let Z := W ⊓ centralizer (L : Set G)
  let H := D.maximalLocal ⊓ normalizer (W : Set G)
  let N := normalizer (L : Set G) ⊓ normalizer (W : Set G)
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp hn
  have hHN : H ≤ N := le_inf
    (source_original_moved_stabilizer_le_component_normalizer D ht htn
      (m.crossed t ht htn)) inf_le_right
  have hHZ : H ≤ normalizer (Z : Set G) :=
    hHN.trans (source_original_moved_fixed_normalizer D)
  have hk : commutatorPreimage H W Z ≤ commutatorPreimage N W Z :=
    le_commutatorPreimage ((commutatorPreimage_le _ _ _).trans hHN)
      (commutator_commutatorPreimage_le _ _ _ hHZ)
  rw [moved_normalizer_quotient_kernel m] at hk
  apply le_antisymm
  · exact le_inf (commutatorPreimage_le _ _ _) (hk.trans inf_le_right)
  · apply le_commutatorPreimage inf_le_left
    exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le

/-- The full induced local action, rather than only the component action,
has two-rank at most two. -/
theorem local_primeRank_le_two (m : SourceLinearThreeGeometry T D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    primeRank 2 (inducedAutomizer ⁅D.fullModule,L⁆ D.maximalLocal) ≤ 2 := by
  let W := ⁅D.fullModule,L⁆
  let Z := W ⊓ centralizer (L : Set G)
  let := source_full_moved_elementary D
  let : Finite (Module.End (ZMod 2) (Fin 3 → ZMod 2)) := Finite.of_injective
    (fun f : Module.End (ZMod 2) (Fin 3 → ZMod 2) => (f : _ → _)) DFunLike.coe_injective
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp hn
  have hNL := source_original_moved_stabilizer_le_component_normalizer D ht htn
    (m.crossed t ht htn)
  have hNZ := (le_inf hNL (show D.maximalLocal ⊓ normalizer (W : Set G) ≤
    normalizer (W : Set G) from inf_le_right)).trans (source_original_moved_fixed_normalizer D)
  have hk : commutatorPreimage (D.maximalLocal ⊓ normalizer (W : Set G)) W Z ≤
      centralizer (W : Set G) := by
    rw [local_section_kernel m hn]
    exact inf_le_right
  obtain ⟨_,f,hf,_,_⟩ := exists_local_section_normalizer L W Z D.maximalLocal
    (Representation.specialLinearNatural 3)
    (m.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
    (m.quotient.surjective.comp (QuotientGroup.mk'_surjective _)) m.natural
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) hNL hNZ hk
  let e := (Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := ZMod 2)).symm.trans
    (Matrix.PSL3Two.equivGL.symm.trans Matrix.PSL3Two.equiv)
  have hr : primeRank 2 (LinearMap.GeneralLinearGroup (ZMod 2) (Fin 3 → ZMod 2)) ≤ 2 := by
    rw [primeRank_equiv 2 e]
    exact (Matrix.PSL3Even.two_rank (ZMod 2) (n := 1) (by decide) (by simp)).le
  exact ((Theory.GroupTheory.primeRank_le_of_injective 2 f hf).trans
    (Theory.GroupTheory.primeRank_le_of_injective 2
      (Representation.BinaryOffender.linearNormalizer (Representation.specialLinearNatural (k := ZMod 2) 3)).subtype Subtype.val_injective)).trans hr

/-- The literal whole moved-module parameter is at most two, including a
nonzero central fixed subgroup. -/
theorem local_moduleA_le_two (m : SourceLinearThreeGeometry T D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    let _ := source_full_moved_elementary D
    moduleA ((automizerRepresentation ⁅D.fullModule,L⁆).comp
      (inducedAutomizer ⁅D.fullModule,L⁆ D.maximalLocal).subtype) ≤ 2 := by
  let := source_full_moved_elementary D
  exact (moduleA_le_primeRank _
    ((automizerRepresentation_injective _).comp Subtype.val_injective)).trans
      (by exact_mod_cast local_primeRank_le_two m hn)

end CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
