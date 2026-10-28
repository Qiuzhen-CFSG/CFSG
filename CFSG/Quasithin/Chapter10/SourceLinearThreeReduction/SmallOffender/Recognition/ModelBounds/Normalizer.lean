module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.Kernel
public import CFSG.Quasithin.ChapterE.Section03.Parameters.SectionNormalizer
public import CFSG.Quasithin.ChapterE.Section04.AlternatingFive

/-!
# Bounds from the full normalizer of a marked moved section

The kernel on the central quotient equals the kernel on the whole moved
module because the component generates that module by commutators. Crossed
centralization then puts the full local automizer in the marked linear
normalizer. Its two-rank bounds both the rank and the offender parameter in
`LargeModuleBounds`, while the actual section coordinates supply the index.

Source: Aschbacher--Smith 10.1.2 and 10.2.12, printed pp.742,754--755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem moved_normalizer_kernel
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    commutatorPreimage
      (normalizer (L : Set G) ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
      ⁅D.fullModule,L⁆ (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) =
    (normalizer (L : Set G) ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) ⊓
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let Z := W ⊓ centralizer (L : Set G)
  let N := normalizer (L : Set G) ⊓ normalizer (W : Set G)
  have hker : commutatorPreimage L W Z ≤ centralizer (W : Set G) := by
    rw [FixedSpaces.moved_quotient_kernel D hn]
    exact (source_component_core_centralizes_fullModule D).trans (centralizer_le
      (le_normalizer_iff_commutator_le_left.mp
        (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
          D.maximalLocal_normalizes_fullModule)))
  apply le_antisymm
  · exact le_inf (commutatorPreimage_le _ _ _)
      (commutatorPreimage_le_centralizer_of_fully_moved N L W Z
        (le_inf L.le_normalizer (normalizer_commutator_ge_right _ _))
        inf_le_left inf_le_right (source_original_moved_fixed_normalizer D)
        inf_le_right (source_full_moved_eq_commutator D) hker)
  · apply le_commutatorPreimage inf_le_left
    exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le

theorem local_rank_le_marked_normalizer
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {J V : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (σ : Representation (ZMod 2) J V)
    (e : (L ⧸ pCore 2 L) ≃* J)
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    primeRank 2 (inducedAutomizer ⁅D.fullModule,L⁆ D.maximalLocal) ≤
      primeRank 2 (linearNormalizer σ) := by
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
    rw [moved_normalizer_kernel D (fun hn => htn (hn ht))] at hh
    exact hh.trans inf_le_right
  obtain ⟨_,f,hf,_,_⟩ := exists_local_section_normalizer L W Z D.maximalLocal σ
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) c
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) hHL hHZ hk
  let : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective (fun x : Module.End (ZMod 2) V => (x : V → V)) DFunLike.coe_injective
  exact Theory.GroupTheory.primeRank_le_of_injective 2 f hf

theorem large_bounds_of_marked_normalizer
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {J V : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (σ : Representation (ZMod 2) J V)
    (e : (L ⧸ pCore 2 L) ≃* J)
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcross : ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {m r : ℕ} (hm : 3 < m) (hcard : Nat.card V = 2 ^ m)
    (hr : primeRank 2 (linearNormalizer σ) ≤ r) (hrm : r < m - 2) :
    Nonempty (LargeModuleBounds D) := by
  let := source_full_moved_elementary D
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp hn
  have hlocal := (local_rank_le_marked_normalizer D σ e c ht htn (hcross t ht htn)).trans hr
  let W := ⁅D.fullModule,L⁆
  let Z := W ⊓ centralizer (L : Set G)
  let := c.kernel_normal
  have hc : (centralizer (L : Set G)).relIndex W = 2 ^ m := by
    have he : Z.relIndex W = Nat.card V := Nat.card_congr c.quotientEquiv.toEquiv
    rw [show Z = W ⊓ centralizer (L : Set G) from rfl,inf_relIndex_left,hcard] at he
    exact he
  refine ⟨⟨m,hm,hc.ge,r,hlocal,?_,?_,hcross⟩⟩
  · exact (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : r < m)).trans_le
      (hc ▸ Nat.le_of_dvd Nat.card_pos ((centralizer (L : Set G)).relIndex_dvd_card W))
  · have ha := moduleA_le_primeRank
      ((automizerRepresentation W).comp (inducedAutomizer W D.maximalLocal).subtype)
      ((automizerRepresentation_injective _).comp Subtype.val_injective)
    have hle : (primeRank 2 (inducedAutomizer W D.maximalLocal) : ℕ∞) ≤ (r : ℕ∞) := by
      exact_mod_cast hlocal
    exact (ha.trans hle).trans_lt (by exact_mod_cast hrm)

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
