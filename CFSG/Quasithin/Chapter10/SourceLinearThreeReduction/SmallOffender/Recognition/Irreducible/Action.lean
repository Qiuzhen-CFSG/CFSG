module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.Kernel
public import Theory.Representation.BinaryConjugationSection.Descent
public import Theory.Representation.PSL3Two.SmallModules

/-!
# The unclassified original moved quotient

Descend conjugation through the intrinsic two-core and retain the literal
map W → W/C_W(L), where W = [V,L]. The previously proved component-kernel
identity makes this action faithful. In particular the binary SL₃ action
is available before any natural-module recognition or irreducibility claim.

Source: Aschbacher–Smith 10.1.1 and 10.2.12, printed pp.741,754–755.
-/

@[expose] public noncomputable section
open scoped IsMulCommutative

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The literal moved central quotient admits the faithful action of any actual component marking.
Its coordinates are the original quotient map. -/
theorem exists_moved_quotient_action
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {J : Type*} [Group J] (e : (L ⧸ pCore 2 L) ≃* J) :
    let W := ⁅D.fullModule,L⁆
    let Z := W ⊓ centralizer (L : Set G)
    letI := source_full_moved_elementary D
    ∃ (ρ : Representation (ZMod 2) J (Additive (W ⧸ Z.subgroupOf W)))
      (s : BinaryConjugationSection L W Z
        (ρ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))),
      Function.Injective ρ ∧
      ∀ w : W, (s.coordinates w).toAdd =
        Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w) := by
  dsimp only
  let W := ⁅D.fullModule,L⁆
  let Z := W ⊓ centralizer (L : Set G)
  let := source_full_moved_elementary D
  have hLW : L ≤ normalizer (W : Set G) := normalizer_commutator_ge_right _ _
  have hLZ : L ≤ normalizer (Z : Set G) :=
    (le_inf L.le_normalizer hLW).trans (source_original_moved_fixed_normalizer D)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨ρ,s,hs⟩ := BinaryConjugationSection.exists_descended_actor
    L W Z (source_full_moved_le_component D) inf_le_left hLW hLZ q hq (by
      intro l hl w hw
      have hp : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp
        (e.injective (hl.trans e.map_one.symm))
      have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
        (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
          D.maximalLocal_normalizes_fullModule)
      have hh := source_component_core_centralizes_fullModule D
        (mem_map_of_mem L.subtype hp) w (hWV hw)
      have he : ⁅(l : G),w⁆ = 1 := (commutatorElement_eq_one_iff_mul_comm).mpr hh.symm
      rw [he]
      exact Z.one_mem)
  refine ⟨ρ,s,?_,hs⟩
  have hk := s.action_kernel_map hLZ
  rw [FixedSpaces.moved_quotient_kernel D hn] at hk
  have hker : (ρ.comp q).ker = pCore 2 L := map_injective L.subtype_injective hk
  apply (MonoidHom.ker_eq_bot_iff ρ).mp
  apply le_bot_iff.mp
  intro j hj
  obtain ⟨l,rfl⟩ := hq j
  have hl : l ∈ pCore 2 L := hker ▸ (show l ∈ (ρ.comp q).ker from hj)
  change e (QuotientGroup.mk' (pCore 2 L) l) = 1
  have hlq : (QuotientGroup.mk' (pCore 2 L)) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
  exact (congrArg e hlq).trans e.map_one

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)

local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_full_moved_elementary D

/-- The action on the original moved subgroup modulo its full component-fixed subgroup. -/
def binaryThreeMovedAction :
    Representation (ZMod 2) BinaryLinearThree.Group
      (Additive ((⁅D.fullModule,L⁆ : Subgroup G) ⧸
        (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)).subgroupOf ⁅D.fullModule,L⁆)) :=
  (exists_moved_quotient_action D hn e).choose

/-- The quotient marking retains the literal component map and denominator. -/
def binaryThreeMovedSection :
    BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      ((binaryThreeMovedAction D hn e).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) :=
  (exists_moved_quotient_action D hn e).choose_spec.choose

theorem binaryThreeMovedAction_faithful : Function.Injective (binaryThreeMovedAction D hn e) :=
  (exists_moved_quotient_action D hn e).choose_spec.choose_spec.1

theorem binaryThreeMovedSection_coordinates (w : (⁅D.fullModule,L⁆ : Subgroup G)) :
    ((binaryThreeMovedSection D hn e).coordinates w).toAdd =
      Additive.ofMul (QuotientGroup.mk'
        ((⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)).subgroupOf ⁅D.fullModule,L⁆) w) :=
  (exists_moved_quotient_action D hn e).choose_spec.choose_spec.2 w

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
