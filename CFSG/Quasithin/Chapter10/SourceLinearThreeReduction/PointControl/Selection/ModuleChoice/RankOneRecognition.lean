module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.NativeRankOne
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuotientCoordinates
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.NaturalLocal
public import Theory.Representation.BinaryConjugationSection.Relabel

/-!
# Literal rank-one recognition on the selected full module

When the original component is binary rank one and the local Thompson
subgroup moves the module, B.5.6 selects its natural row. The canonical
full-action quotient map then supplies coordinates on the original [V,L]
with kernel C_[V,L](L). Changing the finite binary field to its Galois-field
model preserves this actor map and kernel, giving `RankOneNatural D`.

The point-selection application is in ModuleChoice.Source. Component
recognition in the other rows, quiet support and even-degree fixed-kernel
stabilization remain separate obligations of the same source proof.
Source: Aschbacher--Smith B.5.6(3), 3.2.6 and 10.1.1(1),
printed pp.105,581,741.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private def section_relabel_action
    {H A B : Subgroup G} {Q R X Y : Type*} [Group Q] [Group R]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    {ρ : Representation (ZMod 2) Q X} {τ : Representation (ZMod 2) R Y}
    (a : ActionEquiv ρ τ) (q : H →* Q)
    (c : BinaryConjugationSection H A B (ρ.comp q)) :
    BinaryConjugationSection H A B (τ.comp (a.groupEquiv.toMonoidHom.comp q)) := by
  let E : ρ.Equiv (τ.comp a.groupEquiv.toMonoidHom) :=
    Representation.Equiv.mk a.linearEquiv (fun g => by
      ext v
      exact a.intertwines g v)
  exact c.relabel q E

private def binary_field_galois (E : BinaryField) :
    E.Carrier ≃+* GaloisField 2 E.degree :=
  (GaloisField.algEquivGaloisField 2 E.degree E.card_eq).toRingEquiv

private def natural_galois_equiv (E : BinaryField) :
    letI : Algebra (ZMod 2) (GaloisField 2 E.degree) := ZMod.algebra _ 2
    ActionEquiv (linearNatural E 2) (Representation.SL2.BinarySmall.natural
      (K := GaloisField 2 E.degree)) := by
  letI : Algebra (ZMod 2) (GaloisField 2 E.degree) := ZMod.algebra _ 2
  let a := binary_field_galois E
  let b : E.Carrier ≃ₗ[ZMod 2] GaloisField 2 E.degree :=
    { a.toAddEquiv with map_smul' := ZMod.map_smul a }
  refine ⟨Atlas.fieldEquivSL 2 a,
    LinearEquiv.piCongrRight (fun _ : Fin 2 => b),?_⟩
  intro g v
  funext i
  change a (∑ j, g.val i j * v j) = ∑ j, a (g.val i j) * a (v j)
  simp only [map_sum,map_mul]

/-- A genuine binary rank-one component and a moving local Thompson subgroup
give natural coordinates on the original moved subgroup, with its full kernel. -/
theorem rankOneNatural_of_binary_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) : RankOneNatural D := by
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  obtain ⟨r⟩ := full_rank_one_factor D hn hna hJ e
  obtain ⟨a,⟨c⟩⟩ := full_moved_quotient_section D hn hna hJ r.space r.space_eq
  let : NeZero r.field.degree := ⟨Nat.ne_of_gt r.field.degree_pos⟩
  let : Algebra (ZMod 2) (GaloisField 2 r.field.degree) := ZMod.algebra _ 2
  let b := natural_galois_equiv r.field
  let c₁ := section_relabel_action r.model
    (a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) c
  let c₂ := section_relabel_action b
    (r.model.groupEquiv.toMonoidHom.comp
      (a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) c₁
  exact ⟨r.field.degree,r.degree_gt_one,a.trans (r.model.groupEquiv.trans b.groupEquiv),⟨c₂⟩⟩

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
