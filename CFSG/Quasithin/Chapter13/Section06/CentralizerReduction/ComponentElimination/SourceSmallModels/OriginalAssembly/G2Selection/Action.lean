module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.G2Selection.ActionRows
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.AlternatingModels.Source

/-!
# The full moved quotient for the original derived binary G₂ component

Restrict the faithful action to its offender-generated subgroup, apply B.5.1,
and use the component order to select its natural G₂(2)′ action. Extending
back to the original actor leaves the moved space and its central quotient
unchanged. Thus the actual W_K action supplies the natural model on
U_K/C_(U_K)(K), without a short-block or splitting assumption.

Source: Aschbacher–Smith B.5.1, pp.99–103, used in 13.6.22, printed p.932.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.G2Selection.Action
universe u v
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) (C : Subgroup D) [C.Normal]

/-- The actual moved space and its literal component-fixed quotient. -/
structure Data where
  sectionData : MovedSection ρ C
  faithful : Function.Injective sectionData.action
  irreducible : IsIrreducible (sectionData.action.comp C.subtype)
  natural : ActionEquiv (sectionData.action.comp C.subtype) (g2DerivedNatural (ZMod 2))

/-- The B.5.1 application uses the actual offender actor and does not assume
that the ambient actor is offender-generated. -/
theorem nonempty_data [IsQuasisimple C] [IsSimpleGroup C]
    (eC : C ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hC : centralizer (C : Set D) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple C)
    (hf : Function.Injective ρ) (hCJ : C ≤ offenderSubgroup ρ) :
    Nonempty (Data ρ C) := by
  obtain ⟨c⟩ := AlternatingModels.offender_source_conclusion ρ C hC hsq hf hCJ
  obtain ⟨_, hfaith, hi, ⟨e⟩⟩ := classification_natural _
    ((subgroupOfEquivOfLe hCJ).trans eC) c.sectionData c.clause_one
  obtain ⟨f⟩ := AlternatingModels.ambientSection_actionEquiv ρ C hCJ c.sectionData
    (g2DerivedNatural (ZMod 2)) e
  exact ⟨⟨AlternatingModels.ambientSection ρ C hCJ c.sectionData,
    AlternatingModels.ambientSection_faithful ρ C hCJ c.sectionData hC hfaith,
    AlternatingModels.ambientSection_irreducible ρ C hCJ c.sectionData hi,
    f⟩⟩

open ComponentSelection
open SourceContainment.LinearThree.CentralAction.ModuleAlternatives
open SourceOrthogonal.LocalAction
variable {G : Type u} [Group G] [Finite G]

/-- Original local inputs supply the natural quotient of the full U_K.
The component SQTK premise is discharged by the intrinsic quotient in the
original-source wrapper. -/
theorem source_data (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hLK : Lv L v ≤ K)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hzOmega : z ∈ omegaOneCenterAmbient (Tv T v))
    (hchar : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hsq : IsSQTK KnownSimple.IsKnownSimple (plusImage K L T z v hL hz K))
    (eC : plusImage K L T z v hL hz K ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hchar
    Nonempty (Data (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K)) := by
  let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hchar
  let : Module.Finite (ZMod 2) (Additive (WK K L T z v)) := Module.Finite.of_finite
  let C := plusImage K L T z v hL hz K
  have hR := plus_twoCore_eq_bot K L T z v hK.1.1 hL hz hSylow
  let : C.Normal := plusImage_K_normal K L T z v hL hz hK hn
  let : IsQuasisimple C := plusImage_K_quasisimple K L T z v hL hz hK hR
  have hc : center C = ⊥ := by
    apply bot_unique
    intro x hx
    have he : eC x ∈ center (commutator (Atlas.G2.Model (ZMod 2))) :=
      (centerCongr eC ⟨x, hx⟩).property
    rw [Theory.SpecificGroups.g2_derived_two_center_eq_bot] at he
    exact mem_bot.mpr (eC.map_eq_one_iff.mp (mem_bot.mp he))
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  let : IsSimpleGroup C := ((QuotientGroup.quotientMulEquivOfEq hc).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup
  have hcentral : centralizer (C : Set (Gplus K L T z v hL hz)) = ⊥ := by
    obtain ⟨S, hS⟩ := hSylow
    have hT : IsPGroup 2 (Tv T v) := hS ▸ S.isPGroup'.map (Gv v).subtype
    have hquot : IsPGroup 2 (Gplus K L T z v hL hz ⧸ C) :=
      isPGroup_quotient_of_sup_eq_top C (plusImage K L T z v hL hz (Tv T v))
        (hT.comap_subtype.map _)
        (AlternatingModels.component_plus_generation K L T z v hL hz hn hLK)
    exact centralizer_eq_bot_of_simple_two_quotient C
      (Group.IsPerfect.not_isMulCommutative C) hquot hR
  exact nonempty_data _ C eC hcentral hsq
    (wkRepresentation_faithful K L T z v hL hz)
    (component_plus_le_offenders K L T z v hL hz
      ((mem_omegaOneCenterAmbient_iff (Tv T v) z).mp hzOmega).1 hSylow hK hn)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.G2Selection.Action
