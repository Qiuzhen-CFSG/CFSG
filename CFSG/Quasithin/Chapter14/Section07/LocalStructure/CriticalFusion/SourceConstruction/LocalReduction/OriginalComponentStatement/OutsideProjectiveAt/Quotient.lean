module
public import Theory.Representation.EssentialCyclicQuotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.CyclicFlag
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Coordinates
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.SolvableConclusion

/-!
# A normal original component survives in an irreducible quotient

The original Sylow-fixed cyclic flag and the normal quasisimple component
select an actual irreducible quotient retaining component movement. Only
structural facts at the original group and Sylow are used. The normality
input is supplied by the separate projective-model source theorem.
Source: Aschbacher–Smith 14.7.42, printed pp.1061–1062.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open BinaryLinearThree.ParabolicCyclic
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjectiveAt
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open AlternatingSevenSource EightSource
universe u v
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  {I : Subgroup G} {ρ : Representation (ZMod 2) I W}

/-- Every actual original component survives in some irreducible quotient
of the specified literal local two-core action. Nontrivial component movement is derived from the original hypotheses;
normality is an explicit intermediate input. -/
theorem local_component_irreducible_quotient_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) [C.Normal] (hC : C.IsCComponent)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) :
    ∃ N : Subrepresentation a.representation, IsCoatom N ∧
      IsIrreducible N.quotientRepresentation ∧
      ¬ C.map (QuotientGroup.mk' (pCore 2 I)) ≤ N.quotientRepresentation.ker := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let K := C.map q
  let : K.Normal := (inferInstance : C.Normal).map q (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple K :=
    (WholeResidualAssembly.GuardedSource.local_component_star_isComponent h hab structural previous faithful I hI C hC).2
  have hp : IsPPerfect 2 K := by
    intro R hR htwo
    let := hR
    by_contra hne
    let : Nontrivial (K ⧸ R) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (K ⧸ R) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective R)
    exact Group.IsPerfect.not_isNilpotent (K ⧸ R) htwo.isNilpotent
  have hn : K ≠ ⊥ := by
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    exact (nontrivial_iff_ne_bot K).mp inferInstance
  have hmove : ¬ K ≤ a.representation.ker := by
    intro hk
    apply hn
    apply bot_unique
    intro k hkK
    exact a.faithful ((hk hkK).trans a.representation.map_one.symm)
  obtain ⟨x,_,_,hcyc,hfix⟩ := local_exists_sylow_fixed_cyclic_at h hI (localQuotientSection a)
  let S := (T.subtype (F.sylow_le_of_mem_Hz hI)).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 I))
  have hfixed : ∀ g ∈ (S : Subgroup (I ⧸ pCore 2 I)), a.representation g x = x := by
    intro g hg
    obtain ⟨t,ht,rfl⟩ := hg
    exact hfix t ht
  have hgen : orbitSpan a.representation ⊤ x = ⊤ := by
    apply top_unique
    rw [←hcyc]
    apply Submodule.span_le.mpr
    rintro _ ⟨g,_,rfl⟩
    exact orbit_mem a.representation ⊤ x (q g) (mem_top _)
  exact EssentialCyclicQuotient.exists_irreducible_quotient a.representation K hp hmove S x hfixed hgen

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjectiveAt
