module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource.B4
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.ModuleSelection.Seed
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Coordinates
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.SeedGeometry

/-!
# The actual S₈ quotient module in original 14.7.51

The completed B.4 constituent and ambient inputs give either the marked
natural six-space or the actual natural-plus-dual restriction. This retains
the possible exchanged constituents of an irreducible ambient quotient.
The marked middle-node minimal parabolic then excludes the eight-space:
the original seed remains a plane, its three nonzero vectors form one orbit,
and its parabolic fixes it. No component irreducibility is assumed.

The explicit group placement is supplied by the separate graph-node marking.
Source: Aschbacher–Smith 14.7.51, printed p.1065, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction
open OrthogonalQuotient
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter15.Section03.AbelianAmalgam
universe u v

/-- The complete ambient irreducible S₈ alternatives with both B.4 inputs proved. -/
theorem symmetric_eight_module_alternatives
    {H : Type u} {X : Type v} [Group H] [Finite H]
    [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X)
    (eH : H ≃* Equiv.Perm (Fin 8)) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (eK : K ≃* BinaryLinear.GL FourSpace)
    (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (hq : quadraticRatio ρ ≤ 2) :
    IsEightNatural ρ eH ∨ IsNaturalDualRestriction ρ K eK := by
  obtain ⟨A,hA,hquad,hb⟩ := (quadraticRatio_le_two_iff ρ).mp hq
  exact B4Extraction.representation_alternatives ρ eH K hK eK hf hi A hA hquad hb
    (OriginalSource.symmetric_b4 K eH hK) (OriginalSource.component_b4 K eH eK hK)

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The marked original middle parabolic selects the natural six-space on the
literal proper quotient. Seed rank, stability and transitivity are all derived
from the original flag and its natural L₁ action. -/
theorem local_symmetric_eight_quotient_natural_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (N : Subrepresentation a.representation) (hN : N ≠ ⊤)
    (hirr : IsIrreducible N.quotientRepresentation)
    (hq : quadraticRatio N.quotientRepresentation ≤ 2)
    (eH : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 8))
    (eK : C.map (QuotientGroup.mk' (pCore 2 I)) ≃* BinaryLinear.GL FourSpace)
    (hK : (C.map (QuotientGroup.mk' (pCore 2 I))).map eH.toMonoidHom =
      alternatingGroup (Fin 8))
    (P : Subgroup (C.map (QuotientGroup.mk' (pCore 2 I))))
    (A B : Submodule (ZMod 2) FourSpace) (hAB : A ≤ B)
    (hA : Module.finrank (ZMod 2) A = 1) (hB : Module.finrank (ZMod 2) B = 3)
    (hP : P.map eK.toMonoidHom = BinaryLinear.parabolic A ⊓ BinaryLinear.parabolic B)
    (hLP : ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≤
      P.map (C.map (QuotientGroup.mk' (pCore 2 I))).subtype)
    (hPE : P.map (C.map (QuotientGroup.mk' (pCore 2 I))).subtype ≤
      ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) :
    IsEightNatural N.quotientRepresentation eH := by
  rcases symmetric_eight_module_alternatives N.quotientRepresentation eH
    (C.map (QuotientGroup.mk' (pCore 2 I))) hK eK
    (AlternatingSevenSource.local_proper_quotient_faithful_at d h hab structural previous faithful
      earlier source47 I hI C hC a N hN) hirr hq with hn | hd
  · exact hn
  exfalso
  let q := QuotientGroup.mk' (pCore 2 I)
  let c := AlternatingSevenSource.localQuotientSection a
  let p := AlternatingSevenSource.localQuotientProjection a N
  have hp := AlternatingSevenSource.localQuotientProjection_ker_ne_top a N hN
  let S := (c.imageSpace V).map p.toLinearMap
  have hS : Module.finrank (ZMod 2) S = 2 :=
    AlternatingSevenSource.local_quotient_seed_finrank h hI c p hp
  apply not_naturalDual_of_transitive_seed N.quotientRepresentation _ eK P A B hAB hA hB hP S hS ?_ ?_ hd
  · intro g hg x hx
    obtain ⟨i,hi,hig⟩ := hPE (mem_map_of_mem (C.map q).subtype hg)
    obtain ⟨w,hw,rfl⟩ := hx
    have hn : F.Li L 1 ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) :=
      sup_le ((F.Li_le L 1).trans (inf_le_left.trans h.chosen.normalizes))
        (h.sylow_normalizes_seed_at structural)
    refine ⟨a.representation (q i) w,c.imageSpace_apply_mem V i (hn hi) w hw,?_⟩
    change N.quotientRepresentation (q i) (N.toSubmodule.mkQ w) =
      N.quotientRepresentation g.val (N.toSubmodule.mkQ w)
    rw [hig]
    rfl
  · intro x hx hx0 y hy hy0
    obtain ⟨l,hl⟩ := AlternatingSevenSource.local_quotient_seed_transitive h hI c p
      x hx hx0 y hy hy0
    let i := inclusion (F.Li_one_le_of_mem_Hz hI) l
    refine ⟨q i,hLP (mem_map_of_mem q l.property),hl⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
