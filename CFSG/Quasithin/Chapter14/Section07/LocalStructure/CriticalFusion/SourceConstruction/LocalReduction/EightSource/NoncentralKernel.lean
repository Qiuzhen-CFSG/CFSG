module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.Assembly
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightQuotient

/-!
# The actual maximal kernel in the original symmetric-eight branch

The natural quotient of an original linear-four local cannot have its kernel
fixed by the component. Since that component is the actual two-residual,
such fixation would lift the rank-two natural point stabilizer and contradict
the original plane centralizer bound. Thus the remaining kernel carries a
nontrivial component action; this is derived before using the two-section
offender analysis.

Source: Aschbacher–Smith 14.7.4(3), 14.7.48 and 14.7.51, pp.1043,1064–1065.
-/
public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open AlternatingSevenSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The selected original natural quotient has a genuinely noncentral
kernel. The caller supplies no kernel-movement or lifting premise. -/
theorem local_four_quotient_kernel_moved_at
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
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (N : Subrepresentation a.representation) (hN : N ≠ ⊤)
    (hirr : IsIrreducible N.quotientRepresentation)
    (hq : BinaryOffender.quadraticRatio N.quotientRepresentation ≤ 2) :
    ∃ k ∈ C.map (QuotientGroup.mk' (pCore 2 I)),
      ∃ w : N.toSubmodule, N.toRepresentation k w ≠ w := by
  by_contra hn
  push Not at hn
  obtain ⟨b,_,m,hm⟩ := local_four_quotient_natural_marking_at d h hab structural previous
    faithful earlier source47 I hI C hC e a N hN hirr hq
  let q := QuotientGroup.mk' (pCore 2 I)
  let π := b.toMonoidHom.comp q
  let p : Representation.IntertwiningMap (a.representation.comp q)
      ((BinaryPermutation.naturalRepresentation (Fin 8)).comp π) :=
    (m.toLinearMap.comp N.toSubmodule.mkQ).intertwiningMap_of_isIntertwiningMap _ _
      (fun i w => hm (q i) (N.toSubmodule.mkQ w))
  have hres := (local_component_eq_residual_at d h hab structural previous faithful
    earlier source47 I hI C hC).1
  apply local_eight_residual_fixed_quotient_impossible_at h structural
    (local_linear_graph_movement_at d h hab structural previous faithful earlier source47
      I hI C hC 4 (Or.inl rfl) e).1 I hI b (localQuotientSection a) p
  intro w hw k
  have hwN : w ∈ N.toSubmodule := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    apply m.injective
    exact hw.trans (map_zero m).symm
  have hk : q k.val ∈ C.map q := mem_map_of_mem q (hres ▸ k.property)
  exact congrArg Subtype.val (hn (q k.val) hk ⟨w,hwN⟩)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
