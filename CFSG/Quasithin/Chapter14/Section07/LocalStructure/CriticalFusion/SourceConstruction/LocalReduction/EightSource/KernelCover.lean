module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.ChiefFactors
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.KernelCover.Equality

/-!
# The actual maximal kernel is its natural-or-core commutator

The original flag line is fixed by the full Sylow and maps nontrivially
through every proper invariant quotient. Applied to the perfect central
cover U/[N,C] of the natural quotient U/N, this excludes the augmentation
cover and gives N=[N,C]. The transvection model of that commutator is
therefore a model of N itself, with the same symmetric-eight marking.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction
open OffenderModels OffenderModels.StrongSections.Extensions AlternatingSevenSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original Sylow-fixed flag rules out a nontrivial central layer
between a natural quotient kernel and its actual component commutator. -/
theorem local_natural_kernel_componentCommutator_eq_at
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
    (eH : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 8))
    (hK : (C.map (QuotientGroup.mk' (pCore 2 I))).map eH.toMonoidHom =
      alternatingGroup (Fin 8))
    (hQ : IsEightNatural N.quotientRepresentation eH) :
    componentCommutator a.representation N eH (C.map (QuotientGroup.mk' (pCore 2 I))) hK = N := by
  let b := localQuotientSection a
  let p := localQuotientProjection a N
  let q := QuotientGroup.mk' (pCore 2 I)
  let P := (T.subtype (F.sylow_le_of_mem_Hz hI)).mapSurjective (f := q)
    (QuotientGroup.mk'_surjective _)
  have hd := local_quotient_plane_finrank h hI b p (localQuotientProjection_ker_ne_top a N hN)
  have hn : (b.imageSpace (F.Vi 2)).map p.toLinearMap ≠ ⊥ := by
    intro he
    rw [he,finrank_bot] at hd
    omega
  obtain ⟨y,hy,hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  obtain ⟨x,hx,hxy⟩ := hy
  apply KernelCover.componentCommutator_eq_of_fixed_lift a.representation N eH _ hK hQ
    (local_module_fully_moved_at d h hab structural previous faithful earlier source47
      I hI C hC a) P x
  · rintro _ ⟨t,ht,rfl⟩
    exact local_quotient_plane_sylow_fixed b (IntertwiningMap.id _) t ht x ⟨x,hx,rfl⟩
  · intro hxN
    apply hy0
    exact hxy.symm.trans ((Submodule.Quotient.mk_eq_zero _).mpr hxN)

/-- The transvection commutator is the entire original maximal kernel. -/
theorem local_transvection_kernel_eq_top_at
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
    (eH : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 8)) (A : Subgroup (I ⧸ pCore 2 I))
    (t : TransvectionModels a.representation N (C.map (QuotientGroup.mk' (pCore 2 I))) A eH) :
    t.J = ⊤ := by
  apply Subrepresentation.toSubmodule_injective
  exact t.component_commutator.trans (KernelCover.intrinsic_commutator_eq_top
    a.representation N eH _ t.component_marking
    (local_natural_kernel_componentCommutator_eq_at d h hab structural previous faithful
      earlier source47 I hI C hC a N hN eH t.component_marking t.quotient_natural))

/-- The actual maximal kernel, rather than a proper submodule of it, is
the natural six-space or augmentation seven-space in the original marking. -/
theorem local_transvection_kernel_naturalOrCover_at
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
    (eH : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 8)) (A : Subgroup (I ⧸ pCore 2 I))
    (t : TransvectionModels a.representation N (C.map (QuotientGroup.mk' (pCore 2 I))) A eH) :
    IsEightNaturalOrCover N.toRepresentation eH := by
  have hj := local_transvection_kernel_eq_top_at d h hab structural previous faithful
    earlier source47 I hI C hC a N hN eH A t
  have hsur : Function.Surjective t.J.toSubmodule.subtype := by
    intro x
    exact ⟨⟨x,show x ∈ t.J.toSubmodule from hj ▸ Submodule.mem_top⟩,rfl⟩
  let f := LinearEquiv.ofBijective t.J.toSubmodule.subtype
    ⟨t.J.toSubmodule.subtype_injective,hsur⟩
  have hf (g) (x : N.toSubmodule) :
      f.symm (N.toRepresentation g x) = t.J.toRepresentation g (f.symm x) := by
    apply f.injective
    change f (f.symm (N.toRepresentation g x)) = N.toRepresentation g (f (f.symm x))
    rw [f.apply_symm_apply,f.apply_symm_apply]
  rcases t.model with ⟨e,he⟩ | ⟨e,he⟩
  · exact Or.inl ⟨f.symm.trans e,fun g x => by
      change e (f.symm (N.toRepresentation g x)) = _
      rw [hf,he]
      rfl⟩
  · exact Or.inr ⟨f.symm.trans e,fun g x => by
      change e (f.symm (N.toRepresentation g x)) = _
      rw [hf,he]
      rfl⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
