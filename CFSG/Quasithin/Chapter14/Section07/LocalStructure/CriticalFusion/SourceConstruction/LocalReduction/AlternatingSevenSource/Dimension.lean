module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Dimension.PairExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Dimension.PairMarking
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.NaturalMarking.Sylow
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Coordinates
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Classification

/-!
# Eliminating the eight-dimensional original local quotient

The four-plus-dual component alternative forces the ambient group to be S₇
and every three-cycle to be fixed-point-free on the quotient. Conjugating
the marking places the actual Sylow at the standard Sylow while retaining
the same representation through an explicit intertwining equivalence.
The two cubic source orbits in the original seed plane then contradict the
fixed-point calculation. This is the missing inference from the full B.4
three-way alternatives to the four-or-natural-six dichotomy in 14.7.50.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter15.Section03.AbelianAmalgam
open Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The eight-dimensional alternative is impossible for a proper irreducible
quotient of the actual original local section. No component irreducibility,
seed marking, or forbidden-branch premise is assumed. -/
theorem local_fourPlusDual_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (N : Subrepresentation a.representation) (hN : N ≠ ⊤)
    (hirr : IsIrreducible N.quotientRepresentation)
    (j : (I ⧸ pCore 2 I) →* Equiv.Perm (Fin 7)) (hj : Function.Injective j)
    (K : Subgroup (I ⧸ pCore 2 I)) (hK : K.map j = alternatingGroup (Fin 7))
    (hcases : j.range = alternatingGroup (Fin 7) ∨ j.range = ⊤)
    (hpair : IsFourPlusDual N.quotientRepresentation (componentInclusion j hj K hK)) : False := by
  have hjs : Function.Surjective j := MonoidHom.range_eq_top.mp
    (fourPlusDual_range_eq_top j hj K hK hpair hirr hcases)
  let b : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 7) := MulEquiv.ofBijective j ⟨hj,hjs⟩
  let σ := N.quotientRepresentation.comp b.symm.toMonoidHom
  have hfree : ∀ g : Equiv.Perm (Fin 7), g.IsThreeCycle →
      ∀ x, σ g x = x → x = 0 :=
    fourPlusDual_threeCycle_fixedPointFree hpair b (componentInclusion_compatible j hj K hK)
  let m : Representation.Equiv (σ.comp b.toMonoidHom) N.quotientRepresentation :=
    .mk (LinearEquiv.refl _ _) (by
      intro g
      change N.quotientRepresentation (b.symm (b g)) = N.quotientRepresentation g
      rw [b.symm_apply_apply])
  let q := QuotientGroup.mk' (pCore 2 I)
  let P := (T.subtype (F.sylow_le_of_mem_Hz hI)).mapSurjective (f := q)
    (QuotientGroup.mk'_surjective _)
  obtain ⟨b',hP,⟨m'⟩⟩ := NaturalMarking.exists_sylow_marking 2 P standardSylow
    σ N.quotientRepresentation b m
  let π := b'.toMonoidHom.comp q
  have hT : ((T : Subgroup G).subgroupOf I).map π = standardTwo := by
    rw [show π = b'.toMonoidHom.comp q from rfl,←Subgroup.map_map]
    exact hP
  let p : Representation.IntertwiningMap (a.representation.comp q) (σ.comp π) := {
    toLinearMap := m'.symm.toLinearMap.comp N.toSubmodule.mkQ
    isIntertwining' := by
      intro i
      apply LinearMap.ext
      intro z
      exact LinearMap.congr_fun (m'.symm.isIntertwining' (q i)) (N.toSubmodule.mkQ z) }
  have hp : p.toLinearMap.ker ≠ ⊤ := by
    intro he
    apply hN
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro z _
    have hz : p z = 0 := by
      change z ∈ p.toLinearMap.ker
      rw [he]
      trivial
    have hz' : N.toSubmodule.mkQ z = 0 := m'.symm.injective (hz.trans (map_zero m'.symm).symm)
    exact (Submodule.Quotient.mk_eq_zero _).mp hz'
  have hk : IsPGroup 2 π.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ b'.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  exact local_threeCycle_fixedPointFree_impossible_at h hab structural previous faithful
    I hI π (b'.surjective.comp (QuotientGroup.mk'_surjective _)) hk hT σ hfree
    (localQuotientSection a) p hp

/-- The actual local quotient has dimension four or is the marked natural
six-space once the full earlier three-way alternatives have been established. -/
theorem local_four_or_natural_of_alternatives_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (N : Subrepresentation a.representation) (hN : N ≠ ⊤)
    (hirr : IsIrreducible N.quotientRepresentation)
    (j : (I ⧸ pCore 2 I) →* Equiv.Perm (Fin 7)) (hj : Function.Injective j)
    (K : Subgroup (I ⧸ pCore 2 I)) (hK : K.map j = alternatingGroup (Fin 7))
    (hcases : j.range = alternatingGroup (Fin 7) ∨ j.range = ⊤)
    (halt : SmallModuleAlternatives N.quotientRepresentation j (componentInclusion j hj K hK)) :
    Module.finrank (ZMod 2)
      (Additive ((F.UH I) ⧸ (F.Vi 1).subgroupOf (F.UH I)) ⧸ N.toSubmodule) = 4 ∨
      IsNatural N.quotientRepresentation j := by
  rcases halt with hfour | hnatural | hpair
  · exact Or.inl hfour.finrank
  · exact Or.inr hnatural
  · exact (local_fourPlusDual_impossible_at h hab structural previous faithful I hI a N hN
      hirr j hj K hK hcases hpair).elim

/-- Source 14.7.50's genuine dimension dichotomy on the literal original
quotient. The full small-module catalogue is proved from its quadratic bound,
and the cubic source geometry excludes the extra eight-dimensional case. -/
theorem local_quotient_dimension_dichotomy_at
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
    (hq : BinaryOffender.quadraticRatio N.quotientRepresentation ≤ 2)
    (j : (I ⧸ pCore 2 I) →* Equiv.Perm (Fin 7)) (hj : Function.Injective j)
    (hCj : (C.map (QuotientGroup.mk' (pCore 2 I))).map j = alternatingGroup (Fin 7))
    (hcases : j.range = alternatingGroup (Fin 7) ∨ j.range = ⊤) :
    Module.finrank (ZMod 2)
      (Additive ((F.UH I) ⧸ (F.Vi 1).subgroupOf (F.UH I)) ⧸ N.toSubmodule) = 4 ∨
      IsNatural N.quotientRepresentation j := by
  exact local_four_or_natural_of_alternatives_at h hab structural previous faithful
    I hI a N hN hirr j hj (C.map (QuotientGroup.mk' (pCore 2 I))) hCj hcases
    (local_quotient_small_module_alternatives_at d h hab structural previous faithful
      earlier source47 I hI C hC a N hN hirr hq j hj hCj)
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
