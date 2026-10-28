module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.FullKernel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SevenNatural
public import Theory.Representation.BinaryPermutation.SevenSourceCubics.Alternating

/-!
# The alternating weight-four branch of original 14.7.50

Both disjoint cubics are even and have the required S₃ quotient over the
alternating Sylow of order eight. Lifting their full preimages therefore
places their rank-two join in the original flag-plane centralizer, contrary
to 14.7.4(3). The final theorem applies this to the actual proper quotient
of U_I/V₁, retaining the source Sylow and flag-word markings.
Source: Aschbacher–Smith 14.7.50, printed p.1065, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open BinaryPermutation.SevenSourceCubics
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Both marked source cubics lift through the original nonsplit two-kernel. -/
theorem local_alternating_weight_four_centralizer_rank_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (π : I →* alternatingGroup (Fin 7)) (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker)
    (hT : ((T : Subgroup G).subgroupOf I).map π = Alternating.two)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) I W}
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap ((BinaryPermutation.alternatingCoreRepresentation (Fin 7)).comp π))
    (hp : p.toLinearMap.ker ≠ ⊤)
    (hword : ∀ z : F.UH I, (z : G) ∈ F.Vi 2 →
      p (c.coordinates z).toAdd = 0 ∨ p (c.coordinates z).toAdd = point) :
    2 ≤ primeRank 3 (centralizer (F.Vi 2 : Set G)) := by
  apply Alternating.two_le_join_rank.trans
  apply local_two_cubic_plane_centralizer_rank_at h hab structural previous faithful
    I hI π hπ hk c p hp Alternating.firstGroup Alternating.secondGroup
  intro A hA
  have hrow : Nat.card A = 3 ∧
      Nonempty (((A ⊔ Alternating.two : Subgroup (alternatingGroup (Fin 7))) ⧸
        pCore 2 (A ⊔ Alternating.two : Subgroup (alternatingGroup (Fin 7)))) ≃*
          Equiv.Perm (Fin 3)) ∧
      ∀ a ∈ A, BinaryPermutation.alternatingCoreRepresentation (Fin 7) a point = point := by
    rcases Set.mem_insert_iff.mp hA with rfl | hA
    · exact ⟨Alternating.first_card,Alternating.first_join_quotient,Alternating.firstGroup_fixes⟩
    · have he : A = Alternating.secondGroup := Set.mem_singleton_iff.mp hA
      subst A
      exact ⟨Alternating.second_card,Alternating.second_join_quotient,Alternating.secondGroup_fixes⟩
  refine ⟨hrow.1,by rw [hT]; exact hrow.2.1,?_⟩
  intro a ha z hz
  rcases hword z hz with he | he
  · rw [he,map_zero]
  · rw [he]
    exact hrow.2.2 a ha

private def quotientSection {I : Subgroup G} [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) :
    BinaryConjugationSection I (F.UH I) (F.Vi 1)
      (a.representation.comp (QuotientGroup.mk' (pCore 2 I))) where
  section_le := a.le_local
  kernel_le := a.kernel_le
  normalized := a.normalizes
  coordinates := {
    toFun z := Multiplicative.ofAdd (Additive.ofMul
      (QuotientGroup.mk' ((F.Vi 1).subgroupOf (F.UH I)) z))
    map_one' := (QuotientGroup.mk' _).map_one
    map_mul' := (QuotientGroup.mk' _).map_mul }
  onto := QuotientGroup.mk'_surjective _
  kernel_eq := QuotientGroup.ker_mk' _
  equivariant i z := (a.conjugation i z).symm

/-- The actual proper invariant quotient application, with its full original
two-core and module kernel. Only the remaining model markings are explicit. -/
theorem local_alternating_weight_four_quotient_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hm : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (N : Subrepresentation a.representation) (hN : N ≠ ⊤)
    (b : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7))
    (m : Representation.Equiv ((BinaryPermutation.alternatingCoreRepresentation (Fin 7)).comp
      b.toMonoidHom) N.quotientRepresentation)
    (hT : ((T : Subgroup G).subgroupOf I).map
      (b.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))) = Alternating.two)
    (hword : ∀ z : F.UH I, (z : G) ∈ F.Vi 2 →
      m.symm (N.toSubmodule.mkQ (Additive.ofMul
        (QuotientGroup.mk' ((F.Vi 1).subgroupOf (F.UH I)) z))) = 0 ∨
      m.symm (N.toSubmodule.mkQ (Additive.ofMul
        (QuotientGroup.mk' ((F.Vi 1).subgroupOf (F.UH I)) z))) = point) : False := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let π := b.toMonoidHom.comp q
  let c := quotientSection a
  let p : Representation.IntertwiningMap (a.representation.comp q)
      ((BinaryPermutation.alternatingCoreRepresentation (Fin 7)).comp π) := {
    toLinearMap := m.symm.toLinearMap.comp N.toSubmodule.mkQ
    isIntertwining' := by
      intro i
      apply LinearMap.ext
      intro z
      exact LinearMap.congr_fun (m.symm.isIntertwining' (q i)) (N.toSubmodule.mkQ z) }
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
    have hz' : N.toSubmodule.mkQ z = 0 := m.symm.injective (hz.trans (map_zero m.symm).symm)
    exact (Submodule.Quotient.mk_eq_zero _).mp hz'
  have hk : IsPGroup 2 π.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ b.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hr := local_alternating_weight_four_centralizer_rank_at h hab structural previous faithful
    I hI π (b.surjective.comp (QuotientGroup.mk'_surjective _)) hk hT c p hp hword
  have hb := plane_centralizer_three_rank_le_one_at h structural hm
  omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
