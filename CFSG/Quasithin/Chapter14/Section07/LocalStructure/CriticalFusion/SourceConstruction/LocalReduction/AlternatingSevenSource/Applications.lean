module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.FullKernel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SevenNatural
public import Theory.Representation.BinaryPermutation.SevenSourceCubics

/-!
# The marked symmetric weight-four branch of 14.7.50

On the natural six-space the two disjoint source cubics fix the weight-four
point. Their model Sylow joins have exactly the required S₃ quotients.
The full-kernel lifting theorem therefore forces three-rank at least two
in C_G(V₂), contrary to 14.7.4(3) when the original point core moves V₂.

The final application uses the literal maximal quotient of U_I/V₁ and its
equivariant natural-module marking. The Sylow and flag-word markings remain
explicit: deriving them in the partition branch, as well as excluding the
other branches, is part of the remaining source assembly.
Source: Aschbacher–Smith 14.7.50, final paragraph, p.1065, refs/quasithin.pdf.
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
theorem local_symmetric_weight_four_centralizer_rank_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (π : I →* Equiv.Perm (Fin 7)) (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker)
    (hT : ((T : Subgroup G).subgroupOf I).map π = standardTwo)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) I W}
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap ((BinaryPermutation.coreRepresentation (Fin 7)).comp π))
    (hp : p.toLinearMap.ker ≠ ⊤)
    (hword : ∀ z : F.UH I, (z : G) ∈ F.Vi 2 →
      p (c.coordinates z).toAdd = 0 ∨ p (c.coordinates z).toAdd = point) :
    2 ≤ primeRank 3 (centralizer (F.Vi 2 : Set G)) := by
  apply two_le_join_rank.trans
  apply local_two_cubic_plane_centralizer_rank_at h hab structural previous faithful
    I hI π hπ hk c p hp firstGroup secondGroup
  intro A hA
  have hrow : Nat.card A = 3 ∧
      Nonempty (((A ⊔ standardTwo : Subgroup (Equiv.Perm (Fin 7))) ⧸
        pCore 2 (A ⊔ standardTwo : Subgroup (Equiv.Perm (Fin 7)))) ≃*
          Equiv.Perm (Fin 3)) ∧
      ∀ a ∈ A, BinaryPermutation.coreRepresentation (Fin 7) a point = point := by
    rcases Set.mem_insert_iff.mp hA with rfl | hA
    · exact ⟨first_card,first_join_quotient,firstGroup_fixes⟩
    · have he : A = secondGroup := Set.mem_singleton_iff.mp hA
      subst A
      exact ⟨second_card,second_join_quotient,secondGroup_fixes⟩
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
theorem local_symmetric_weight_four_quotient_impossible_at
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
    (b : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 7))
    (m : Representation.Equiv ((BinaryPermutation.coreRepresentation (Fin 7)).comp
      b.toMonoidHom) N.quotientRepresentation)
    (hT : ((T : Subgroup G).subgroupOf I).map
      (b.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))) = standardTwo)
    (hword : ∀ z : F.UH I, (z : G) ∈ F.Vi 2 →
      m.symm (N.toSubmodule.mkQ (Additive.ofMul
        (QuotientGroup.mk' ((F.Vi 1).subgroupOf (F.UH I)) z))) = 0 ∨
      m.symm (N.toSubmodule.mkQ (Additive.ofMul
        (QuotientGroup.mk' ((F.Vi 1).subgroupOf (F.UH I)) z))) = point) : False := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let π := b.toMonoidHom.comp q
  let c := quotientSection a
  let p : Representation.IntertwiningMap (a.representation.comp q)
      ((BinaryPermutation.coreRepresentation (Fin 7)).comp π) := {
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
  have hr := local_symmetric_weight_four_centralizer_rank_at h hab structural previous faithful
    I hI π (b.surjective.comp (QuotientGroup.mk'_surjective _)) hk hT c p hp hword
  have hb := plane_centralizer_three_rank_le_one_at h structural hm
  omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
