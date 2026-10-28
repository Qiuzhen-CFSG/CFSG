module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.CubicSpan
public import Theory.Representation.BinaryPermutation.SevenSourceCubics.Alternating

/-!
# The pair-word orbit contradiction for an alternating quotient

The pair-rotation cubic is even. Its join with the alternating Sylow has
order twenty-four and quotient S₃ by its two-core. The original cubic
orbit bound therefore excludes the pair word for A₇ just as for S₇.
Source: Aschbacher–Smith 14.7.50, printed p.1065, refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Equiv Representation Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.NaturalMarking
open BinaryPermutation.SevenSourceCubics
abbrev A7 := alternatingGroup (Fin 7)
def alternatingCycle : A7 := ⟨BinaryPermutation.SevenSourceSpan.cycle, by
  rw [Perm.mem_alternatingGroup]
  decide⟩
def alternatingAxis : Subgroup A7 := zpowers alternatingCycle

theorem alternatingCycle_order : orderOf alternatingCycle = 3 :=
  orderOf_eq_prime (by decide : alternatingCycle ^ 3 = 1) (by decide)

theorem alternatingAxis_card : Nat.card alternatingAxis = 3 :=
  (Nat.card_zpowers alternatingCycle).trans alternatingCycle_order

/-- The pair rotation retains the exact source quotient in A₇. -/
theorem alternatingAxis_join_quotient :
    Nonempty (((alternatingAxis ⊔ Alternating.two : Subgroup A7) ⧸
      pCore 2 (alternatingAxis ⊔ Alternating.two : Subgroup A7)) ≃* Perm (Fin 3)) :=
  Alternating.cubic_join_quotient alternatingCycle alternatingCycle_order
    synthemeOvergroup inf_le_right (by decide) synthemeOvergroup_card
    ⟨swap 2 4 * swap 3 5, by rw [Perm.mem_alternatingGroup]; decide⟩
    (by decide) (by decide)
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.NaturalMarking

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open BinaryPermutation SevenSourceSpan SevenSourceCubics
universe u v
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A marked pair word cannot occur as the flag point in a proper natural
quotient: its source cubic would generate a three-space inside the seed plane. -/
theorem local_alternating_weight_two_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (π : I →* alternatingGroup (Fin 7)) (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker)
    (hT : ((T : Subgroup G).subgroupOf I).map π = Alternating.two)
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) I W}
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap ((alternatingCoreRepresentation (Fin 7)).comp π))
    (hp : p.toLinearMap.ker ≠ ⊤)
    (z : F.UH I) (hz : (z : G) ∈ F.Vi 2)
    (hword : p (c.coordinates z).toAdd = SevenSourceSpan.point) : False := by
  obtain ⟨A,hAp,hAB,he⟩ := cubic_lift_with_sylow_join I hI π hπ hk NaturalMarking.alternatingAxis NaturalMarking.alternatingAxis_card
    (by rw [hT]; exact NaturalMarking.alternatingAxis_join_quotient)
  let Y := A.map I.subtype
  have hYp : IsPPerfect 2 Y := hAp.of_surjective
    (I.subtype.subgroupMap A) (I.subtype.subgroupMap_surjective A)
  let E := (c.imageSpace (conjugateSpanBy (F.Vi 2) Y)).map p.toLinearMap
  have hb := local_quotient_cubic_plane_span_dimension_at h hab structural previous faithful
    I hI c p hp Y (map_subtype_le A) hYp he
  have hlo : 3 ≤ Module.finrank (ZMod 2) E := by
    apply three_le_of_orbit_mem
    intro i
    have hm : NaturalMarking.alternatingCycle ^ i.val ∈ A.map π := hAB.symm ▸ pow_mem (mem_zpowers NaturalMarking.alternatingCycle) i.val
    obtain ⟨g,hg,hgπ⟩ := hm
    let u : F.UH I := ⟨g.val*z.val*g.val⁻¹,
      (mem_normalizer_iff.mp (c.normalized g.property) z.val).mp z.property⟩
    have hu : (u : G) ∈ conjugateSpanBy (F.Vi 2) Y :=
      subset_closure ⟨g.val,mem_map_of_mem I.subtype hg,z.val,hz,rfl⟩
    have hmem : p (c.coordinates u).toAdd ∈ E :=
      ⟨_,(c.mem_imageSpace_iff _ _).mpr ⟨u,hu,rfl⟩,rfl⟩
    have heq : p (c.coordinates u).toAdd =
        alternatingCoreRepresentation (Fin 7) (NaturalMarking.alternatingCycle ^ i.val) SevenSourceSpan.point := by
      rw [show (c.coordinates u).toAdd = ρ g (c.coordinates z).toAdd
        from c.equivariant g z,p.isIntertwining]
      change alternatingCoreRepresentation (Fin 7) (π g) (p (c.coordinates z).toAdd) = _
      rw [hgπ,hword]
    rwa [heq] at hmem
  change Module.finrank (ZMod 2) E = 1 ∨ Module.finrank (ZMod 2) E = 2 at hb
  omega
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

/-- Rank-three contradiction on the literal proper quotient of U_I/V₁.
The quotient map and natural-module isomorphism are the original ones. -/
theorem local_alternating_weight_two_quotient_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (N : Subrepresentation a.representation) (hN : N ≠ ⊤)
    (b : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7))
    (m : Representation.Equiv ((BinaryPermutation.alternatingCoreRepresentation (Fin 7)).comp
      b.toMonoidHom) N.quotientRepresentation)
    (hT : ((T : Subgroup G).subgroupOf I).map
      (b.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))) = Alternating.two)
    (z : F.UH I) (hz : (z : G) ∈ F.Vi 2)
    (hword : m.symm (N.toSubmodule.mkQ (Additive.ofMul
      (QuotientGroup.mk' ((F.Vi 1).subgroupOf (F.UH I)) z))) =
        SevenSourceSpan.point) : False := by
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
  exact local_alternating_weight_two_impossible_at h hab structural previous faithful
    I hI π (b.surjective.comp (QuotientGroup.mk'_surjective _)) hk hT c p hp z hz hword

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
