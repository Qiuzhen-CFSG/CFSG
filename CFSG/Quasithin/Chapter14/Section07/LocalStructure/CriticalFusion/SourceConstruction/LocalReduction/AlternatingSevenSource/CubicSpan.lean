module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Cubic
public import Theory.GroupTheory.PGroup.ExtraspecialThreeCubicLifts
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.Quasithin.TwoKernelSubgroupRank
public import Theory.Representation.BinaryPermutation.SevenSourceSpan

/-!
# The rank-three orbit contradiction in original 14.7.50

The pair-rotation cubic has three independent pair words in the natural
six-space. Its full preimage supplies a two-perfect actor with the literal
S₃-over-Sylow quotient. The original 14.7.2 orbit bound then contradicts
this rank-three image, retaining both the group kernel and module kernel.
Source: Aschbacher–Smith 14.7.50, printed p.1065, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
universe u v w w'
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

theorem cubic_lift_with_sylow_join
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    {D : Type v} [Group D] [Finite D]
    (π : I →* D) (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker)
    (B : Subgroup D) (hB : Nat.card B = 3)
    (he : Nonempty (((B ⊔ ((T : Subgroup G).subgroupOf I).map π : Subgroup D) ⧸
      pCore 2 (B ⊔ ((T : Subgroup G).subgroupOf I).map π : Subgroup D)) ≃*
        Equiv.Perm (Fin 3))) :
    ∃ A : Subgroup I, IsPPerfect 2 A ∧ A.map π = B ∧
      Nonempty (((A.map I.subtype ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (A.map I.subtype ⊔ (T : Subgroup G) : Subgroup G)) ≃*
          Equiv.Perm (Fin 3)) := by
  obtain ⟨A,_hAR,hAp,_hSA,_hkA,hAB,_hAk,_hAc⟩ :=
    exists_cubic_residual_lift π hπ hk (⊥ : Subgroup I) B hB (by simp)
  let Y := A.map I.subtype
  have hYI : Y ≤ I := map_subtype_le A
  let J := Y ⊔ (T : Subgroup G)
  have hJI : J ≤ I := sup_le hYI (F.sylow_le_of_mem_Hz hI)
  let f := π.comp (inclusion hJI)
  let P := B ⊔ ((T : Subgroup G).subgroupOf I).map π
  have hAJ : J.subgroupOf I = A ⊔ (T : Subgroup G).subgroupOf I := by
    rw [subgroupOf_sup hYI (F.sylow_le_of_mem_Hz hI)]
    congr 1
    exact comap_map_eq_self_of_injective I.subtype_injective A
  have him : f.range = P := by
    rw [MonoidHom.range_comp,inclusion_range,hAJ,Subgroup.map_sup,hAB]
  have hfk : IsPGroup 2 f.ker := hk.comap_of_injective
    (inclusion hJI) (inclusion_injective hJI)
  have hfrk : IsPGroup 2 f.rangeRestrict.ker := by
    have hh : f.rangeRestrict.ker = f.ker := by
      ext x
      exact Subtype.ext_iff
    rwa [hh]
  let ef := f.rangeRestrict.pCoreQuotientEquiv f.rangeRestrict_surjective hfrk
  let er := MulEquiv.subgroupCongr him
  let eq := QuotientGroup.congr _ _ er (pCore_map_iso 2 er)
  obtain ⟨e⟩ := he
  have heY : Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3)) :=
    ⟨ef.trans (eq.trans e)⟩
  exact ⟨A,hAp,hAB,heY⟩

open BinaryPermutation SevenSourceSpan
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition

/-- A marked pair word cannot occur as the flag point in a proper natural
quotient: its source cubic would generate a three-space inside the seed plane. -/
theorem local_symmetric_weight_two_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (π : I →* Equiv.Perm (Fin 7)) (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker)
    (hT : ((T : Subgroup G).subgroupOf I).map π = standardTwo)
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) I W}
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap ((coreRepresentation (Fin 7)).comp π))
    (hp : p.toLinearMap.ker ≠ ⊤)
    (z : F.UH I) (hz : (z : G) ∈ F.Vi 2)
    (hword : p (c.coordinates z).toAdd = SevenSourceSpan.point) : False := by
  obtain ⟨A,hAp,hAB,he⟩ := cubic_lift_with_sylow_join I hI π hπ hk axis axis_card
    (by rw [hT]; exact axis_join_quotient)
  let Y := A.map I.subtype
  have hYp : IsPPerfect 2 Y := hAp.of_surjective
    (I.subtype.subgroupMap A) (I.subtype.subgroupMap_surjective A)
  let E := (c.imageSpace (conjugateSpanBy (F.Vi 2) Y)).map p.toLinearMap
  have hb := local_quotient_cubic_plane_span_dimension_at h hab structural previous faithful
    I hI c p hp Y (map_subtype_le A) hYp he
  have hlo : 3 ≤ Module.finrank (ZMod 2) E := by
    apply three_le_of_orbit_mem
    intro i
    have hm : cycle ^ i.val ∈ A.map π := hAB.symm ▸ pow_mem (mem_zpowers cycle) i.val
    obtain ⟨g,hg,hgπ⟩ := hm
    let u : F.UH I := ⟨g.val*z.val*g.val⁻¹,
      (mem_normalizer_iff.mp (c.normalized g.property) z.val).mp z.property⟩
    have hu : (u : G) ∈ conjugateSpanBy (F.Vi 2) Y :=
      subset_closure ⟨g.val,mem_map_of_mem I.subtype hg,z.val,hz,rfl⟩
    have hmem : p (c.coordinates u).toAdd ∈ E :=
      ⟨_,(c.mem_imageSpace_iff _ _).mpr ⟨u,hu,rfl⟩,rfl⟩
    have heq : p (c.coordinates u).toAdd =
        coreRepresentation (Fin 7) (cycle ^ i.val) SevenSourceSpan.point := by
      rw [show (c.coordinates u).toAdd = ρ g (c.coordinates z).toAdd
        from c.equivariant g z,p.isIntertwining]
      change coreRepresentation (Fin 7) (π g) (p (c.coordinates z).toAdd) = _
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
theorem local_symmetric_weight_two_quotient_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (N : Subrepresentation a.representation) (hN : N ≠ ⊤)
    (b : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 7))
    (m : Representation.Equiv ((BinaryPermutation.coreRepresentation (Fin 7)).comp
      b.toMonoidHom) N.quotientRepresentation)
    (hT : ((T : Subgroup G).subgroupOf I).map
      (b.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))) = standardTwo)
    (z : F.UH I) (hz : (z : G) ∈ F.Vi 2)
    (hword : m.symm (N.toSubmodule.mkQ (Additive.ofMul
      (QuotientGroup.mk' ((F.Vi 1).subgroupOf (F.UH I)) z))) =
        SevenSourceSpan.point) : False := by
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
  exact local_symmetric_weight_two_impossible_at h hab structural previous faithful
    I hI π (b.surjective.comp (QuotientGroup.mk'_surjective _)) hk hT c p hp z hz hword

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
