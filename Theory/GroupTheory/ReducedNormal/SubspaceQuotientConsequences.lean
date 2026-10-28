module

public import Theory.GroupTheory.ReducedNormal.SubspaceConsequences
public import Theory.Representation.BinaryOffender.Homogeneous.EquivTransport

/-!
# Homogeneous transitivity on the literal centralizer quotient

The canonical fixed-space quotient equivalence transports the full
ambient conjugation action and its invariant constituents to the actual
group quotient. It preserves each homogeneous component, so the source
orbit theorem gives transitivity there. The conjugation formula on every
original representative fixes the quotient coordinates explicitly.

Source: Aschbacher–Smith, Lemma 3.2.2(3), combined manuscript of
1 March 2004, printed p.579, from D.3.4(3), p.193.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace Theory.GroupTheory.ReducedNormal
variable {G : Type*} [Group G] (H : Subgroup G)
  (W : Submodule (ZMod 2) (Additive (ModuleGroup H)))

noncomputable def centralizerQuotientEquiv
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W)
    (X : Subgroup G) (hXH : X ≤ H) :
    (fixedQuotientRepresentation (subspaceRepresentation H W hW) (X.subgroupOf H)) ≃ₗ
      (centralizerQuotientRepresentation H W hW X hXH) :=
  Representation.RepEquiv.mk (fixedSpaceQuotientEquiv H W hW X hXH) (fun g => by
    apply LinearMap.ext
    intro v
    change _ = (fixedSpaceQuotientEquiv H W hW X hXH)
      ((fixedQuotientRepresentation (subspaceRepresentation H W hW) (X.subgroupOf H)) g
        ((fixedSpaceQuotientEquiv H W hW X hXH).symm
          (fixedSpaceQuotientEquiv H W hW X hXH v)))
    rw [LinearEquiv.symm_apply_apply]
    rfl)

/-- The actual ambient conjugation action on the literal centralizer quotient. -/
noncomputable def centralizerAmbientRepresentation
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W)
    (X : Subgroup G) (hXH : X ≤ H) [(X.subgroupOf H).Normal] :
    Representation (ZMod 2) H
      (Additive ((subspaceImage H W) ⧸ subspaceCentralizer H W X)) :=
  (fixedSpaceQuotientEquiv H W hW X hXH).conjRingEquiv.toMonoidHom.comp
    ((normalizerQuotientRepresentation (subspaceRepresentation H W hW) (X.subgroupOf H)).comp
      ((MonoidHom.id H).codRestrict _ fun g => by rw [normalizer_eq_top]; exact mem_top g))

@[simp] theorem centralizerAmbientRepresentation_comp
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W)
    (X : Subgroup G) (hXH : X ≤ H) [(X.subgroupOf H).Normal] :
    (centralizerAmbientRepresentation H W hW X hXH).comp (X.subgroupOf H).subtype =
      centralizerQuotientRepresentation H W hW X hXH := by
  ext x q
  obtain ⟨v, rfl⟩ := (fixedSpaceQuotientEquiv H W hW X hXH).surjective q
  rfl

theorem centralizerAmbientRepresentation_mk
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W)
    (X : Subgroup G) (hXH : X ≤ H) [(X.subgroupOf H).Normal]
    (g : H) (u : subspaceImage H W) :
    centralizerAmbientRepresentation H W hW X hXH g
      (Additive.ofMul (QuotientGroup.mk' (subspaceCentralizer H W X) u)) =
        Additive.ofMul (QuotientGroup.mk' (subspaceCentralizer H W X)
          (subspaceConjugation H W hW g u)) := by
  let e := fixedSpaceQuotientEquiv H W hW X hXH
  change e ((normalizerQuotientRepresentation (subspaceRepresentation H W hW)
    (X.subgroupOf H)) _ (e.symm (e (Submodule.Quotient.mk (Additive.ofMul u))))) = _
  rw [e.symm_apply_apply]
  rfl

/-- Homogeneous transitivity on the actual group centralizer quotient. -/
theorem centralizerQuotient_homogeneous_transitive
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W)
    (X : Subgroup G) (hXH : X ≤ H) [(X.subgroupOf H).Normal]
    {I : Submodule (ZMod 2) (Additive (ModuleGroup H))}
    (hI : IsIrrPlus (representation H) (X.subgroupOf H) I)
    (hgen : orbitSpan (representation H) ⊤ I = W)
    (A B : Subrepresentation (centralizerQuotientRepresentation H W hW X hXH))
    (hA : Representation.IsIrreducible A.toRepresentation)
    (hB : Representation.IsIrreducible B.toRepresentation) :
    ∃ g : H, (homogeneousPart A ⊤).map (centralizerAmbientRepresentation H W hW X hXH g) =
      homogeneousPart B ⊤ := by
  let e := centralizerQuotientEquiv H W hW X hXH
  let F := Representation.subrepresentationOrderIsoOfEquiv e
  obtain ⟨A', rfl⟩ := F.surjective A
  obtain ⟨B', rfl⟩ := F.surjective B
  have hA' : Representation.IsIrreducible A'.toRepresentation :=
    (Representation.RepEquiv.irreducible_euqiv (equivSubrepresentation e A')).mpr hA
  have hB' : Representation.IsIrreducible B'.toRepresentation :=
    (Representation.RepEquiv.irreducible_euqiv (equivSubrepresentation e B')).mpr hB
  have hn : (⊤ : Subgroup H) ≤ normalizer (X.subgroupOf H : Set H) := by
    rw [normalizer_eq_top]
  obtain ⟨g, hg⟩ := homogeneousParts_transitive_of_orbitSpan_eq_top
    (subspaceRepresentation H W hW) hn
    (imageSeed_isIrrPlus H W hW hI (hgen ▸ le_orbitSpan _ ⊤ I))
    (imageSeed_orbitSpan_eq_top H W hW I hgen) A' B' hA' hB'
  refine ⟨g.val, ?_⟩
  rw [← homogeneousPart_map_equiv e A', ← homogeneousPart_map_equiv e B', ← Submodule.map_comp]
  have he : (centralizerAmbientRepresentation H W hW X hXH g.val).comp e.toLinearMap =
      e.toLinearMap.comp (normalizerQuotientRepresentation (subspaceRepresentation H W hW)
        (X.subgroupOf H) ⟨g.val, hn g.property⟩) := by
    apply LinearMap.ext
    intro v
    change (fixedSpaceQuotientEquiv H W hW X hXH)
      ((normalizerQuotientRepresentation (subspaceRepresentation H W hW) (X.subgroupOf H))
        ⟨g.val, hn g.property⟩ ((fixedSpaceQuotientEquiv H W hW X hXH).symm
        (fixedSpaceQuotientEquiv H W hW X hXH v))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  rw [he, Submodule.map_comp, hg]

/-- Replace the ambient image by the specified equal subgroup, retaining
the original quotient projection and its full ambient conjugation action. -/
theorem exists_actual_quotient_consequences
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W)
    (X : Subgroup G) (hXH : X ≤ H) [(X.subgroupOf H).Normal]
    {I : Submodule (ZMod 2) (Additive (ModuleGroup H))}
    (hI : IsIrrPlus (representation H) (X.subgroupOf H) I)
    (hgen : orbitSpan (representation H) ⊤ I = W)
    (U : Subgroup G) [IsElementaryAbelian 2 U]
    (hU : subspaceImage H W = U) (hnU : H ≤ normalizer (U : Set G)) :
    ∃ σ : Representation (ZMod 2) H
        (Additive (U ⧸ (centralizer (X : Set G)).subgroupOf U)),
      Representation.IsSemisimpleRepresentation (σ.comp (X.subgroupOf H).subtype) ∧
      (∀ (A B : Subrepresentation (σ.comp (X.subgroupOf H).subtype)),
        Representation.IsIrreducible A.toRepresentation →
        Representation.IsIrreducible B.toRepresentation →
        ∃ g : H, (homogeneousPart A ⊤).map (σ g) = homogeneousPart B ⊤) ∧
      (∀ (g : H) (u : U),
        σ g (Additive.ofMul (QuotientGroup.mk' ((centralizer (X : Set G)).subgroupOf U) u)) =
          Additive.ofMul (QuotientGroup.mk' ((centralizer (X : Set G)).subgroupOf U)
            ⟨(g : G) * (u : G) * (g : G)⁻¹,
              (mem_normalizer_iff.mp (hnU g.property) u).mp u.property⟩)) := by
  subst U
  refine ⟨centralizerAmbientRepresentation H W hW X hXH, ?_, ?_, ?_⟩
  · rw [centralizerAmbientRepresentation_comp]
    exact centralizerQuotient_semisimple H W hW X hXH hI hgen
  · exact centralizerQuotient_homogeneous_transitive H W hW X hXH hI hgen
  · exact centralizerAmbientRepresentation_mk H W hW X hXH

end Theory.GroupTheory.ReducedNormal
