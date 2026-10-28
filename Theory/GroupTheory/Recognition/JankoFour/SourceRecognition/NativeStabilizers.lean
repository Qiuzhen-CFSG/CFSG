module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CoreStabilizers

/-!
# The original cubic maps and native vector stabilizers

The full core-action isomorphism sends the actual cubic covering kernel to
the native scalar subgroup. Quotienting gives an explicit automorphism-group
marking whose square with both original projections commutes. Restricting the
same isomorphism identifies each literal image of C_H(r) under H → H/Q with
the actual native vector stabilizer. Finally, a nonidentity element of the
cubic kernel generates it; the fixed-point-free cubic action therefore proves
that the original projection is injective on every noncentral core stabilizer.

The final assembly constructs this comparison for both involution classes,
without assuming any local geometry or subgroup splitting.
Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*, Invent.
Math. 105 (1991), (4.1–2), printed p.597, DOI 10.1007/BF01232280. The native
stabilizers still require their stated S₅/E₃₂ and S₅/E₁₆ structure proofs.
This is local core-action comparison, not comparison of the later geometry.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Subgroup Sporadic.Mathieu Representation
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open M22TripleCover.Ambient

variable {G : Type*} [Group G] [Finite G] {z : G} (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))
variable (X : Sylow 3 (LocalGeometry.CubicLift.subgroup e))
variable [IsExtraspecial 2 (core z)]

theorem coreAmbientHom_on_inner (g : innerPreimage e) :
    coreAmbientHom h e X g = coverInclusion (innerPreimageTripleEquiv h e g) :=
  markedTripleAmbientHom_on_component _ _ _ _ g

/-- The actual three-element covering kernel maps to the native scalar subgroup. -/
theorem coreAmbientHom_kernel_image :
    e.projection.ker.map (coreAmbientHom h e X) = scalarSubgroup := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨g,hg,rfl⟩
    have hi : g ∈ innerPreimage e := by
      change e.projection g ∈ MulAut.innerSubgroup M22
      rw [show e.projection g = 1 from hg]
      exact one_mem _
    let c : innerPreimage e := ⟨g,hi⟩
    have hc : c ∈ center (innerPreimage e) :=
      innerProjection_kernel_central e ((innerProjection_ker_iff e c).mpr hg)
    change coreAmbientHom h e X c ∈ scalarSubgroup
    rw [coreAmbientHom_on_inner, coverInclusion_mem_scalar]
    exact (centerCongr (innerPreimageTripleEquiv h e) ⟨c,hc⟩).property
  · rw [card_map_of_injective (coreAmbientHom_injective h e X), e.kernel_card, scalarSubgroup_card]

/-- The induced automorphism-group marking records the original projection,
including its full cubic kernel, under the native matrix identification. -/
noncomputable def coreAmbientAutEquiv : MulAut M22 ≃* MulAut M22 :=
  e.quotientEquiv.symm.trans
    ((QuotientGroup.congr e.projection.ker scalarSubgroup (coreAmbientEquiv h e X)
      (coreAmbientHom_kernel_image h e X)).trans scalarQuotientEquiv)

theorem coreAmbientAutEquiv_projection (g : centralizer z ⧸ core z) :
    coreAmbientAutEquiv h e X (e.projection g) =
      quotientConjugation (coreAmbientHom h e X g) := by
  have he : e.quotientEquiv.symm (e.projection g) = QuotientGroup.mk' e.projection.ker g :=
    e.quotientEquiv.symm_apply_apply (QuotientGroup.mk' e.projection.ker g)
  change scalarQuotientEquiv (QuotientGroup.congr e.projection.ker scalarSubgroup
    (coreAmbientEquiv h e X) (coreAmbientHom_kernel_image h e X)
    (e.quotientEquiv.symm (e.projection g))) = _
  rw [he]
  exact scalarQuotientEquiv_mk _

/-- Stabilizer in the actual full native cubic action, before any scalar quotient. -/
noncomputable def nativeVectorStabilizer (v : M22TripleCover.BinarySpace) : Subgroup actionGroup where
  carrier := {g | binaryAction g v = v}
  one_mem' := by change binaryAction 1 v = v; rw [map_one]; rfl
  mul_mem' := by
    intro a b ha hb
    change binaryAction (a*b) v = v
    rw [map_mul,Module.End.mul_apply,hb,ha]
  inv_mem' := by
    intro g hg
    have he := congrArg (binaryAction g⁻¹) hg
    rw [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one] at he
    exact he.symm

theorem coreVectorStabilizer_native_image (r : core z) :
    (coreVectorStabilizer h r).map (coreAmbientHom h e X) =
      nativeVectorStabilizer (coreNativeEquiv h e X
        (Additive.ofMul (QuotientGroup.mk' (center (core z)) r))) := by
  ext g
  obtain ⟨g,rfl⟩ := coreAmbientHom_surjective h e X g
  rw [mem_map_iff_mem (coreAmbientHom_injective h e X)]
  change coreBinaryRepresentation h g _ = _ ↔ binaryAction (coreAmbientHom h e X g) _ = _
  rw [← coreAmbientHom_intertwines]
  exact (coreNativeEquiv h e X).injective.eq_iff.symm

/-- Isomorphism of the full vector stabilizers, induced by the source action. -/
noncomputable def coreVectorStabilizerNativeEquiv (r : core z) :
    coreVectorStabilizer h r ≃* nativeVectorStabilizer (coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r))) :=
  ((coreVectorStabilizer h r).equivMapOfInjective (coreAmbientHom h e X)
    (coreAmbientHom_injective h e X)).trans
      (MulEquiv.subgroupCongr (coreVectorStabilizer_native_image h e X r))

/-- The actual C_H(r) image under H → H/Q has the native stabilizer structure. -/
noncomputable def coreCentralizerImageNativeEquiv (r : core z) (hr : r ∉ center (core z)) :
    (Subgroup.centralizer ({(r : centralizer z)} : Set (centralizer z))).map
      (QuotientGroup.mk' (core z)) ≃* nativeVectorStabilizer (coreNativeEquiv h e X
        (Additive.ofMul (QuotientGroup.mk' (center (core z)) r))) :=
  (MulEquiv.subgroupCongr (coreVectorStabilizer_eq_centralizer_image h r hr).symm).trans
    (coreVectorStabilizerNativeEquiv h e X r)

/-- The original cubic projection is faithful on every noncentral core
stabilizer. Its kernel cannot be discarded before proving this fact. -/
theorem coreVectorStabilizer_projection_injective (r : core z) (hr : r ∉ center (core z)) :
    Function.Injective (e.projection.comp (coreVectorStabilizer h r).subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro g hg
  apply mem_bot.mpr
  by_contra hne
  let k : e.projection.ker := ⟨g.val,hg⟩
  have hk : k ≠ 1 := by
    intro hk
    apply hne
    apply Subtype.ext
    exact congrArg (fun x : e.projection.ker => x.val) hk
  have hgen : zpowers g.val = e.projection.ker := by
    have he := congrArg (fun S : Subgroup e.projection.ker => S.map e.projection.ker.subtype)
      (zpowers_eq_top_of_prime_card e.kernel_card hk)
    simpa only [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      Subgroup.subtype_apply, k] using he
  have hle : e.projection.ker ≤ coreVectorStabilizer h r := by
    rw [← hgen]
    exact zpowers_le.mpr g.property
  have hv := cubicKernel_fixed_eq_zero_of_triple h e (innerDerived_is_triple h e).some
    (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)) (fun k => hle k.property)
  exact hr ((QuotientGroup.eq_one_iff r).mp (congrArg Additive.toMul hv))

omit [IsExtraspecial 2 (core z)] in
include h in
/-- Constructed local comparison for both source classes, with the literal
cubic map and centralizer images retained. -/
theorem source_involution_native_stabilizers :
    letI := h.extraspecial
    ∃ (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))
      (X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)),
      Function.Bijective (coreAmbientHom h e X) ∧
      e.projection.ker.map (coreAmbientHom h e X) = scalarSubgroup ∧
      (∀ g, coreAmbientAutEquiv h e X (e.projection g) =
        quotientConjugation (coreAmbientHom h e X g)) ∧
      ∃ r₁ r₂ : core z,
        orderOf r₁ = 2 ∧ orderOf r₂ = 2 ∧
        r₁ ∉ center (core z) ∧ r₂ ∉ center (core z) ∧
        ¬ IsConj (r₁ : centralizer z) (r₂ : centralizer z) ∧
        Nonempty ((Subgroup.centralizer ({(r₁ : centralizer z)} : Set (centralizer z))).map
          (QuotientGroup.mk' (core z)) ≃* nativeVectorStabilizer (VectorOrbits.decode 4)) ∧
        Nonempty ((Subgroup.centralizer ({(r₂ : centralizer z)} : Set (centralizer z))).map
          (QuotientGroup.mk' (core z)) ≃* nativeVectorStabilizer (VectorOrbits.decode 7)) ∧
        (∀ r : core z, r ∉ center (core z) →
          Function.Injective (e.projection.comp (coreVectorStabilizer h r).subtype)) ∧
        ∀ r : core z, orderOf r = 2 → r ∉ center (core z) →
          IsConj (r : centralizer z) (r₁ : centralizer z) ∨
            IsConj (r : centralizer z) (r₂ : centralizer z) := by
  let := h.extraspecial
  obtain ⟨e⟩ := h.cubic_quotient
  obtain ⟨X⟩ := (inferInstance : Nonempty (Sylow 3 (LocalGeometry.CubicLift.subgroup e)))
  refine ⟨e,X,⟨coreAmbientHom_injective h e X,coreAmbientHom_surjective h e X⟩,
    coreAmbientHom_kernel_image h e X,coreAmbientAutEquiv_projection h e X,?_⟩
  obtain ⟨r₁,r₂,h₁,h₂,h₁c,h₂c,e₁,e₂,hcov⟩ := source_involution_orbit_cover h e X
  refine ⟨r₁,r₂,h₁,h₂,h₁c,h₂c,?_,?_,?_,coreVectorStabilizer_projection_injective h e,hcov⟩
  · intro hc
    have he := core_label_of_isConj h e X r₁ r₂ hc
    rw [e₁,e₂,VectorOrbits.label_decode,VectorOrbits.label_decode] at he
    exact (by decide : (VectorOrbits.treeRow 4).root ≠ (VectorOrbits.treeRow 7).root) he
  · have hn := coreCentralizerImageNativeEquiv h e X r₁ h₁c
    rw [e₁] at hn
    exact ⟨hn⟩
  · have hn := coreCentralizerImageNativeEquiv h e X r₂ h₂c
    rw [e₂] at hn
    exact ⟨hn⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
