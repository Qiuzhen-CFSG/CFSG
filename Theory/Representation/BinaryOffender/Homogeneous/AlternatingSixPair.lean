module
public import Theory.Representation.BinaryOffender.Homogeneous.AlternatingSixInertia
public import Theory.Representation.BinaryOffender.AlternatingSixCentralCover
public import Theory.Representation.BinaryPermutationSixCover
public import Theory.Representation.BinaryAlternatingSixModels
public import Theory.Alternating.proposition_5_2_7_8

/-!
# Two marked A₆ central covers in a homogeneous orbit

Exact inertia gives precisely two seed conjugates. The original projection
is a commutator-generated central cover, hence its entire seed is the
natural four-space or five-dimensional augmentation core. Transport along
the inverse original operator marks the companion using the same A₆
isomorphism and the specified exceptional diagram automorphism. Central
covering kernels are retained throughout.

Source: Aschbacher--Smith I.1.5--6 and14.6.22, pp.408,1038.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
namespace Representation.BinaryOffender.Homogeneous
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {K T : Subgroup D}
    {I : Submodule (ZMod 2) V}

theorem IsIrrPlusWith.alternating_six_conjugates
    (hI : IsIrrPlusWith ρ K T I) (t : T)
    (j : K ≃* alternatingGroup (Fin 6))
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.invariant k v) =
      BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6) (j k) (l v))
    (hnt : I.map (ρ t.val) ≠ I) :
    (∀ s : T, I.map (ρ s.val) = I ∨ I.map (ρ s.val) = I.map (ρ t.val)) ∧
      orbitSpan ρ T I = I ⊔ I.map (ρ t.val) := by
  let N := (subspaceStabilizer ρ I).subgroupOf T
  have hi : N.index = 2 := hI.alternating_six_stabilizer_index ρ j l he ⟨t,hnt⟩
  have htN : t⁻¹ ∉ N := by
    intro hh
    exact hnt ((subspace_map_eq_iff ρ I t.val).mpr
      ((subspaceStabilizer ρ I).inv_mem_iff.mp hh))
  have hall (s : T) : I.map (ρ s.val) = I ∨ I.map (ρ s.val) = I.map (ρ t.val) := by
    by_cases hs : s ∈ N
    · exact Or.inl ((subspace_map_eq_iff ρ I s.val).mpr hs)
    right
    have hh : t⁻¹*s ∈ N := (N.mul_mem_iff_of_index_two hi).mpr (iff_of_false htN hs)
    have hm := congrArg (Submodule.map (ρ t.val))
      ((subspace_map_eq_iff ρ I (t⁻¹*s).val).mpr hh)
    rw [←Submodule.map_comp] at hm
    have hp : (ρ t.val).comp (ρ (t⁻¹*s).val) = ρ s.val := by
      change ρ t.val * ρ (t.val⁻¹*s.val) = ρ s.val
      rw [←map_mul,mul_inv_cancel_left]
    rwa [hp] at hm
  refine ⟨hall,le_antisymm (iSup_le fun s => ?_)
    (sup_le (le_orbitSpan ρ T I) (le_iSup (fun s : T => I.map (ρ s.val)) t))⟩
  rcases hall s with hs | hs
  · rw [hs]; exact le_sup_left
  · rw [hs]; exact le_sup_right

theorem IsIrrPlus.alternating_six_natural_or_core
    [FiniteDimensional (ZMod 2) V]
    (hI : IsIrrPlus ρ K I)
    (j : K ≃* alternatingGroup (Fin 6))
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.choose k v) =
      BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6) (j k) (l v)) :
    BinaryPermutation.SixCover.IsNaturalOrCore (alternatingSixCoverAction ρ K hI j)
      (alternatingGroup (Fin 6)).subtype := by
  let p := alternatingSixCoverProjection ρ K hI j l he
  have hp := alternatingSixCoverProjection_isCover ρ K hI j l he
  have hh := BinaryPermutation.SixCover.naturalOrCore_alternating
    (alternatingSixCoverAction ρ K hI j) (MulEquiv.refl _) ⊤ rfl p.toLinearMap
    (fun g v => LinearMap.congr_fun (p.isIntertwining' g) v) hp.1
    (fun v hv g => hp.2.1 hv g.val) (by
      apply top_unique
      conv_lhs => rw [←hp.2.2]
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g,v⟩,rfl⟩
      exact Submodule.subset_span ⟨g,mem_top g,v,Submodule.mem_top,rfl⟩)
  exact hh

end Representation.BinaryOffender.Homogeneous

namespace BinaryPermutation.SixCover
private theorem diagram_not_natural :
    BinaryAlternatingSix.alternatingDiagramAut ∉ AlternatingSix.ShadowLocal.natural := by
  intro hh
  have hnat : MulAut.conjNormal BinaryAlternatingSix.align ∈ AlternatingSix.ShadowLocal.natural :=
    ⟨BinaryAlternatingSix.align,rfl⟩
  have he : BinaryAlternatingSix.alternatingDiagramAut =
      MulAut.conjNormal BinaryAlternatingSix.align * GLS3.Chapter5.outerAltAut := rfl
  rw [he] at hh
  exact GLS3.Chapter5.outerAltAut_not_mem_natural
    ((AlternatingSix.ShadowLocal.natural.mul_mem_cancel_left hnat).mp hh)

private theorem twist_coordinates
    {X Y : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) X)
    (τ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) Y)
    (E : X ≃ₗ[ZMod 2] Y) (hE : ∀ g v, E (σ g v) = τ g.val (E v))
    (α : MulAut (alternatingGroup (Fin 6)))
    (hα : α ∉ AlternatingSix.ShadowLocal.natural) :
    ∃ F : X ≃ₗ[ZMod 2] Y, ∀ g v,
      F (σ (α g) v) = τ (BinaryAlternatingSix.diagramAut g.val) (F v) := by
  let δ := BinaryAlternatingSix.alternatingDiagramAut
  have hd : δ⁻¹ ∉ AlternatingSix.ShadowLocal.natural := by
    simpa only [inv_mem_iff] using diagram_not_natural
  have hn : α*δ⁻¹ ∈ AlternatingSix.ShadowLocal.natural :=
    (AlternatingSix.ShadowLocal.natural.mul_mem_iff_of_index_two
      GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index).mpr (iff_of_false hα hd)
  obtain ⟨s,hs⟩ := hn
  let u := LinearMap.GeneralLinearGroup.toLinearEquiv (τ.asGroupHom s⁻¹)
  refine ⟨E.trans u,fun g v => ?_⟩
  have hg : (α g).val = s * (δ g).val * s⁻¹ := by
    have hh := congrArg Subtype.val (DFunLike.congr_fun hs (δ g))
    change s*(δ g).val*s⁻¹ = (α (δ.symm (δ g))).val at hh
    simpa only [δ.symm_apply_apply] using hh.symm
  change τ s⁻¹ (E (σ (α g) v)) = τ (δ g).val (τ s⁻¹ (E v))
  rw [hE,hg]
  simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel_left]

theorem IsNaturalOrCore.twist_outer
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) X}
    (hσ : IsNaturalOrCore σ (alternatingGroup (Fin 6)).subtype)
    (α : MulAut (alternatingGroup (Fin 6)))
    (hα : α ∉ AlternatingSix.ShadowLocal.natural) :
    IsNaturalOrCore (σ.comp α.toMonoidHom)
      (BinaryAlternatingSix.diagramAut.toMonoidHom.comp (alternatingGroup (Fin 6)).subtype) := by
  rcases hσ with ⟨E,hE⟩ | ⟨E,hE⟩
  · exact Or.inl (twist_coordinates σ (naturalRepresentation (Fin 6)) E hE α hα)
  · exact Or.inr (twist_coordinates σ (coreRepresentation (Fin 6)) E hE α hα)
end BinaryPermutation.SixCover

namespace Representation.BinaryOffender.Homogeneous
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {K T : Subgroup D}
    {I : Submodule (ZMod 2) V}

/-- The literal conjugate cover has the companion marking under the SAME
component isomorphism; the specified exceptional automorphism is retained. -/
theorem IsIrrPlusWith.alternating_six_companion
    (hI : IsIrrPlusWith ρ K T I) (t : T)
    (j : K ≃* alternatingGroup (Fin 6))
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.invariant k v) =
      BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6) (j k) (l v))
    (hnt : I.map (ρ t.val) ≠ I) :
    BinaryPermutation.SixCover.IsNaturalOrCore
      (alternatingSixCoverAction ρ K (hI.isIrrPlus.map_normalizer ρ (hI.normalizes t.property)) j)
      (BinaryAlternatingSix.diagramAut.toMonoidHom.comp (alternatingGroup (Fin 6)).subtype) := by
  let J := I.map (ρ t.val)
  let hJ := hI.isIrrPlus.map_normalizer ρ (hI.normalizes t.property)
  let σ := alternatingSixCoverAction ρ K hI.isIrrPlus j
  let τ := alternatingSixCoverAction ρ K hJ j
  let c := Submodule.equivMapOfInjective (ρ t.val) (ρ.apply_bijective t.val).1 I
  let r := c.symm
  let α := MulAut.congr j
    (K.normalizerMonoidHom ⟨t.val⁻¹,hI.normalizes (T.inv_mem t.property)⟩)
  have hn : α ∉ AlternatingSix.ShadowLocal.natural := by
    intro hn
    have hm := hI.alternating_six_map_eq_of_natural ρ t⁻¹ j l he hn
    exact hnt ((subspace_map_eq_iff ρ I t.val).mpr
      ((subspaceStabilizer ρ I).inv_mem_iff.mp ((subspace_map_eq_iff ρ I t.val⁻¹).mp hm)))
  have hrval (v : J) : (r v : V) = ρ t.val⁻¹ v.val := by
    apply (ρ.apply_bijective t.val).1
    have hh := congrArg Subtype.val (c.apply_symm_apply v)
    change ρ t.val (r v).val = v.val at hh
    rw [hh]
    simp only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  have hr (g : alternatingGroup (Fin 6)) (v : J) : r (τ g v) = σ (α g) (r v) := by
    apply Subtype.ext
    rw [hrval]
    change ρ t.val⁻¹ (ρ (j.symm g).val v.val) = ρ (j.symm (α g)).val (r v).val
    rw [hrval]
    have hg : (j.symm (α g)).val = t.val⁻¹ * (j.symm g).val * t.val := by
      simp only [α,MulAut.congr_apply,MulEquiv.trans_apply,j.symm_apply_apply,
        normalizerMonoidHom_apply_apply_coe,inv_inv]
    rw [hg]
    simp only [←Module.End.mul_apply,←map_mul,mul_assoc,mul_inv_cancel,mul_one]
  have hm := (IsIrrPlus.alternating_six_natural_or_core ρ hI.isIrrPlus j l he).twist_outer α hn
  rcases hm with ⟨E,hE⟩ | ⟨E,hE⟩
  · refine Or.inl ⟨r.trans E,fun g v => ?_⟩
    change E (r (τ g v)) = _
    rw [hr]
    exact hE g (r v)
  · refine Or.inr ⟨r.trans E,fun g v => ?_⟩
    change E (r (τ g v)) = _
    rw [hr]
    exact hE g (r v)
end Representation.BinaryOffender.Homogeneous
