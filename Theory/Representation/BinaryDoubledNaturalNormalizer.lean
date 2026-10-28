module
public import Theory.Representation.SL3DoubledNaturalOffenders.NormalizerCoverage.Factorization
public import Theory.Representation.BinaryDoubledNaturalCentralizer

/-!
# The full binary doubled-natural normalizer

Over F₂ the published field-linear factorization applies to every normalizer
operator. Both invertible matrix factors have determinant one. The resulting
SL₃(2) × SL₂(2) tensor map is injective because the binary natural factor has
trivial center. This gives the full normalizer, its commuting-factor
factorization, and an actual product isomorphism retaining evaluation on every
vector.

The source consumer is the original N_G(U)/U in 12.2.25, once the hyperplane
residual is normal. No identification from group orders is used.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004, B.5.9--10,
printed pp.107--109, and original 12.2.25, printed p.806.
-/

open Matrix Subgroup
namespace Representation.SL3DoubledNaturalOffenders
public noncomputable section

 theorem binary_normalizer_eq_tensorSubgroup :
    normalizer (ZMod 2) = tensorSubgroup (ZMod 2) := by
  apply le_antisymm ?_ (tensorSubgroup_le_normalizer _)
  intro b hb
  obtain ⟨g,c,hgc⟩ := normalizer_linear_tensor_factors b hb
    (fun a v => map_smul (b : Module.End (ZMod 2) (Space (ZMod 2))) a v)
  obtain ⟨g,rfl⟩ := BinaryLinear.OuterCyclic.binary_toGL_surjective 3 g
  obtain ⟨c,rfl⟩ := BinaryLinear.OuterCyclic.binary_toGL_surjective 2 c
  refine ⟨(g,c),?_⟩
  apply Units.ext
  apply LinearMap.ext
  intro v
  funext i
  exact (hgc v i).symm

 theorem binary_tensor_injective :
    Function.Injective (tensorRepresentation (ZMod 2)).asGroupHom := by
  apply (injective_iff_map_eq_one _).mpr
  rintro ⟨g,c⟩ h
  have ht : (tensorRepresentation (ZMod 2)).asGroupHom (g,c) =
      (representation (ZMod 2)).asGroupHom g *
        (multiplicityRepresentation (ZMod 2)).asGroupHom c := by
    apply Units.ext
    rfl
  have he : (representation (ZMod 2)).asGroupHom g =
      ((multiplicityRepresentation (ZMod 2)).asGroupHom c)⁻¹ :=
    eq_inv_of_mul_eq_one_left (ht.symm.trans h)
  have hc : (representation (ZMod 2)).asGroupHom g ∈
      centralizer (component (ZMod 2) : Set (Ambient (ZMod 2))) := by
    rw [he]
    exact (centralizer _).inv_mem (multiplicity_mem_centralizer _ c)
  have hg : g ∈ center (SL (ZMod 2)) := by
    rw [Subgroup.mem_center_iff]
    intro a
    apply representation_injective
    have hh := mem_centralizer_iff.mp hc ((representation (ZMod 2)).asGroupHom a) ⟨a,rfl⟩
    exact congrArg Units.val (by simpa only [← map_mul] using hh)
  rw [BinaryLinear.OuterCyclic.binary_center_eq_bot (by decide : 0 < 3)] at hg
  have hg1 : g = 1 := mem_bot.mp hg
  have hc1 : c = 1 := by
    apply Subtype.ext
    apply multiplicity_injective (ZMod 2)
    have hh := congrArg Units.val h
    change representation (ZMod 2) g * multiplicity (ZMod 2) c.val = 1 at hh
    rw [hg1,map_one,one_mul,←multiplicity_one] at hh
    exact hh
  exact Prod.ext hg1 hc1

 theorem binary_normalizer_eq_sup : normalizer (ZMod 2) =
    component (ZMod 2) ⊔ centralizer (component (ZMod 2) : Set (Ambient (ZMod 2))) := by
  apply le_antisymm
  · rw [binary_normalizer_eq_tensorSubgroup]
    rintro b ⟨⟨g,c⟩,rfl⟩
    have he : (tensorRepresentation (ZMod 2)).asGroupHom (g,c) =
        (representation (ZMod 2)).asGroupHom g *
          (multiplicityRepresentation (ZMod 2)).asGroupHom c := Units.ext rfl
    rw [he]
    exact (component (ZMod 2) ⊔ centralizer (component (ZMod 2) : Set (Ambient (ZMod 2)))).mul_mem
      (mem_sup_left ⟨g,rfl⟩) (mem_sup_right (multiplicity_mem_centralizer _ c))
  · exact sup_le (component _).le_normalizer (centralizer_le_normalizer _)

 def binaryNormalizerEquiv : normalizer (ZMod 2) ≃* (SL (ZMod 2) × MultiplicitySL (ZMod 2)) :=
  (MulEquiv.subgroupCongr binary_normalizer_eq_tensorSubgroup).trans
    (MonoidHom.ofInjective binary_tensor_injective).symm

 theorem binaryNormalizerEquiv_action (b : normalizer (ZMod 2)) (v : Space (ZMod 2)) :
    (b.val : Module.End (ZMod 2) (Space (ZMod 2))) v =
      tensorRepresentation (ZMod 2) (binaryNormalizerEquiv b) v := by
  have hh := (MonoidHom.ofInjective binary_tensor_injective).apply_symm_apply
    ((MulEquiv.subgroupCongr binary_normalizer_eq_tensorSubgroup) b)
  exact (LinearMap.congr_fun (congrArg (fun x : tensorSubgroup (ZMod 2) =>
    (x.val : Module.End (ZMod 2) (Space (ZMod 2)))) hh) v).symm
end
end Representation.SL3DoubledNaturalOffenders
