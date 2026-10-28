module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Involutions.Ranks
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Involutions.Pointwise
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Conjugation and M23 restriction of the involution calculations

Conjugation transports both fixed codimension and the pointwise centralizer
of a fixed space. Restriction along the actual injective point embedding
identifies the M23 fixed spaces and takes pointwise centralizers to preimages.
Thus a native conjugacy witness to the octad representative suffices for
rank four and the centralizer equality, including in M23; the other native
representative gives rank five.

Source: Aschbacher–Smith H.14.4(3) and H.15.2(5), printed pp.397–399.
Involution-class coverage is not a premise hidden in these calculations.
-/

public section

open Sporadic.Mathieu Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

lemma subspaceKernel_fixedSpace_map_conj (ρ : Representation (ZMod 2) G V)
    (A : Subgroup G) (c : G) :
    subspaceKernel ρ (fixedSpace ρ (A.map (MulAut.conj c).toMonoidHom)) ⊤ =
      (subspaceKernel ρ (fixedSpace ρ A) ⊤).map (MulAut.conj c).toMonoidHom := by
  have hf (v : V) (hv : v ∈ fixedSpace ρ A) :
      ρ c v ∈ fixedSpace ρ (A.map (MulAut.conj c).toMonoidHom) := by
    rintro ⟨_, a, ha, rfl⟩
    change ρ (c * a * c⁻¹) (ρ c v) = ρ c v
    have hav : ρ a v = v := hv ⟨a, ha⟩
    simp only [map_mul, Module.End.mul_apply, ρ.inv_self_apply, hav]
  have hb (w : V) (hw : w ∈ fixedSpace ρ (A.map (MulAut.conj c).toMonoidHom)) :
      ρ c⁻¹ w ∈ fixedSpace ρ A := by
    intro a
    change ρ a.val (ρ c⁻¹ w) = ρ c⁻¹ w
    have h := hw ⟨c * a.val * c⁻¹, ⟨a.val, a.property, rfl⟩⟩
    change ρ (c * a.val * c⁻¹) w = w at h
    have h' := congrArg (ρ c⁻¹) h
    simpa only [map_mul, Module.End.mul_apply, ρ.inv_self_apply] using h'
  apply le_antisymm
  · intro g hg
    refine ⟨c⁻¹ * g * c, ⟨Subgroup.mem_top _, ?_⟩, ?_⟩
    · intro v hv
      have h := congrArg (ρ c⁻¹) (hg.2 _ (hf v hv))
      simpa only [map_mul, Module.End.mul_apply, ρ.inv_self_apply] using h
    · change c * (c⁻¹ * g * c) * c⁻¹ = g
      group
  · rintro _ ⟨g, hg, rfl⟩
    refine ⟨Subgroup.mem_top _, ?_⟩
    intro w hw
    change ρ (c * g * c⁻¹) w = w
    simp only [map_mul, Module.End.mul_apply, hg.2 _ (hb w hw), ρ.self_inv_apply]

lemma fixedCodim_zpowers_isConj [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {a b : G} (h : IsConj a b) :
    fixedCodim ρ (Subgroup.zpowers b) = fixedCodim ρ (Subgroup.zpowers a) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc, fixedCodim_zpowers_conj]

lemma subspaceKernel_fixedSpace_zpowers_isConj (ρ : Representation (ZMod 2) G V)
    {a b : G} (h : IsConj a b)
    (ha : subspaceKernel ρ (fixedSpace ρ (Subgroup.zpowers a)) ⊤ = Subgroup.zpowers a) :
    subspaceKernel ρ (fixedSpace ρ (Subgroup.zpowers b)) ⊤ = Subgroup.zpowers b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hm := (MulAut.conj c).toMonoidHom.map_zpowers a
  change (Subgroup.zpowers a).map (MulAut.conj c).toMonoidHom =
    Subgroup.zpowers (c * a * c⁻¹) at hm
  rw [← hc, ← hm, subspaceKernel_fixedSpace_map_conj, ha]

end Representation.BinaryOffender

namespace MathieuCode.CocodeOctad.Involutions
noncomputable section

lemma fixedCodim_of_isConj_z (x : M24) (hx : IsConj z x) :
    fixedCodim cocodeRepresentation (Subgroup.zpowers x) = 4 :=
  (fixedCodim_zpowers_isConj cocodeRepresentation hx).trans fixedCodim_z

lemma fixedCodim_of_isConj_t (x : M24) (hx : IsConj t x) :
    fixedCodim cocodeRepresentation (Subgroup.zpowers x) = 5 :=
  (fixedCodim_zpowers_isConj cocodeRepresentation hx).trans fixedCodim_t

lemma pointwiseCentralizer_of_isConj_z (x : M24) (hx : IsConj z x) :
    subspaceKernel cocodeRepresentation (fixedSpace cocodeRepresentation (Subgroup.zpowers x)) ⊤ =
      Subgroup.zpowers x :=
  subspaceKernel_fixedSpace_zpowers_isConj cocodeRepresentation hx pointwiseCentralizer_z

lemma m23_fixedSpace_zpowers (x : M23) :
    fixedSpace m23CocodeRepresentation (Subgroup.zpowers x) =
      fixedSpace cocodeRepresentation (Subgroup.zpowers (pointEmbedding x)) := by
  change fixedSpace (cocodeRepresentation.comp pointEmbedding) _ = _
  rw [fixedSpace_comp_map, MonoidHom.map_zpowers]

lemma m23_fixedCodim_zpowers (x : M23) :
    fixedCodim m23CocodeRepresentation (Subgroup.zpowers x) =
      fixedCodim cocodeRepresentation (Subgroup.zpowers (pointEmbedding x)) := by
  unfold fixedCodim
  rw [m23_fixedSpace_zpowers]

lemma m23_subspaceKernel (W : Submodule (ZMod 2) Cocode) :
    subspaceKernel m23CocodeRepresentation W ⊤ =
      (subspaceKernel cocodeRepresentation W ⊤).comap pointEmbedding := by
  ext x
  rfl

lemma m23_fixedCodim_of_isConj_z (x : M23) (hx : IsConj z (pointEmbedding x)) :
    fixedCodim m23CocodeRepresentation (Subgroup.zpowers x) = 4 := by
  rw [m23_fixedCodim_zpowers]
  exact fixedCodim_of_isConj_z _ hx

lemma m23_pointwiseCentralizer_of_isConj_z (x : M23)
    (hx : IsConj z (pointEmbedding x)) :
    subspaceKernel m23CocodeRepresentation
      (fixedSpace m23CocodeRepresentation (Subgroup.zpowers x)) ⊤ = Subgroup.zpowers x := by
  rw [m23_fixedSpace_zpowers, m23_subspaceKernel, pointwiseCentralizer_of_isConj_z _ hx,
    ← MonoidHom.map_zpowers, Subgroup.comap_map_eq_self_of_injective pointEmbedding_injective]

end
end MathieuCode.CocodeOctad.Involutions
