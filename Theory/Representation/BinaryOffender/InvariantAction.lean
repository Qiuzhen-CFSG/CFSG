module

public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Action images of globally invariant subspaces

For an invariant subspace, we construct the surjective action map from the
whole group to the actual stabilizer-action image. Its kernel is the pointwise
centralizer, its subgroup images agree with the restricted-action construction,
and its quotient by that kernel is explicitly isomorphic to the image.
Fixed spaces of normal subgroups are invariant, providing the input for the
fixed-space reduction in Aschbacher–Smith, *The Classification of Quasithin
Groups*, B.1.10–11, printed pp. 72–73.
-/

@[expose] public section

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem fixedSpace_stable_of_normal (Q : Subgroup G) [Q.Normal] :
    (⊤ : Subgroup G) ≤ subspaceStabilizer ρ (fixedSpace ρ Q) := by
  apply le_subspaceStabilizer
  intro g _ v hv q
  have hq := hv ⟨g⁻¹ * q * g, by simpa only [inv_inv] using (inferInstance : Q.Normal).conj_mem q q.property g⁻¹⟩
  change ρ q (ρ g v) = ρ g v
  calc
    _ = ρ g (ρ (g⁻¹ * q * g) v) := by
      simp only [map_mul, Module.End.mul_apply]
      simp
    _ = ρ g v := congrArg (ρ g) hq

variable (W : Submodule (ZMod 2) V) (hW : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ W)

def invariantActionHom : G →* subspaceActionImage ρ W :=
  (subspaceActionHom ρ W).comp
    { toFun := fun g => ⟨g, hW (Subgroup.mem_top g)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem invariantActionHom_surjective : Function.Surjective (invariantActionHom ρ W hW) := by
  intro d
  obtain ⟨g, rfl⟩ := (stabilizerRepresentation ρ W).asGroupHom.rangeRestrict_surjective d
  exact ⟨g, rfl⟩

theorem invariantActionHom_apply (g : G) (w : W) :
    (subspaceImageRepresentation ρ W (invariantActionHom ρ W hW g) w : V) = ρ g w := rfl

theorem invariantActionHom_ker :
    (invariantActionHom ρ W hW).ker = subspaceKernel ρ W ⊤ := by
  ext g
  constructor
  · intro hg
    refine ⟨Subgroup.mem_top g, ?_⟩
    intro w hw
    have hh := congrArg (fun d => subspaceImageRepresentation ρ W d ⟨w, hw⟩) hg
    exact congrArg (fun w : W => (w : V)) hh
  · rintro ⟨_, hg⟩
    apply subspaceImageRepresentation_injective ρ W
    ext w
    exact hg w w.property

theorem invariantActionHom_map (L : Subgroup G) :
    L.map (invariantActionHom ρ W hW) = restrictedSubgroup ρ W L := by
  ext d
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hW (Subgroup.mem_top g)⟩, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩

noncomputable def invariantActionQuotientEquiv :
    G ⧸ (invariantActionHom ρ W hW).ker ≃* subspaceActionImage ρ W :=
  QuotientGroup.quotientKerEquivOfSurjective _ (invariantActionHom_surjective ρ W hW)
end Representation.BinaryOffender
