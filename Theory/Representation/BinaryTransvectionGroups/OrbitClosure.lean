module

public import Theory.Representation.BinaryTransvectionGroups.RootForms.Generation

/-!
# Full transvection groups on an orbit span

If the action contains every binary transvection with a specified center, the
normal closure of that root group induces the full linear group on the span of
the center's orbit. Extend a linear form from the orbit span to the original
space, conjugate a root element, and restrict back. Thus all orbit points are
full transvection directions in the action image; they span, so Gaussian
elimination gives the full linear group.

The normal closure is taken in the original acting group. No faithfulness is
needed for this stronger image statement. Finite dimensionality supplies the
finite Gaussian elimination argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma B.4.10, printed p.96.
-/

@[expose] public section

open BinaryLinear BinaryLinear.FourCentralizerOvergroups
open BinaryTransvectionGroups

namespace BinaryTransvectionGroups
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The subspace spanned by the orbit of the original vector. -/
abbrev orbitSpan (ρ : G →* GL V) (u : V) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) (Set.range fun g => ρ g u)

/-- The original action preserves its orbit span. -/
theorem map_mem_orbitSpan (ρ : G →* GL V) (u : V) (g : G)
    {v : V} (hv : v ∈ orbitSpan ρ u) : ρ g v ∈ orbitSpan ρ u := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨h, rfl⟩ := hv
    exact Submodule.subset_span ⟨g * h, by simp⟩
  | zero => simp
  | add x y hx hy hix hiy => simpa using (orbitSpan ρ u).add_mem hix hiy
  | smul a x hx hix => simpa using (orbitSpan ρ u).smul_mem a hix

/-- The literal restriction of the original action to its orbit span. -/
def orbitSpanAction (ρ : G →* GL V) (u : V) : G →* GL (orbitSpan ρ u) where
  toFun g :=
    { toFun := fun v => ⟨ρ g v, map_mem_orbitSpan ρ u g v.property⟩
      invFun := fun v => ⟨ρ g⁻¹ v, map_mem_orbitSpan ρ u g⁻¹ v.property⟩
      left_inv := by intro v; apply Subtype.ext; simp [← LinearEquiv.mul_apply]
      right_inv := by intro v; apply Subtype.ext; simp
      map_add' := by intros; apply Subtype.ext; simp
      map_smul' := by intros; apply Subtype.ext; simp }
  map_one' := by ext v; simp
  map_mul' := by intros; ext v; simp

/-- Normal closure, in the acting group, of the full root group preimage. -/
abbrev rootNormalClosure (ρ : G →* GL V) (u : V) : Subgroup G :=
  Subgroup.normalClosure ((radical (centerLine u)).comap ρ : Set G)

/-- Full root groups induce the full binary linear group on the orbit span. -/
theorem rootNormalClosure_action_eq_top [FiniteDimensional (ZMod 2) V]
    (ρ : G →* GL V) (u : V)
    (hfull : radical (centerLine u) ≤ ρ.range) :
    (rootNormalClosure ρ u).map (orbitSpanAction ρ u) = ⊤ := by
  let U := orbitSpan ρ u
  let K := (rootNormalClosure ρ u).map (orbitSpanAction ρ u)
  have hroot (g : G) (f : V →ₗ[ZMod 2] ZMod 2) (hf : f (ρ g u) = 0) :
      ∃ a ∈ rootNormalClosure ρ u, ρ a = transvection (ρ g u) f hf := by
    let f' := f.comp (ρ g).toLinearMap
    have hf' : f' u = 0 := hf
    have ht : transvection u f' hf' ∈ radical (centerLine u) :=
      transvection_mem (Submodule.mem_span_singleton_self u)
        (Submodule.span_le.mpr (by simpa using hf'))
    obtain ⟨t, htρ⟩ := hfull ht
    have htL : t ∈ rootNormalClosure ρ u :=
      Subgroup.subset_normalClosure (show ρ t ∈ radical (centerLine u) from htρ ▸ ht)
    refine ⟨g * t * g⁻¹, (inferInstance : (rootNormalClosure ρ u).Normal).conj_mem t htL g, ?_⟩
    rw [map_mul, map_mul, htρ, map_inv]
    ext v
    simp [transvection, f']
  have hdir (g : G) :
      (⟨ρ g u, Submodule.subset_span ⟨g, rfl⟩⟩ : U) ∈ directions K := by
    intro f hf
    obtain ⟨F, hF⟩ := f.exists_extend
    have hFv (v : U) : F v = f v := congrArg (fun l : U →ₗ[ZMod 2] ZMod 2 => l v) hF
    have hFu : F (ρ g u) = 0 := (hFv ⟨ρ g u, Submodule.subset_span ⟨g, rfl⟩⟩).trans hf
    obtain ⟨a, ha, he⟩ := hroot g F hFu
    refine ⟨a, ha, ?_⟩
    ext v
    change ρ a v = (v : V) + f v • ρ g u
    rw [he]
    change (v : V) + F v • ρ g u = _
    rw [hFv]
  apply BinaryTransvectionGroups.eq_top_of_directions_eq_top
  apply top_unique
  intro v _
  have hle : U ≤ (directions K).map U.subtype := by
    apply Submodule.span_le.mpr
    rintro x ⟨g, rfl⟩
    exact ⟨⟨ρ g u, Submodule.subset_span ⟨g, rfl⟩⟩, hdir g, rfl⟩
  obtain ⟨w, hw, he⟩ := hle v.property
  exact (Subtype.ext he : w = v) ▸ hw

end BinaryTransvectionGroups
