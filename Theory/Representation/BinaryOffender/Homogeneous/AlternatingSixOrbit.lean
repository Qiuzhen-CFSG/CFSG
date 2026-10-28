module
public import Theory.Representation.BinaryOffender.Homogeneous.AlternatingSixPair
public import Theory.Representation.AlternatingSixPairedCovers.Inputs

/-!
# The full actor on a paired A₆ seed orbit

When a normal A₆ component and its normalizing actor generate the group,
the two homogeneous seed conjugates are permuted by the whole group.
Their literal subspaces in the orbit carry the natural and diagram-twisted
natural-or-core markings. They span the orbit even when their fixed
kernels overlap. The actual component embedding is retained.

Source: Aschbacher--Smith14.6.22, printed p.1038.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped Pointwise
namespace Representation.BinaryOffender.Homogeneous
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {K T : Subgroup D}
    {I : Submodule (ZMod 2) V}

private theorem naturalOrCore_pullback
    {H X Y : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) H X) (τ : Representation (ZMod 2) H Y)
    (f : H →* Equiv.Perm (Fin 6)) (u : X ≃ₗ[ZMod 2] Y)
    (hu : ∀ g v, u (σ g v) = τ g (u v))
    (hm : BinaryPermutation.SixCover.IsNaturalOrCore τ f) :
    BinaryPermutation.SixCover.IsNaturalOrCore σ f := by
  rcases hm with ⟨E,hE⟩ | ⟨E,hE⟩
  · exact Or.inl ⟨u.trans E,fun g v => by
      change E (u (σ g v)) = _
      rw [hu,hE]; rfl⟩
  · exact Or.inr ⟨u.trans E,fun g v => by
      change E (u (σ g v)) = _
      rw [hu,hE]; rfl⟩

/-- The actual pair orbit carries both model coordinates and the full
ambient action; only the group's normal component and generation are inputs. -/
theorem IsIrrPlusWith.alternating_six_pair_data
    [K.Normal] (hcent : centralizer (K : Set D) = ⊥) (hgen : K ⊔ T = ⊤)
    (hI : IsIrrPlusWith ρ K T I) (t : T)
    (j : K ≃* alternatingGroup (Fin 6))
    (l : centralQuotient ρ K I ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (he : ∀ k v, l (centralQuotientRepresentation ρ K I hI.invariant k v) =
      BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6) (j k) (l v))
    (hnt : I.map (ρ t.val) ≠ I) :
    ∃ (W : Subrepresentation ρ) (C : AlternatingSixPairedCovers.Data W.toRepresentation),
      W.toSubmodule = I ⊔ I.map (ρ t.val) ∧
      W.toSubmodule = orbitSpan ρ T I ∧
      C.component = K.subtype.comp j.symm.toMonoidHom ∧
      C.component.range = K ∧
      (∀ s : D, I.map (ρ s) = I ∨ I.map (ρ s) = I.map (ρ t.val)) := by
  let J := I.map (ρ t.val)
  let O := orbitSpan ρ T I
  have hO : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ O := by
    rw [←hgen]
    exact sup_le (orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus)
      (orbitSpan_invariant ρ T I)
  let W : Subrepresentation ρ := ⟨O,fun g v hv => (hO (mem_top g) v).2 hv⟩
  have hJ := hI.isIrrPlus.map_normalizer ρ (hI.normalizes t.property)
  obtain ⟨hp,hspan⟩ := hI.alternating_six_conjugates ρ t j l he hnt
  have hfull (s : D) : I.map (ρ s) = I ∨ I.map (ρ s) = J := by
    have hs : s ∈ (K : Set D) * (T : Set D) := by
      rw [←coe_mul_of_right_le_normalizer_left K T hI.normalizes,hgen]
      trivial
    obtain ⟨k,hk,x,hx,rfl⟩ := hs
    have hm : (ρ k).comp (ρ x) = ρ (k*x) := (ρ.map_mul _ _).symm
    rw [←hm,Submodule.map_comp]
    rcases hp ⟨x,hx⟩ with hx | hx
    · rw [hx]
      exact Or.inl ((subspace_map_eq_iff ρ I k).mpr (hI.invariant hk))
    · rw [hx]
      exact Or.inr ((subspace_map_eq_iff ρ J k).mpr (hJ.choose hk))
  have hperm (s : D) :
      (I.map (ρ s) = I ∧ J.map (ρ s) = J) ∨
      (I.map (ρ s) = J ∧ J.map (ρ s) = I) := by
    have hb : J.map (ρ s) = I ∨ J.map (ρ s) = J := by
      have hh := hfull (s*t.val)
      change (I.map (ρ t.val)).map (ρ s) = I ∨ (I.map (ρ t.val)).map (ρ s) = J
      rw [←Submodule.map_comp]
      simpa only [←Module.End.mul_eq_comp,←map_mul] using hh
    rcases hfull s with ha | ha <;> rcases hb with hb | hb
    · have hIJ : I = J := Submodule.map_injective_of_injective (ρ.apply_bijective s).1 (ha.trans hb.symm)
      exact Or.inl ⟨ha,hb.trans hIJ⟩
    · exact Or.inl ⟨ha,hb⟩
    · exact Or.inr ⟨ha,hb⟩
    · have hIJ : I = J := Submodule.map_injective_of_injective (ρ.apply_bijective s).1 (ha.trans hb.symm)
      exact Or.inr ⟨ha,hb.trans hIJ.symm⟩
  let κ := K.subtype.comp j.symm.toMonoidHom
  have hκ : κ.range = K := by
    ext x
    constructor
    · rintro ⟨g,rfl⟩
      exact (j.symm g).property
    · intro hx
      exact ⟨j ⟨x,hx⟩,congrArg Subtype.val (j.symm_apply_apply ⟨x,hx⟩)⟩
  let R : Subrepresentation (W.toRepresentation.comp κ) := {
    toSubmodule := I.comap O.subtype
    apply_mem_toSubmodule := fun g v hv => (hI.invariant (j.symm g).property v.val).2 hv }
  let R' : Subrepresentation (W.toRepresentation.comp κ) := {
    toSubmodule := J.comap O.subtype
    apply_mem_toSubmodule := fun g v hv => (hJ.choose (j.symm g).property v.val).2 hv }
  have hIO : I ≤ O := le_orbitSpan ρ T I
  have hJO : J ≤ O := le_iSup (fun s : T => I.map (ρ s.val)) t
  let u : R.toSubmodule ≃ₗ[ZMod 2] I := Submodule.comapSubtypeEquivOfLe hIO
  let u' : R'.toSubmodule ≃ₗ[ZMod 2] J := Submodule.comapSubtypeEquivOfLe hJO
  have hm := IsIrrPlus.alternating_six_natural_or_core ρ hI.isIrrPlus j l he
  have hm' := hI.alternating_six_companion ρ t j l he hnt
  have hsum : R.toSubmodule ⊔ R'.toSubmodule = ⊤ := by
    apply top_unique
    intro v _
    have hv : v.val ∈ I ⊔ J := hspan ▸ v.property
    obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hv
    apply Submodule.mem_sup.mpr
    exact ⟨⟨x,hIO hx⟩,hx,⟨y,hJO hy⟩,hy,Subtype.ext hxy⟩
  let C : AlternatingSixPairedCovers.Data W.toRepresentation := {
    component := κ
    injective := K.subtype_injective.comp j.symm.injective
    normal := hκ.symm ▸ (inferInstance : K.Normal)
    centralizer := hκ.symm ▸ hcent
    first := R
    second := R'
    first_model := naturalOrCore_pullback R.toRepresentation _ _ u (fun _ _ => rfl) hm
    second_model := naturalOrCore_pullback R'.toRepresentation _ _ u' (fun _ _ => rfl) hm'
    span := by rw [hsum,top_sup_eq]
    permutes := by
      intro s
      have hp (P Q : Submodule (ZMod 2) V) (hh : P.map (ρ s) = Q)
          (v : W.toSubmodule) (hv : v.val ∈ P) : (W.toRepresentation s v).val ∈ Q :=
        hh ▸ (show ρ s v.val ∈ P.map (ρ s) from ⟨v.val,hv,rfl⟩)
      rcases hperm s with ⟨hi,hj⟩ | ⟨hi,hj⟩
      · exact Or.inl ⟨hp I I hi,hp J J hj⟩
      · exact Or.inr ⟨hp I J hi,hp J I hj⟩ }
  exact ⟨W,C,hspan,rfl,rfl,hκ,hfull⟩
end Representation.BinaryOffender.Homogeneous
