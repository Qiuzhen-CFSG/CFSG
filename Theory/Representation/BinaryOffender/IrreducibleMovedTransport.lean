module

public import Theory.Representation.BinaryOffender.MovedSpaceTransport

/-!
# Transport of irreducible sections

An Irr⁺ member is characterized by full commutator generation, noncentrality,
and minimality among invariant subspaces not contained in the fixed space.
The converse is proved on the literal quotient by the central subspace.
This criterion transports through an injective linear intertwiner and a
surjection of acting groups. In particular it applies to conjugation by a
normalizer element and to the actual faithful action image on a containing
invariant subspace.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.40 and the moved-space reduction in B.7.2, printed pp. 31 and 119
(1 March 2004 manuscript).
-/

@[expose] public section

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Every proper invariant subspace of an Irr⁺ member is centralized. -/
theorem IsIrrPlus.eq_or_le_fixedSpace {X : Subgroup G} {I J : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ X I) (hJ : X ≤ subspaceStabilizer ρ J) (hJI : J ≤ I) :
    J = I ∨ J ≤ fixedSpace ρ X := by
  rcases hI.le_or_inf_sup_fixedSpace_le ρ hJ with h | h
  · exact Or.inl (le_antisymm hJI h)
  · exact Or.inr (fun v hv => h ⟨hJI hv, Submodule.mem_sup_left hv⟩)

set_option backward.isDefEq.respectTransparency false in
/-- Noncentral invariant minimality gives the actual irreducible central quotient. -/
theorem isIrrPlus_of_minimal {X : Subgroup G} {I : Submodule (ZMod 2) V}
    (hs : X ≤ subspaceStabilizer ρ I) (hc : subspaceCommutator ρ I X = I)
    (hn : ¬ I ≤ fixedSpace ρ X)
    (hmin : ∀ J : Submodule (ZMod 2) V, X ≤ subspaceStabilizer ρ J → J ≤ I →
      J = I ∨ J ≤ fixedSpace ρ X) : IsIrrPlus ρ X I := by
  refine ⟨hs, hc, ?_⟩
  let C := centralSubspace ρ X I hs
  have hC : C.toSubmodule ≠ ⊤ := by
    intro he
    apply hn
    intro i hi
    exact (show (⟨i, hi⟩ : I) ∈ C.toSubmodule from he.symm ▸ Submodule.mem_top)
  let : Nontrivial (I ⧸ C.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hC
  change IsIrreducible C.quotientRepresentation
  refine ⟨?_⟩
  intro S
  let J := (S.toSubmodule.comap C.toSubmodule.mkQ).map I.subtype
  have hJI : J ≤ I := Submodule.map_subtype_le _ _
  have hJs : X ≤ subspaceStabilizer ρ J := by
    apply le_subspaceStabilizer
    rintro x hx _ ⟨i, hi, rfl⟩
    refine ⟨(invariantSubspace ρ X I hs).toRepresentation ⟨x, hx⟩ i, ?_, rfl⟩
    exact S.apply_mem_toSubmodule ⟨x, hx⟩ hi
  rcases hmin J hJs hJI with he | hfix
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro q _
    obtain ⟨i, rfl⟩ := C.toSubmodule.mkQ_surjective q
    obtain ⟨j, hj, heji⟩ := (show (i : V) ∈ J from he.symm ▸ i.property)
    have hji : j = i := Subtype.ext heji
    exact hji ▸ hj
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_bot_iff.mp
    intro q hq
    obtain ⟨i, rfl⟩ := C.toSubmodule.mkQ_surjective q
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hfix ⟨i, hq, rfl⟩)

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  (σ : Representation (ZMod 2) H U)

/-- Transport through a surjection of acting groups and an injective intertwining linear map. -/
theorem IsIrrPlus.of_intertwining {X : Subgroup G} {Y : Subgroup H}
    {I : Submodule (ZMod 2) V} {J : Submodule (ZMod 2) U}
    (hI : IsIrrPlus ρ X I) (f : X →* Y) (hf : Function.Surjective f)
    (e : U →ₗ[ZMod 2] V) (he : Function.Injective e)
    (hequiv : ∀ x : X, ∀ u : U, e (σ (f x) u) = ρ x (e u))
    (hJI : J.map e = I) : IsIrrPlus σ Y J := by
  have hmem (u : U) : e u ∈ I ↔ u ∈ J := by
    rw [← hJI]
    exact ⟨fun ⟨v, hv, hve⟩ => he hve ▸ hv, fun hu => ⟨u, hu, rfl⟩⟩
  have hs : Y ≤ subspaceStabilizer σ J := by
    apply le_subspaceStabilizer
    intro y hy u hu
    obtain ⟨x, hx⟩ := hf ⟨y, hy⟩
    apply (hmem _).mp
    have hv : e (σ (f x) u) ∈ I := by
      rw [hequiv]
      exact (hI.choose x.property _).2 ((hmem u).mpr hu)
    simpa only [hx] using hv
  have hc : (subspaceCommutator σ J Y).map e = subspaceCommutator ρ I X := by
    apply le_antisymm
    · apply Submodule.map_le_iff_le_comap.mpr
      apply Submodule.span_le.mpr
      rintro _ ⟨y, hy, u, hu, rfl⟩
      obtain ⟨x, hx⟩ := hf ⟨y, hy⟩
      change e (σ y u - u) ∈ subspaceCommutator ρ I X
      have hv : e (σ y u) = ρ x (e u) := by simpa only [hx] using hequiv x u
      rw [map_sub, hv]
      exact Submodule.subset_span ⟨x, x.property, e u, (hmem u).mpr hu, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨x, hx, v, hv, rfl⟩
      obtain ⟨u, hu, rfl⟩ := (show v ∈ J.map e from hJI.symm ▸ hv)
      refine ⟨σ (f ⟨x, hx⟩) u - u,
        Submodule.subset_span ⟨f ⟨x, hx⟩, (f ⟨x, hx⟩).property, u, hu, rfl⟩, ?_⟩
      rw [map_sub, hequiv]
  apply isIrrPlus_of_minimal σ hs
  · apply Submodule.map_injective_of_injective he
    rw [hc, hJI, hI.choose_spec.1]
  · intro hfix
    apply hI.not_le_fixedSpace ρ
    intro v hv x
    obtain ⟨u, hu, rfl⟩ := (show v ∈ J.map e from hJI.symm ▸ hv)
    change ρ x (e u) = e u
    rw [← hequiv]
    exact congrArg e (hfix hu (f x))
  · intro K hKs hKJ
    have hKe : X ≤ subspaceStabilizer ρ (K.map e) := by
      apply le_subspaceStabilizer
      rintro x hx _ ⟨u, hu, rfl⟩
      exact ⟨σ (f ⟨x, hx⟩) u, (hKs (f ⟨x, hx⟩).property u).2 hu, hequiv ⟨x, hx⟩ u⟩
    have hKI : K.map e ≤ I := hJI ▸ Submodule.map_mono hKJ
    rcases hI.eq_or_le_fixedSpace ρ hKe hKI with heq | hfix
    · exact Or.inl (Submodule.map_injective_of_injective he (heq.trans hJI.symm))
    · right
      intro u hu y
      obtain ⟨x, rfl⟩ := hf y
      apply he
      change e (σ (f x) u) = e u
      rw [hequiv]
      exact hfix ⟨u, hu, rfl⟩ x

/-- Conjugation by a normalizer element transports the actual Irr⁺ family. -/
theorem IsIrrPlus.map_normalizer {X : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ X I) {a : G} (ha : a ∈ Subgroup.normalizer X) :
    IsIrrPlus ρ X (I.map (ρ a)) := by
  let f := X.normalizerMonoidHom ⟨a, ha⟩
  have he : Function.Injective (ρ a⁻¹) := by
    apply Function.LeftInverse.injective (g := ρ a)
    intro v
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  apply hI.of_intertwining ρ ρ f.toMonoidHom f.surjective (ρ a⁻¹) he
  · intro x v
    change ρ a⁻¹ (ρ (a * x * a⁻¹) v) = ρ x (ρ a⁻¹ v)
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  · rw [← Submodule.map_comp]
    have heq : (ρ a⁻¹).comp (ρ a) = LinearMap.id := by
      change ρ a⁻¹ * ρ a = 1
      rw [← map_mul, inv_mul_cancel, map_one]
    rw [heq, Submodule.map_id]

/-- Restriction uses the literal preimage inside W and the actual image of X. -/
theorem IsIrrPlus.restricted {X : Subgroup G} {I W : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ X I) (hX : X ≤ subspaceStabilizer ρ W) (hIW : I ≤ W) :
    IsIrrPlus (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W X)
      (I.comap W.subtype) := by
  apply hI.of_intertwining ρ (subspaceImageRepresentation ρ W)
    (restrictedActionSurjection ρ W X hX) (restrictedActionSurjection_surjective ρ W X hX)
    W.subtype W.subtype_injective
  · intro x w
    rfl
  · rw [Submodule.map_comap_subtype, inf_eq_right.mpr hIW]

end Representation.BinaryOffender
