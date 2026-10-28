module
public import Theory.Representation.BinarySymmetricThreeSeed
public import Theory.Representation.BinarySylowSeedSupplement
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.Embedded
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.SymmetricThreeSeparation

/-!
# The literal support action of a proper symmetric-three seed

The embedded factor is a normal faithful S₃ in its support action image.
Its full movement and the original Sylow-fixed seed pass through the exact
support action map. A proper seed therefore forces a four-subgroup; in
dimension four the support image is S₃ × C₂ or S₃ × S₃.

Source: Aschbacher--Smith 15.1.2, printed p.1085.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.RatioDecomposition.Factor
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (F : Factor ρ)

omit [Finite G] in
private theorem actor_le_stabilizer : F.actor ≤ subspaceStabilizer ρ F.space := by
  apply le_subspaceStabilizer
  rintro g ⟨a,rfl⟩ w ⟨v,rfl⟩
  exact ⟨F.action a v,F.embedding.equivariant a v⟩

omit [Finite G] in
private theorem support_image_data
    (hN : subspaceStabilizer ρ F.space ≤ normalizer (F.actor : Set G)) :
    ∃ (k : F.Carrier →* subspaceActionImage ρ F.space)
      (J : F.Space ≃ₗ[ZMod 2] F.space),
      Function.Injective k ∧
      (∀ g w, J (F.action g w) = subspaceImageRepresentation ρ F.space (k g) (J w)) ∧
      k.range = restrictedSubgroup ρ F.space F.actor ∧ k.range.Normal ∧
      subspaceCommutator (subspaceImageRepresentation ρ F.space) ⊤ k.range = ⊤ := by
  let W := F.space
  let L := subspaceStabilizer ρ W
  let A := subspaceActionImage ρ W
  let q := subspaceActionHom ρ W
  let σ := subspaceImageRepresentation ρ W
  let R := F.actor.subgroupOf L
  let H := R.map q
  let : R.Normal := normal_subgroupOf_of_le_normalizer hN
  let : H.Normal := (inferInstance : R.Normal).map q
    (stabilizerRepresentation ρ W).asGroupHom.rangeRestrict_surjective
  let k : F.Carrier →* A := (subgroupActionHom ρ W F.actor F.actor_le_stabilizer).comp
    F.embedding.groupMap.rangeRestrict
  have hkeq (g : F.Carrier) (w : F.Space) :
      (σ (k g) ⟨F.embedding.spaceMap w,⟨w,rfl⟩⟩ : V) = F.embedding.spaceMap (F.action g w) :=
    (F.embedding.equivariant g w).symm
  have hk : Function.Injective k := by
    intro a b hab
    apply F.faithful
    ext w
    apply F.embedding.space_injective
    exact (hkeq a w).symm.trans
      ((congrArg (fun g => (σ g ⟨F.embedding.spaceMap w,⟨w,rfl⟩⟩ : V)) hab).trans (hkeq b w))
  have hkr : k.range = H := by
    ext x
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨⟨F.embedding.groupMap g,F.actor_le_stabilizer ⟨g,rfl⟩⟩,⟨g,rfl⟩,rfl⟩
    · rintro ⟨g,hg,rfl⟩
      obtain ⟨a,ha⟩ := hg
      refine ⟨a,?_⟩
      change q ⟨F.embedding.groupMap a,_⟩ = q g
      exact congrArg q (Subtype.ext ha)
  let J : F.Space ≃ₗ[ZMod 2] W := LinearEquiv.ofInjective F.embedding.spaceMap F.embedding.space_injective
  let : FiniteDimensional (ZMod 2) W := Module.Finite.of_surjective J.toLinearMap J.surjective
  have hJ (g : F.Carrier) (w : F.Space) : J (F.action g w) = σ (k g) (J w) := by
    apply Subtype.ext
    exact (hkeq g w).symm
  have hfull : subspaceCommutator σ ⊤ H = ⊤ := by
    have hh := subspaceCommutator_map_embedding F.action σ k J.symm.toLinearMap
      (fun g w => by
        apply J.injective
        rw [hJ]
        change (σ (k g)) (J (J.symm w)) = J (J.symm ((σ (k g)) w))
        rw [J.apply_symm_apply,J.apply_symm_apply]) ⊤ ⊤
    rw [Submodule.map_top,LinearEquiv.range,F.full,←MonoidHom.range_eq_map,hkr] at hh
    apply (Submodule.map_injective_of_injective J.symm.injective)
    rw [Submodule.map_top,LinearEquiv.range]
    exact hh.symm
  refine ⟨k,J,hk,hJ,hkr,?_,?_⟩
  · rw [hkr]
    infer_instance
  · rw [hkr]
    exact hfull

/-- Proper generation by the original Sylow-fixed seed forces a four-subgroup
in the literal support action image. -/
theorem symmetricThree_proper_sylow_seed_four_dvd
    (e : F.Carrier ≃* Equiv.Perm (Fin 3))
    (hN : subspaceStabilizer ρ F.space ≤ normalizer (F.actor : Set G))
    (S : Sylow 2 (subspaceStabilizer ρ F.space))
    (hproper : Homogeneous.orbitSpan ρ F.actor
      (fixedSpace ρ ((S : Subgroup (subspaceStabilizer ρ F.space)).map
        (subspaceStabilizer ρ F.space).subtype) ⊓ F.space) < F.space) :
    4 ∣ Nat.card (subspaceActionImage ρ F.space) := by
  obtain ⟨k,J,hk,hJ,hkr,hn,hfull⟩ := F.support_image_data hN
  let W := F.space
  let L := subspaceStabilizer ρ W
  let A := subspaceActionImage ρ W
  let q := subspaceActionHom ρ W
  let σ := subspaceImageRepresentation ρ W
  let R := F.actor.subgroupOf L
  let H := k.range
  let : H.Normal := hn
  let : FiniteDimensional (ZMod 2) W := Module.Finite.of_surjective J.toLinearMap J.surjective
  let j : H ≃* Equiv.Perm (Fin 3) := (MonoidHom.ofInjective hk).symm.trans e
  let P : Sylow 2 A := S.mapSurjective (f := q)
    (stabilizerRepresentation ρ W).asGroupHom.rangeRestrict_surjective
  have hfixed : (fixedSpace σ (P : Subgroup A)).map W.subtype =
      fixedSpace ρ ((S : Subgroup L).map L.subtype) ⊓ W := by
    change (fixedSpace σ ((S : Subgroup L).map q)).map W.subtype = _
    rw [←fixedSpace_comp_map]
    have he : fixedSpace (σ.comp q) (S : Subgroup L) =
        (fixedSpace ρ ((S : Subgroup L).map L.subtype)).comap W.subtype := by
      ext w
      constructor
      · intro hw
        rintro ⟨g,x,hx,rfl⟩
        exact congrArg (fun w : W => (w : V)) (hw ⟨x,hx⟩)
      · intro hw x
        apply Subtype.ext
        exact hw ⟨x,mem_map_of_mem L.subtype x.property⟩
    rw [he,Submodule.map_comap_subtype,inf_comm]
  have horbit : (Homogeneous.orbitSpan σ H (fixedSpace σ (P : Subgroup A))).map W.subtype =
      Homogeneous.orbitSpan ρ F.actor
        (fixedSpace ρ ((S : Subgroup L).map L.subtype) ⊓ W) := by
    have he := Homogeneous.orbitSpan_map_equivariant (σ.comp q) σ q (LinearMap.id)
      (fun _ _ => rfl) R (fixedSpace σ (P : Subgroup A))
    simp only [Submodule.map_id] at he
    change (Homogeneous.orbitSpan σ k.range (fixedSpace σ (P : Subgroup A))).map W.subtype = _
    rw [hkr]
    change (Homogeneous.orbitSpan σ (R.map q) (fixedSpace σ (P : Subgroup A))).map W.subtype = _
    rw [←he]
    have hf := Homogeneous.orbitSpan_map_equivariant (σ.comp q) ρ L.subtype W.subtype
      (fun _ _ => rfl) R (fixedSpace σ (P : Subgroup A))
    rw [map_subgroupOf_eq_of_le F.actor_le_stabilizer,hfixed] at hf
    exact hf
  apply Representation.BinarySymmetricThreeSeed.proper_fixed_sylow_seed_four_dvd σ H j hfull P
  intro hh
  rw [hh,Submodule.map_top,Submodule.range_subtype] at horbit
  exact hproper.ne horbit.symm

/-- The two literal support-image possibilities follow from a proper Sylow-fixed seed,
without assuming a four-subgroup in advance. -/
theorem symmetricThree_proper_sylow_seed_cases
    (hdim : Module.finrank (ZMod 2) F.Space = 4)
    (e : F.Carrier ≃* Equiv.Perm (Fin 3))
    (hN : subspaceStabilizer ρ F.space ≤ normalizer (F.actor : Set G))
    (S : Sylow 2 (subspaceStabilizer ρ F.space))
    (hproper : Homogeneous.orbitSpan ρ F.actor
      (fixedSpace ρ ((S : Subgroup (subspaceStabilizer ρ F.space)).map
        (subspaceStabilizer ρ F.space).subtype) ⊓ F.space) < F.space) :
    Nonempty (subspaceActionImage ρ F.space ≃*
      (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2))) ∨
    Nonempty (subspaceActionImage ρ F.space ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  obtain ⟨k,J,hk,hJ,hkr,hn,hfull⟩ := F.support_image_data hN
  let A := subspaceActionImage ρ F.space
  let σ := subspaceImageRepresentation ρ F.space
  let H := k.range
  let : H.Normal := hn
  let : FiniteDimensional (ZMod 2) F.space :=
    Module.Finite.of_surjective J.toLinearMap J.surjective
  let j : H ≃* Equiv.Perm (Fin 3) := (MonoidHom.ofInjective hk).symm.trans e
  have h4 : Module.finrank (ZMod 2) F.space = 4 := J.finrank_eq.symm.trans hdim
  have hfree : ∀ v, σ (j.symm InvertedCubicTensor.cubic : A) v = v → v = 0 := by
    let f := H.subtype.comp j.symm.toMonoidHom
    have hmap : (⊤ : Subgroup (Equiv.Perm (Fin 3))).map f = H := by
      rw [show f = H.subtype.comp j.symm.toMonoidHom from rfl,←map_map,
        map_top_of_surjective _ j.symm.surjective,←MonoidHom.range_eq_map,H.range_subtype]
    apply Representation.BinarySymmetricThreeNormalizer.fixedFree_of_full (σ.comp f)
    rw [subspaceCommutator_comp_map,hmap]
    exact hfull
  exact Representation.BinarySymmetricThreeNormalizer.normal_symmetricThree_cases σ
    (subspaceImageRepresentation_injective ρ F.space) h4 H j hfree
    (F.symmetricThree_proper_sylow_seed_four_dvd e hN S hproper)

/-- In the small support image the whole support stabilizer and the factor actor
have the same orbit span of the literal Sylow-fixed seed. -/
theorem symmetricThree_small_image_sylow_seed_eq
    (e : F.Carrier ≃* Equiv.Perm (Fin 3))
    (hN : subspaceStabilizer ρ F.space ≤ normalizer (F.actor : Set G))
    (esmall : subspaceActionImage ρ F.space ≃*
      (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)))
    (S : Sylow 2 (subspaceStabilizer ρ F.space)) :
    Homogeneous.orbitSpan ρ (subspaceStabilizer ρ F.space)
      (fixedSpace ρ ((S : Subgroup (subspaceStabilizer ρ F.space)).map
        (subspaceStabilizer ρ F.space).subtype) ⊓ F.space) =
    Homogeneous.orbitSpan ρ F.actor
      (fixedSpace ρ ((S : Subgroup (subspaceStabilizer ρ F.space)).map
        (subspaceStabilizer ρ F.space).subtype) ⊓ F.space) := by
  obtain ⟨k,J,hk,hJ,hkr,hn,hfull⟩ := F.support_image_data hN
  let W := F.space
  let L := subspaceStabilizer ρ W
  let A := subspaceActionImage ρ W
  let q := subspaceActionHom ρ W
  let σ := subspaceImageRepresentation ρ W
  let R := F.actor.subgroupOf L
  let H := k.range
  let : H.Normal := hn
  let j : H ≃* Equiv.Perm (Fin 3) := (MonoidHom.ofInjective hk).symm.trans e
  let P : Sylow 2 A := S.mapSurjective (f := q)
    (stabilizerRepresentation ρ W).asGroupHom.rangeRestrict_surjective
  let I := fixedSpace σ (P : Subgroup A)
  have hfixed : I.map W.subtype =
      fixedSpace ρ ((S : Subgroup L).map L.subtype) ⊓ W := by
    change (fixedSpace σ ((S : Subgroup L).map q)).map W.subtype = _
    rw [←fixedSpace_comp_map]
    have he : fixedSpace (σ.comp q) (S : Subgroup L) =
        (fixedSpace ρ ((S : Subgroup L).map L.subtype)).comap W.subtype := by
      ext w
      constructor
      · intro hw
        rintro ⟨g,x,hx,rfl⟩
        exact congrArg (fun w : W => (w : V)) (hw ⟨x,hx⟩)
      · intro hw x
        apply Subtype.ext
        exact hw ⟨x,mem_map_of_mem L.subtype x.property⟩
    rw [he,Submodule.map_comap_subtype,inf_comm]
  have horbit (T : Subgroup L) :
      (Homogeneous.orbitSpan σ (T.map q) I).map W.subtype =
        Homogeneous.orbitSpan ρ (T.map L.subtype) (I.map W.subtype) := by
    have he := Homogeneous.orbitSpan_map_equivariant (σ.comp q) σ q
      (LinearMap.id) (fun _ _ => rfl) T I
    simp only [Submodule.map_id] at he
    rw [←he]
    exact Homogeneous.orbitSpan_map_equivariant (σ.comp q) ρ L.subtype
      W.subtype (fun _ _ => rfl) T I
  have htop := horbit ⊤
  rw [map_top_of_surjective q (stabilizerRepresentation ρ W).asGroupHom.rangeRestrict_surjective,
    ←MonoidHom.range_eq_map,L.range_subtype,hfixed] at htop
  have hactor := horbit R
  have hh : R.map q = H := hkr.symm
  rw [hh,map_subgroupOf_eq_of_le F.actor_le_stabilizer,hfixed] at hactor
  have he := congrArg (Submodule.map W.subtype)
    (Representation.BinarySylowSeedSupplement.small_symmetricThree_seed_eq σ H j esmall P)
  exact htop.symm.trans (he.trans hactor)

end CFSG.Quasithin.ChapterD.RatioDecomposition.Factor

namespace CFSG.Quasithin.ChapterD.RatioDecomposition.FactorData
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G} {U : Submodule (ZMod 2) V}
  (c : FactorData ρ K U) (d : Decomposition c.representation)

/-- The literal support permutation makes its stabilizer normalize the marked actor. -/
theorem support_stabilizer_normalizes_actor (π : G →* Equiv.Perm d.Index)
    (hp : ∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g i)).actor)
    (hs : ∀ g i, (c.ambientFactor d i).space.map (ρ g) =
      (c.ambientFactor d (π g i)).space) (i : d.Index) :
    subspaceStabilizer ρ (c.ambientFactor d i).space ≤
      normalizer ((c.ambientFactor d i).actor : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  have hi := c.support_stabilizer_fixes_index d π hs i hg
  have he := hp g i
  rw [hi] at he
  have hh := mem_map_of_mem (MulAut.conj g).toMonoidHom hx
  rw [he] at hh
  exact hh
end CFSG.Quasithin.ChapterD.RatioDecomposition.FactorData
