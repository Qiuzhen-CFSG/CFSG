module

public import Theory.Representation.SymplecticConjugatePair.Ambient.Normalizer.Generators

/-!
# Coordinate restrictions of paired normalizers

The natural image here is the image of the genuine derived matrix group on
one binary natural module. A paired normalizer preserving both coordinates
restricts to an invertible binary operator normalizing that natural image.
The coordinate lemmas use actual linear maps and evaluation, and apply to the
binary field without replacing the derived group by the full symplectic group.

These are the interfaces for the commutant and semilinear calculations in the
normalizer proof for Aschbacher–Smith H.7, printed pp.388–389 of
`refs/quasithin.pdf`.
-/

@[expose] public section
open Representation BinaryOffender Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
namespace SymplecticConjugatePair.Ambient.Normalizer
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

noncomputable def naturalDerivedAction :
    Representation (ZMod 2) (commutator (Sp F)) (Vector F) :=
  (restrictScalars (symplecticNatural 2)).comp (commutator (Sp F)).subtype

noncomputable def naturalDerivedImage : Subgroup (Vector F ≃ₗ[ZMod 2] Vector F) :=
  (linearAction (naturalDerivedAction (F := F))).range

noncomputable def naturalNormalizer : Subgroup (Vector F ≃ₗ[ZMod 2] Vector F) :=
  Subgroup.normalizer (naturalDerivedImage (F := F))

def blockScalar (a b : F) : Space F →ₗ[ZMod 2] Space F where
  toFun v := (a • v.1, b • v.2)
  map_add' v w := by simp [smul_add]
  map_smul' c v := by
    change (a • (c • v.1), b • (c • v.2)) = (c • (a • v.1), c • (b • v.2))
    rw [smul_comm a c, smul_comm b c]

@[simp] lemma blockScalar_apply (a b : F) (v : Space F) :
    blockScalar a b v = (a • v.1, b • v.2) := rfl

lemma blockScalar_commutes (τ : MulAut (Sp F)) (a b : F)
    (g : commutator (Sp F)) (v : Space F) :
    blockScalar a b (derivedPair τ g v) = derivedPair τ g (blockScalar a b v) := by
  change (a • symplecticNatural 2 g.val v.1, b • symplecticNatural 2 (τ g.val) v.2) =
    (symplecticNatural 2 g.val (a • v.1), symplecticNatural 2 (τ g.val) (b • v.2))
  simp only [map_smul]

def PreservesCoordinates (f : Space F ≃ₗ[ZMod 2] Space F) : Prop :=
  (∀ w : Vector F, (f (w, 0)).2 = 0) ∧ (∀ w : Vector F, (f (0, w)).1 = 0)

def firstBlock (f : Space F ≃ₗ[ZMod 2] Space F) : Vector F →ₗ[ZMod 2] Vector F :=
  (LinearMap.fst (ZMod 2) (Vector F) (Vector F)).comp
    (f.toLinearMap.comp (LinearMap.inl (ZMod 2) (Vector F) (Vector F)))

def secondBlock (f : Space F ≃ₗ[ZMod 2] Space F) : Vector F →ₗ[ZMod 2] Vector F :=
  (LinearMap.snd (ZMod 2) (Vector F) (Vector F)).comp
    (f.toLinearMap.comp (LinearMap.inr (ZMod 2) (Vector F) (Vector F)))

@[simp] lemma firstBlock_apply (f : Space F ≃ₗ[ZMod 2] Space F) (w : Vector F) :
    firstBlock f w = (f (w, 0)).1 := rfl
@[simp] lemma secondBlock_apply (f : Space F ≃ₗ[ZMod 2] Space F) (w : Vector F) :
    secondBlock f w = (f (0, w)).2 := rfl

lemma preservesCoordinates_apply (f : Space F ≃ₗ[ZMod 2] Space F)
    (hp : PreservesCoordinates f) (v : Space F) :
    f v = (firstBlock f v.1, secondBlock f v.2) := by
  have hv : v = (v.1, 0) + (0, v.2) := by simp
  conv_lhs => rw [hv, map_add]
  exact Prod.ext (by simpa using hp.2 v.2) (by simpa using hp.1 v.1)

lemma firstBlock_fst (f : Space F ≃ₗ[ZMod 2] Space F)
    (hp : PreservesCoordinates f) (v : Space F) :
    firstBlock f v.1 = (f v).1 := (congrArg Prod.fst (preservesCoordinates_apply f hp v)).symm

lemma secondBlock_snd (f : Space F ≃ₗ[ZMod 2] Space F)
    (hp : PreservesCoordinates f) (v : Space F) :
    secondBlock f v.2 = (f v).2 := (congrArg Prod.snd (preservesCoordinates_apply f hp v)).symm

lemma firstBlock_bijective (f : Space F ≃ₗ[ZMod 2] Space F) (hp : PreservesCoordinates f) :
    Function.Bijective (firstBlock f) := by
  constructor
  · intro u v huv
    have he : f (u, 0) = f (v, 0) := Prod.ext huv ((hp.1 u).trans (hp.1 v).symm)
    exact congrArg Prod.fst (f.injective he)
  · intro w
    refine ⟨(f.symm (w, 0)).1, ?_⟩
    rw [firstBlock_fst f hp, LinearEquiv.apply_symm_apply]

lemma secondBlock_bijective (f : Space F ≃ₗ[ZMod 2] Space F) (hp : PreservesCoordinates f) :
    Function.Bijective (secondBlock f) := by
  constructor
  · intro u v huv
    have he : f (0, u) = f (0, v) := Prod.ext ((hp.2 u).trans (hp.2 v).symm) huv
    exact congrArg Prod.snd (f.injective he)
  · intro w
    refine ⟨(f.symm (0, w)).2, ?_⟩
    rw [secondBlock_snd f hp, LinearEquiv.apply_symm_apply]

noncomputable def firstBlockEquiv (f : Space F ≃ₗ[ZMod 2] Space F) (hp : PreservesCoordinates f) :
    Vector F ≃ₗ[ZMod 2] Vector F :=
  LinearEquiv.ofBijective (firstBlock f) (firstBlock_bijective f hp)

noncomputable def secondBlockEquiv (f : Space F ≃ₗ[ZMod 2] Space F) (hp : PreservesCoordinates f) :
    Vector F ≃ₗ[ZMod 2] Vector F :=
  LinearEquiv.ofBijective (secondBlock f) (secondBlock_bijective f hp)

lemma preservesCoordinates_symm (f : Space F ≃ₗ[ZMod 2] Space F) (hp : PreservesCoordinates f) :
    PreservesCoordinates f.symm := by
  constructor
  · intro w
    apply (secondBlock_bijective f hp).1
    rw [secondBlock_snd f hp, LinearEquiv.apply_symm_apply, map_zero]
  · intro w
    apply (firstBlock_bijective f hp).1
    rw [firstBlock_fst f hp, LinearEquiv.apply_symm_apply, map_zero]

lemma preservesCoordinates_iff (τ : MulAut (Sp F)) (f : pairedNormalizer τ) :
    PreservesCoordinates f.val ↔
      f ∈ summandStabilizer (normalizerAction τ) ∧
      f ∈ subspaceStabilizer (normalizerAction τ) secondSummand := by
  constructor
  · intro hp
    constructor
    · intro v
      change f.val v ∈ firstSummand ↔ v ∈ firstSummand
      rw [mem_firstSummand, mem_firstSummand, ← secondBlock_snd _ hp]
      exact (secondBlockEquiv f.val hp).map_eq_zero_iff
    · intro v
      change f.val v ∈ secondSummand ↔ v ∈ secondSummand
      rw [mem_secondSummand, mem_secondSummand, ← firstBlock_fst _ hp]
      exact (firstBlockEquiv f.val hp).map_eq_zero_iff
  · rintro ⟨hU, hW⟩
    exact ⟨fun w => (mem_firstSummand _).mp ((hU (w, 0)).mpr ⟨w, rfl⟩),
      fun w => (mem_secondSummand _).mp ((hW (0, w)).mpr ⟨w, rfl⟩)⟩

lemma normalizer_intertwines (τ : MulAut (Sp F))
    (f : Space F ≃ₗ[ZMod 2] Space F) (hf : f ∈ pairedNormalizer τ)
    (g : commutator (Sp F)) :
    ∃ h : commutator (Sp F), ∀ v, f (derivedPair τ g v) = derivedPair τ h (f v) := by
  have hm := (Subgroup.mem_normalizer_iff.mp hf (linearAction (derivedPair τ) g)).mp ⟨g, rfl⟩
  obtain ⟨h, hh⟩ := hm
  refine ⟨h, fun v => ?_⟩
  have he := congrArg (fun e : Space F ≃ₗ[ZMod 2] Space F => e (f v)) hh
  change derivedPair τ h (f v) = f (derivedPair τ g (f.symm (f v))) at he
  simpa only [LinearEquiv.symm_apply_apply] using he.symm

lemma firstBlock_mem_naturalNormalizer [Finite F] (τ : MulAut (Sp F))
    (f : Space F ≃ₗ[ZMod 2] Space F) (hf : f ∈ pairedNormalizer τ)
    (hp : PreservesCoordinates f) : firstBlockEquiv f hp ∈ naturalNormalizer := by
  let e := firstBlockEquiv f hp
  have hconj (g : commutator (Sp F)) :
      e * linearAction naturalDerivedAction g * e⁻¹ ∈ naturalDerivedImage := by
    obtain ⟨h, hh⟩ := normalizer_intertwines τ f hf g
    refine ⟨h, ?_⟩
    apply LinearEquiv.ext
    intro v
    have he := congrArg Prod.fst (hh (e.symm v, 0))
    change naturalDerivedAction h v = e (naturalDerivedAction g (e.symm v))
    have hi : e (naturalDerivedAction g (e.symm v)) = naturalDerivedAction h (e (e.symm v)) := by
      change (f (symplecticNatural 2 g.val (e.symm v), 0)).1 =
        symplecticNatural 2 h.val (f (e.symm v, 0)).1
      change (f (symplecticNatural 2 g.val (e.symm v),
        symplecticNatural 2 (τ g.val) 0)).1 =
        symplecticNatural 2 h.val (f (e.symm v, 0)).1 at he
      simpa only [map_zero] using he
    rw [e.apply_symm_apply] at hi
    exact hi.symm
  have : Finite (naturalDerivedImage (F := F)) :=
    Finite.of_surjective (linearAction (naturalDerivedAction (F := F))).rangeRestrict
      (linearAction (naturalDerivedAction (F := F))).rangeRestrict_surjective
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact hconj g
  · exact (Subgroup.card_map_of_injective (MulAut.conj e).injective).ge

end SymplecticConjugatePair.Ambient.Normalizer
