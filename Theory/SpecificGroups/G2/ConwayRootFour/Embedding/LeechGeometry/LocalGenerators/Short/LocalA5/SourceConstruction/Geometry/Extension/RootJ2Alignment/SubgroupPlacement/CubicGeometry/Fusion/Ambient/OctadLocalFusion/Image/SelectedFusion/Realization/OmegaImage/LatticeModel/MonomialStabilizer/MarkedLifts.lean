module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.OmegaImage.LatticeModel.ReducedKernel
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Counting
public import Theory.AtlasPort.OtherSporadic.Conway.GolayOctadRestriction
public import Theory.Mathieu.M24.LocalGeometry.LinearFourCore
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction.DerivedBound

/-!
# Marked monomial lifts for the reduced octad lattice

The native octad 100 is reindexed along the established native/ATLAS marking.
Its permutation image on the eight supported coordinates is precisely A8.
Every even sign word extends to a Golay word. These two facts construct actual
integral centralizer lifts of all even signed alternating coordinate actions.
Conversely, a monomial element centralizing the octad sign has precisely this
form. The published reduction action and kernel retain the literal quotient
maps throughout.

Perfectness of the native octad stabilizer places its permutation image in
Omega. Containment for the sign actions and reconstruction of every Omega
axis-fixer remain separate geometric obligations. No image equality is asserted.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1(4), 25.2 and the stabilizer
argument in 25.5(7), pp.132–134. The Golay, Leech and Mathieu primitives are
existing licensed ATLAS ports; see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`.
-/

open Atlas.Codes Atlas.Lattices Atlas.Conway
open scoped BigOperators
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace Realization.OmegaImage.LatticeModel
namespace MonomialStabilizer
attribute [local irreducible] golayBasis
open Sporadic.Mathieu.M24LocalGeometry
abbrev NativeStabilizer := octadStabilizer KernelModel.nativeOctad

def nativeCoordinates : Coordinate ≃ KernelModel.nativeOctad.val :=
  (MathieuCode.atlasPointEquiv.symm.subtypeEquiv
    (p := fun i : Fin 24 => i ∈ KernelModel.nativeOctad.val)
    (q := fun i : Omega => (golayBasis 0).val i ≠ 0)
    KernelModel.nativeOctad_support).symm

def coordinatePermutation : NativeStabilizer →* Equiv.Perm Coordinate :=
  nativeCoordinates.symm.permCongrHom.toMonoidHom.comp
    (MathieuCode.CocodeOctad.coordinateAction KernelModel.nativeOctad)

theorem coordinatePermutation_apply (p : NativeStabilizer) (i : Coordinate) :
    (coordinatePermutation p i).val = (SextetCore.groupEquiv p.val).val i.val := rfl

theorem coordinatePermutation_symm_apply (p : NativeStabilizer) (i : Coordinate) :
    ((coordinatePermutation p).symm i).val = (SextetCore.groupEquiv p.val).val.symm i.val := by
  apply (SextetCore.groupEquiv p.val).val.injective
  rw [← coordinatePermutation_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem coordinatePermutation_range :
    coordinatePermutation.range = alternatingGroup Coordinate := by
  ext p
  constructor
  · rintro ⟨g, rfl⟩
    apply Equiv.Perm.mem_alternatingGroup.mpr
    change Equiv.Perm.sign (nativeCoordinates.symm.permCongr
      (MathieuCode.CocodeOctad.coordinateAction KernelModel.nativeOctad g)) = 1
    rw [Equiv.Perm.sign_permCongr]
    apply Equiv.Perm.mem_alternatingGroup.mp
    rw [← MathieuCode.CocodeOctad.coordinateAction_range]
    exact ⟨g, rfl⟩
  · intro hp
    let q := nativeCoordinates.permCongr p
    have hq : q ∈ alternatingGroup KernelModel.nativeOctad.val := by
      apply Equiv.Perm.mem_alternatingGroup.mpr
      rw [Equiv.Perm.sign_permCongr]
      exact Equiv.Perm.mem_alternatingGroup.mp hp
    rw [← MathieuCode.CocodeOctad.coordinateAction_range] at hq
    obtain ⟨g, hg⟩ := hq
    refine ⟨g, ?_⟩
    change nativeCoordinates.symm.permCongr
      (MathieuCode.CocodeOctad.coordinateAction KernelModel.nativeOctad g) = p
    rw [hg]
    exact nativeCoordinates.permCongr.symm_apply_apply p

private theorem permCongr_inverse {A B : Type*} (e : A ≃ B) (p : Equiv.Perm A) (i : B) :
    (e.permCongr p).symm i = e (p.symm (e.symm i)) := rfl

private theorem atlas_inverse (p : Sporadic.Mathieu.M24) (i : Omega) :
    (SextetCore.groupEquiv p).val.symm i =
      MathieuCode.atlasPointEquiv.symm (p.val.symm (MathieuCode.atlasPointEquiv i)) := by
  rw [SextetCore.groupEquiv_apply, permCongr_inverse, Equiv.symm_symm]

private theorem marked_word (c : golay) (O : Sporadic.Mathieu.M24LocalGeometry.Octad)
    (hO : ∀ j : Fin 24, j ∈ O.val ↔ c.val (MathieuCode.atlasPointEquiv.symm j) ≠ 0)
    (p : octadStabilizer O) (i : Omega) :
    c.val ((SextetCore.groupEquiv p.val).val.symm i) =
      c.val i := by
  have hp := MulAction.mem_stabilizer_finset.mp p.prop
  have hs : c.val ((SextetCore.groupEquiv p.val).val.symm i) ≠ 0 ↔
      c.val i ≠ 0 := by
    have hc (j : Omega) : MathieuCode.atlasPointEquiv j ∈ O.val ↔
        c.val j ≠ 0 := by
      simpa only [Equiv.symm_apply_apply] using
        hO (MathieuCode.atlasPointEquiv j)
    rw [← hc, ← hc]
    rw [atlas_inverse, Equiv.apply_symm_apply]
    change p.val.val.symm (MathieuCode.atlasPointEquiv i) ∈ O.val ↔
      MathieuCode.atlasPointEquiv i ∈ O.val
    have h := (hp (p.val.val.symm (MathieuCode.atlasPointEquiv i))).symm
    change _ ↔ p.val.val (p.val.val.symm (MathieuCode.atlasPointEquiv i)) ∈ _ at h
    simpa only [Equiv.apply_symm_apply] using h
  rcases bit_cases (c.val ((SextetCore.groupEquiv p.val).val.symm i)) with h | h
  · rcases bit_cases (c.val i) with k | k
    · exact h.trans k.symm
    · exact False.elim ((hs.mpr (k ▸ one_ne_zero)) h)
  · rcases bit_cases (c.val i) with k | k
    · exact False.elim ((hs.mp (h ▸ one_ne_zero)) k)
    · exact h.trans k.symm

theorem native_word (p : NativeStabilizer) (i : Omega) :
    (golayBasis 0).val ((SextetCore.groupEquiv p.val).val.symm i) =
      (golayBasis 0).val i :=
  marked_word (golayBasis 0) KernelModel.nativeOctad KernelModel.nativeOctad_support p i

def signs : Multiplicative golay →* centralizer :=
  signEmbedding.codRestrict centralizer (by
    intro c
    apply mem_centralizer.mpr
    exact (Commute.all c (Multiplicative.ofAdd (golayBasis 0))).map signEmbedding)

def permutations : NativeStabilizer →* centralizer :=
  (permutationEmbedding.comp (SextetCore.groupEquiv.toMonoidHom.comp
    (octadStabilizer KernelModel.nativeOctad).subtype)).codRestrict centralizer (by
      intro p
      apply mem_centralizer.mpr
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      apply Subtype.ext
      funext i
      change (if (golayBasis 0).val ((SextetCore.groupEquiv p.val).val.symm i) = 0
        then x.val ((SextetCore.groupEquiv p.val).val.symm i)
        else -x.val ((SextetCore.groupEquiv p.val).val.symm i)) =
        (if (golayBasis 0).val i = 0 then x.val ((SextetCore.groupEquiv p.val).val.symm i)
        else -x.val ((SextetCore.groupEquiv p.val).val.symm i))
      rw [native_word])

def lift (c : golay) (p : NativeStabilizer) : centralizer :=
  signs (Multiplicative.ofAdd c) * permutations p

theorem lift_val (c : golay) (p : NativeStabilizer) :
    (lift c p).val = monomialEmbedding ⟨Multiplicative.ofAdd c, SextetCore.groupEquiv p.val⟩ := rfl

theorem lift_apply (c : golay) (p : NativeStabilizer) (x : lattice) (i : Coordinate) :
    (action (lift c p) x).val.val i.val =
      if c.val i.val = 0 then x.val.val ((coordinatePermutation p).symm i).val
      else -x.val.val ((coordinatePermutation p).symm i).val := by
  rw [coordinatePermutation_symm_apply]
  rfl


def signRestriction : golay →ₗ[Bit] (Coordinate → Bit) where
  toFun c i := c.val i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem signRestriction_even (c : golay) : ∑ i, signRestriction c i = 0 := by
  have h := golay_selfOrthogonal (golayBasis 0).prop c.val c.prop
  change binaryDot c.val (golayBasis 0).val = 0 at h
  rw [binaryDot_apply] at h
  have he : (∑ i : Coordinate, c.val i.val) =
      ∑ i : Omega, c.val i * (golayBasis 0).val i := by
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro i hi
      have hz : (golayBasis 0).val i = 0 := by
        by_contra hn
        exact hi ⟨⟨i, hn⟩, rfl⟩
      rw [hz, mul_zero]
    · intro i
      have hi : (golayBasis 0).val i.val = 1 := by
        rcases bit_cases ((golayBasis 0).val i.val) with h | h
        · exact (i.prop h).elim
        · exact h
      rw [hi, mul_one]
  exact he.trans h

theorem signRestriction_surjective_even (s : Coordinate → Bit) (hs : ∑ i, s i = 0) :
    ∃ c : golay, signRestriction c = s := by
  classical
  let T := support (golayBasis 0).val
  have hT : T.card = 8 := ambientOctad_weight
  have hmem (i : Omega) : i ∈ T ↔ (golayBasis 0).val i ≠ 0 := by simp [T, support]
  have hw : supportWord T = (golayBasis 0).val := by
    funext i
    rcases bit_cases ((golayBasis 0).val i) with h | h <;> simp [supportWord, hmem, h]
  let w : BinaryWord := fun i => if hi : (golayBasis 0).val i ≠ 0 then s ⟨i, hi⟩ else 0
  have hsum : ∑ i ∈ T, w i = 0 := by
    rw [← Finset.sum_coe_sort]
    have he : (∑ i : T, w i.val) = ∑ i : Coordinate, s i := by
      apply Fintype.sum_equiv (Equiv.subtypeEquivRight hmem)
      intro i
      simp only [w, dif_pos ((hmem i.val).mp i.prop)]
      rfl
    exact he.trans hs
  obtain ⟨c, hc⟩ := golay_octad_restriction T hT (by rw [hw]; exact (golayBasis 0).prop) w hsum
  refine ⟨c, ?_⟩
  funext i
  have h := hc i.val ((hmem _).mpr i.prop)
  simpa [signRestriction, w, i.prop] using h

theorem lift_fixes_axis (c : golay) (p : NativeStabilizer) (i : Coordinate) :
    linearAction (lift c p) (reduction (axis i)) = reduction (axis i) := by
  apply (fixes_axis_class_iff_monomial _ i).mpr
  exact ⟨⟨Multiplicative.ofAdd c, SextetCore.groupEquiv p.val⟩, rfl⟩

theorem monomial_word_of_centralizes (m : GolayMonomialGroup)
    (hm : monomialEmbedding m ∈ centralizer) :
    golayPermutationEquiv m.right (golayBasis 0) = golayBasis 0 := by
  let b : GolayMonomialGroup := SemidirectProduct.inl (Multiplicative.ofAdd (golayBasis 0))
  have hb : monomialEmbedding b = sign := rfl
  have hcomm := (mem_centralizer.mp hm).eq
  rw [← hb, ← map_mul, ← map_mul] at hcomm
  have h := congrArg (fun n : GolayMonomialGroup => n.left.toAdd)
    (monomialEmbedding_injective hcomm)
  change m.left.toAdd + golayPermutationEquiv m.right (golayBasis 0) =
    golayBasis 0 + m.left.toAdd at h
  exact add_left_cancel (h.trans (add_comm _ _))

theorem native_of_word (p : Mathieu24CodeModel)
    (hp : golayPermutationEquiv p (golayBasis 0) = golayBasis 0) :
    SextetCore.groupEquiv.symm p ∈ octadStabilizer KernelModel.nativeOctad := by
  apply MulAction.mem_stabilizer_finset.mpr
  intro i
  let n := SextetCore.groupEquiv.symm p
  have he (j : Omega) : (golayBasis 0).val (p.val.symm j) = (golayBasis 0).val j :=
    congrArg (fun c : golay => c.val j) hp
  have hh := he (p.val (MathieuCode.atlasPointEquiv.symm i))
  rw [Equiv.symm_apply_apply] at hh
  have hn : MathieuCode.atlasPointEquiv.symm (n.val i) =
      p.val (MathieuCode.atlasPointEquiv.symm i) := by
    have h := congrArg (fun q : Mathieu24CodeModel => q.val
      (MathieuCode.atlasPointEquiv.symm i)) (SextetCore.groupEquiv.apply_symm_apply p)
    change MathieuCode.atlasPointEquiv.symm
      (n.val (MathieuCode.atlasPointEquiv (MathieuCode.atlasPointEquiv.symm i))) = _ at h
    simpa only [Equiv.apply_symm_apply] using h
  change n.val i ∈ KernelModel.nativeOctad.val ↔ i ∈ KernelModel.nativeOctad.val
  rw [KernelModel.nativeOctad_support, KernelModel.nativeOctad_support, hn, hh]

theorem exists_lift_of_monomial (a : centralizer) (ha : a.val ∈ monomialSubgroup) :
    ∃ c : golay, ∃ p : NativeStabilizer, lift c p = a := by
  obtain ⟨m, hm⟩ := ha
  let p : NativeStabilizer := ⟨SextetCore.groupEquiv.symm m.right,
    native_of_word m.right (monomial_word_of_centralizes m (hm.symm ▸ a.prop))⟩
  refine ⟨m.left.toAdd, p, ?_⟩
  apply Subtype.ext
  rw [lift_val]
  change monomialEmbedding ⟨m.left, SextetCore.groupEquiv (SextetCore.groupEquiv.symm m.right)⟩ = a.val
  rw [MulEquiv.apply_symm_apply]
  exact hm



/-- A literal signed-coordinate description, including a lattice representative
of every transformed reduction class. -/
def SignedAction (C : Coordinates) (s : Coordinate → Bit) (p : Equiv.Perm Coordinate)
    (g : SelectedGeometry.Orthogonal) : Prop :=
  ∀ x : lattice, ∃ y : lattice,
    (∀ i : Coordinate, y.val.val i.val =
      if s i = 0 then x.val.val (p.symm i).val else -x.val.val (p.symm i).val) ∧
    g.val (C.coordinates (reduction x)) = C.coordinates (reduction y)

theorem signedAction_lift (C : Coordinates) (c : golay) (p : NativeStabilizer) :
    SignedAction C (signRestriction c) (coordinatePermutation p)
      (C.orthogonalAction (lift c p)) := by
  intro x
  exact ⟨action (lift c p) x, lift_apply c p x, C.orthogonalAction_reduction _ _⟩

/-- Equality here is equality of the actual linear maps, not an abstract
isomorphism of their images. -/
theorem signedAction_unique (C : Coordinates) (s : Coordinate → Bit)
    (p : Equiv.Perm Coordinate) {g h : SelectedGeometry.Orthogonal}
    (hg : SignedAction C s p g) (hh : SignedAction C s p h) : g = h := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  obtain ⟨a, rfl⟩ := C.coordinates.surjective v
  obtain ⟨x, rfl⟩ := reduction_surjective a
  obtain ⟨y, hy, hgy⟩ := hg x
  obtain ⟨z, hz, hhz⟩ := hh x
  have he : y = z := coordinates_injective (funext fun i => (hy i).trans (hz i).symm)
  rw [hgy, hhz, he]

/-- Every even signed alternating action is realized by a literal element of
the integral Leech centralizer with the native octad marking. -/
theorem signedAction_has_lift (C : Coordinates) (s : Coordinate → Bit)
    (hs : ∑ i, s i = 0) (p : Equiv.Perm Coordinate) (hp : p ∈ alternatingGroup Coordinate)
    (g : SelectedGeometry.Orthogonal) (hg : SignedAction C s p g) :
    ∃ a : centralizer, a.val ∈ monomialSubgroup ∧ C.orthogonalAction a = g := by
  obtain ⟨c, rfl⟩ := signRestriction_surjective_even s hs
  obtain ⟨q, rfl⟩ := (show p ∈ coordinatePermutation.range by rw [coordinatePermutation_range]; exact hp)
  exact ⟨lift c q, ⟨⟨Multiplicative.ofAdd c, SextetCore.groupEquiv q.val⟩, rfl⟩,
    signedAction_unique C _ _ (signedAction_lift C c q) hg⟩


/-- The native octad stabilizer is perfect, so its literal orthogonal image
lies in the proved full commutator bound for binary split dimension eight. -/
theorem permutations_mem_omega (C : Coordinates) (p : NativeStabilizer) :
    C.orthogonalAction (permutations p) ∈ SelectedGeometry.omega := by
  let : Group.IsPerfect NativeStabilizer :=
    (Sporadic.Mathieu.M24LocalGeometry.LinearFourCore.octad_core_structure
      KernelModel.nativeOctad).1
  let f := C.orthogonalAction.comp permutations
  have hp : p ∈ commutator NativeStabilizer := by
    rw [Group.IsPerfect.commutator_eq_top]
    trivial
  have hm : f p ∈ (commutator NativeStabilizer).map f := ⟨p, hp, rfl⟩
  rw [map_commutator_eq] at hm
  exact ClassicalOrthogonal.BinaryEightObstruction.commutator_full_le_elementary
    (Subgroup.commutator_mono (show f.range ≤ ⊤ from le_top)
      (show f.range ≤ ⊤ from le_top) hm)

theorem lift_mem_omega_of_signs (C : Coordinates)
    (hSigns : ∀ c : golay, C.orthogonalAction (signs (Multiplicative.ofAdd c)) ∈
      SelectedGeometry.omega) (c : golay) (p : NativeStabilizer) :
    C.orthogonalAction (lift c p) ∈ SelectedGeometry.omega := by
  rw [lift, map_mul]
  exact SelectedGeometry.omega.mul_mem (hSigns c) (permutations_mem_omega C p)

end MonomialStabilizer

/-- The integral monomial criterion transported through the given norm coordinates. -/
theorem Coordinates.fixes_axis_iff_monomial (C : Coordinates) (a : centralizer)
    (i : Coordinate) :
    (C.orthogonalAction a).val (C.coordinates (reduction (axis i))) =
      C.coordinates (reduction (axis i)) ↔ a.val ∈ monomialSubgroup := by
  rw [C.orthogonalAction_reduction, C.coordinates.injective.eq_iff]
  exact fixes_axis_class_iff_monomial a i

/-- Every element in the image fixing the axis has an actual Golay/Mathieu lift. -/
theorem Coordinates.axis_mem_range_iff_lift (C : Coordinates) (i : Coordinate)
    (g : SelectedGeometry.Orthogonal)
    (hg : g.val (C.coordinates (reduction (axis i))) = C.coordinates (reduction (axis i))) :
    g ∈ C.orthogonalAction.range ↔ ∃ c : golay,
      ∃ p : MonomialStabilizer.NativeStabilizer,
        C.orthogonalAction (MonomialStabilizer.lift c p) = g := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨c, p, rfl⟩ := MonomialStabilizer.exists_lift_of_monomial a
      ((C.fixes_axis_iff_monomial a i).mp hg)
    exact ⟨c, p, rfl⟩
  · rintro ⟨c, p, rfl⟩
    exact ⟨_, rfl⟩

end Realization.OmegaImage.LatticeModel
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
