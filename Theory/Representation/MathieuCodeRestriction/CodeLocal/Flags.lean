module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.CoordinateTransport
public import Theory.Mathieu.M24.LocalGeometry.SextetCore.Hexacode
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.FixedLift
public import Theory.Representation.MathieuCodeRestriction.Duality
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The native code four-space and its exact sextet stabilizers

A code class is fixed by the intrinsic sextet two-core exactly when its
Golay representatives are constant on each tetrad. To prove the forward
implication, use translations with a zero coordinate in the hexacode: each
such translation fixes an actual point, so fixation lifts through the
constant-line quotient. Their coordinate projections connect every pair of
points in a tetrad. The reverse implication follows from the translation
coordinates.

The coordinate pairing identifies this space with the annihilator of the
seven-dimensional within-tetrad cocode pair span, giving dimension four.
Octads formed from two tetrads distinguish the parts and recover the exact
setwise stabilizer. Duality and the faithful natural action on six parts
then identify its ambient pointwise centralizer with the column kernel.
Its order is 192, whereas the intrinsic two-core has order 64.

Thus the pointwise-centralizer equality printed in the proof of H.16.6
is false on the literal native representation. This does not refute the
conclusion of H.16.6. The larger kernel agrees with the quotient convention
in H.16.1(2); identifying it with the intrinsic iterated core is a separate
statement, not used here. Chief factors and transvection assertions are
not claimed by this module.

Source: Aschbacher--Smith, H.16.1(1--2), printed p.402, and the proof of
H.16.6, printed pp.404--405, combined manuscript of 1 March 2004.
The affine coordinates are the existing licensed ATLAS ports by Gerald Höhn
and ATLAS contributors, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917;
see LICENSES/ATLAS.txt. No external source is copied here.
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
open MathieuCode.SextetLayers.CoordinateTransport
open scoped Pointwise BigOperators
namespace MathieuCode.CodeFlags

def sextetCore (S : Sextet) : Subgroup M24 :=
  (pCore 2 (sextetStabilizer S)).map (sextetStabilizer S).subtype

def annihilator (U : Submodule (ZMod 2) Cocode) : Submodule (ZMod 2) Code :=
  U.dualAnnihilator.comap codeDuality.toLinearEquiv.toLinearMap

lemma mem_annihilator (U : Submodule (ZMod 2) Cocode) (v : Code) :
    v ∈ annihilator U ↔ ∀ u ∈ U, codeCocodePairing v u = 0 :=
  Submodule.mem_dualAnnihilator (codeDuality v)

lemma finrank_annihilator_add (U : Submodule (ZMod 2) Cocode) :
    Module.finrank (ZMod 2) (annihilator U) + Module.finrank (ZMod 2) U = 11 := by
  unfold annihilator
  rw [Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq, add_comm,
    Subspace.finrank_add_finrank_dualAnnihilator_eq, finrank_cocode]

def sextetCodeSpace (S : Sextet) : Submodule (ZMod 2) Code :=
  annihilator (⨆ B ∈ S.parts, supportedPairSpace B)

lemma sextetCodeSpace_finrank (S : Sextet) :
    Module.finrank (ZMod 2) (sextetCodeSpace S) = 4 := by
  have h := finrank_annihilator_add (⨆ B ∈ S.parts, supportedPairSpace B)
  rw [sextetPairSpan_finrank] at h
  change Module.finrank (ZMod 2) (sextetCodeSpace S) + 7 = 11 at h
  omega

private lemma dot_pair (w : Full) (x y : Fin 24) (hxy : x ≠ y) :
    dotForm w (wordOfSet {x,y}) = w x + w y := by
  change (∑ z, w z * (if z ∈ ({x,y} : Finset (Fin 24)) then 1 else 0)) = _
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_pair hxy]

lemma sextetCodeSpace_mk_iff (S : Sextet) (w : golay) :
    codeLine.mkQ w ∈ sextetCodeSpace S ↔
      ∀ B ∈ S.parts, ∀ x ∈ B, ∀ y ∈ B, w.val x = w.val y := by
  rw [sextetCodeSpace, mem_annihilator]
  constructor
  · intro hv B hB x hx y hy
    by_cases hxy : x = y
    · exact congrArg w.val hxy
    have hp : pairVector ⟨{x,y}, by simp [hxy]⟩ ∈
        (⨆ B ∈ S.parts, supportedPairSpace B) := by
      apply (le_iSup_of_le B (le_iSup_of_le hB le_rfl) :
        supportedPairSpace B ≤ ⨆ B ∈ S.parts, supportedPairSpace B)
      apply pairVector_mem_supportedPairSpace
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · exact Finset.mem_singleton.mp hz ▸ hy
    have h := hv _ hp
    change dotForm w.val (wordOfSet {x,y}) = 0 at h
    simpa only [dot_pair _ _ _ hxy, CharTwo.add_eq_zero] using h
  · intro hc
    have hle : (⨆ B ∈ S.parts, supportedPairSpace B) ≤
        (codeCocodePairing (codeLine.mkQ w)).ker := by
      refine iSup_le fun B => iSup_le fun hB => ?_
      apply Submodule.span_le.mpr
      rintro v ⟨P, hP, rfl⟩
      change dotForm w.val (wordOfSet P.val) = 0
      obtain ⟨x, y, hxy, he⟩ := Finset.card_eq_two.mp P.property
      rw [he, dot_pair _ _ _ hxy]
      rw [hc B hB x (hP (by simp [he])) y (hP (by simp [he]))]
      exact CharTwo.add_self_eq_zero _
    exact fun u hu => hle hu

lemma nativeTranslation_range_eq_core (S : Sextet) :
    (nativeTranslation S).range = pCore 2 (sextetStabilizer S) := by
  change (translation (nativeStabilizerEquiv S)).range = _
  rw [translation, MonoidHom.range_comp, ← Atlas.Codes.sextetQuotient_kernel,
    ← SextetCore.atlas_core_eq_kernel, pCore_map_iso]

lemma sextetCore_card (S : Sextet) : Nat.card (sextetCore S) = 64 := by
  rw [sextetCore, Subgroup.card_map_of_injective (sextetStabilizer S).subtype_injective,
    ← nativeTranslation_range_eq_core, nativeTranslation_card]

lemma nativeTranslation_mem_core (S : Sextet) (t : Multiplicative Atlas.Codes.hexacode) :
    (nativeTranslation S t).val ∈ sextetCore S := by
  refine ⟨nativeTranslation S t, ?_, rfl⟩
  rw [← nativeTranslation_range_eq_core]
  exact ⟨t, rfl⟩

private lemma hex_coordinate_with_zero : ∀ (i : Atlas.Codes.HexIndex) (a : Atlas.Codes.K),
    ∃ m : Atlas.Codes.HexParameters,
      Atlas.Codes.hexEncoder m i = a ∧ ∃ j, Atlas.Codes.hexEncoder m j = 0 := by
  decide +kernel

lemma translation_coordinates (S : Sextet) (t : Multiplicative Atlas.Codes.hexacode)
    (i : Atlas.Codes.HexIndex) (k : Fin 4) :
    (nativeTranslation S t).val • nativePointEquiv S (i,k) =
      nativePointEquiv S (i, Atlas.Codes.rowLabel.symm (Atlas.Codes.rowLabel k + t.toAdd.val i)) :=
  nativeStabilizer_coordinates S (Atlas.Codes.sextetTranslation t) (i,k)

lemma sextetCore_fixed_mk_iff (S : Sextet) (w : golay) :
    codeLine.mkQ w ∈ fixedSpace codeRepresentation (sextetCore S) ↔
      ∀ B ∈ S.parts, ∀ x ∈ B, ∀ y ∈ B, w.val x = w.val y := by
  constructor
  · intro hw B hB x hx y hy
    obtain ⟨i, hi⟩ := (nativePartEquiv S).surjective ⟨B,hB⟩
    obtain ⟨⟨ix,k⟩, rfl⟩ := (nativePointEquiv S).surjective x
    obtain ⟨⟨iy,l⟩, rfl⟩ := (nativePointEquiv S).surjective y
    have hix : ix = i := (nativePointEquiv_mem_part S (ix,k) i).mp (by simpa [hi] using hx)
    have hiy : iy = i := (nativePointEquiv_mem_part S (iy,l) i).mp (by simpa [hi] using hy)
    subst ix; subst iy
    obtain ⟨m, hm, j, hj⟩ := hex_coordinate_with_zero i
      (Atlas.Codes.rowLabel l - Atlas.Codes.rowLabel k)
    let t : Multiplicative Atlas.Codes.hexacode :=
      Multiplicative.ofAdd ⟨Atlas.Codes.hexEncoder m, ⟨m,rfl⟩⟩
    let g := (nativeTranslation S t).val
    have hgj : g • nativePointEquiv S (j,0) = nativePointEquiv S (j,0) := by
      rw [translation_coordinates]
      change nativePointEquiv S (j, Atlas.Codes.rowLabel.symm
        (Atlas.Codes.rowLabel 0 + Atlas.Codes.hexEncoder m j)) = _
      rw [hj, add_zero, Equiv.symm_apply_apply]
    have hgi : g • nativePointEquiv S (i,k) = nativePointEquiv S (i,l) := by
      rw [translation_coordinates]
      change nativePointEquiv S (i, Atlas.Codes.rowLabel.symm
        (Atlas.Codes.rowLabel k + Atlas.Codes.hexEncoder m i)) = _
      rw [hm, add_sub_cancel, Equiv.symm_apply_apply]
    have he := golay_fixed_of_code_fixed g _ hgj w
      (hw ⟨g, nativeTranslation_mem_core S t⟩)
    have he' := congrArg (fun u : golay => u.val (g • nativePointEquiv S (i,k))) he
    change w.val (g⁻¹ • (g • nativePointEquiv S (i,k))) =
      w.val (g • nativePointEquiv S (i,k)) at he'
    rw [inv_smul_smul, hgi] at he'
    exact he'
  · intro hc g
    obtain ⟨a, ha, hga⟩ := g.property
    rw [← nativeTranslation_range_eq_core] at ha
    obtain ⟨t,rfl⟩ := ha
    have he : g.val = (nativeTranslation S t).val := hga.symm
    change codeRepresentation g.val (codeLine.mkQ w) = codeLine.mkQ w
    rw [codeRepresentation_mk]
    apply congrArg codeLine.mkQ
    apply Subtype.ext
    funext x
    change w.val (g.val⁻¹ • x) = w.val x
    have hginv : g.val⁻¹ = (nativeTranslation S t⁻¹).val := by rw [he, map_inv]; rfl
    rw [hginv]
    obtain ⟨⟨i,k⟩, rfl⟩ := (nativePointEquiv S).surjective x
    rw [translation_coordinates]
    exact hc _ (nativePartEquiv S i).property _
      ((nativePointEquiv_mem_part S _ i).mpr rfl) _
      ((nativePointEquiv_mem_part S _ i).mpr rfl)

lemma sextetCore_fixedSpace (S : Sextet) :
    fixedSpace codeRepresentation (sextetCore S) = sextetCodeSpace S := by
  ext v
  obtain ⟨w,rfl⟩ := codeLine.mkQ_surjective v
  rw [sextetCore_fixed_mk_iff, sextetCodeSpace_mk_iff]


lemma sextetCodeSpace_invariant (S : Sextet) (g : sextetStabilizer S)
    (v : Code) (hv : v ∈ sextetCodeSpace S) :
    codeRepresentation g.val v ∈ sextetCodeSpace S := by
  obtain ⟨w,rfl⟩ := codeLine.mkQ_surjective v
  rw [codeRepresentation_mk, sextetCodeSpace_mk_iff]
  have hc := (sextetCodeSpace_mk_iff S w).mp hv
  intro B hB x hx y hy
  have hB' : g.val⁻¹ • B ∈ S.parts :=
    (MulAction.mem_stabilizer_finset'.mp (g⁻¹).property) hB
  exact hc _ hB' _ (Finset.smul_mem_smul_finset hx) _ (Finset.smul_mem_smul_finset hy)

private lemma same_part_membership (S : Sextet) {B C : Finset (Fin 24)}
    (hB : B ∈ S.parts) (hC : C ∈ S.parts) {x y : Fin 24} (hx : x ∈ B) (hy : y ∈ B) :
    x ∈ C ↔ y ∈ C := by
  by_cases h : B = C
  · subst C; exact iff_of_true hx hy
  · exact iff_of_false (fun hc => Finset.disjoint_left.mp (S.disjoint _ hB _ hC h) hx hc)
      (fun hc => Finset.disjoint_left.mp (S.disjoint _ hB _ hC h) hy hc)

private lemma union_word_constant (S : Sextet) {B C : Finset (Fin 24)}
    (hB : B ∈ S.parts) (hC : C ∈ S.parts) :
    ∀ D ∈ S.parts, ∀ x ∈ D, ∀ y ∈ D,
      wordOfSet (B ∪ C) x = wordOfSet (B ∪ C) y := by
  intro D hD x hx y hy
  simp only [wordOfSet, Finset.mem_union,
    same_part_membership S hD hB hx hy, same_part_membership S hD hC hx hy]

private lemma same_part_of_code_words (S : Sextet) {B C : Finset (Fin 24)}
    (hB : B ∈ S.parts) (hC : C ∈ S.parts) {x y : Fin 24} (hx : x ∈ B) (hy : y ∈ C)
    (h : ∀ w : golay, codeLine.mkQ w ∈ sextetCodeSpace S → w.val x = w.val y) : B = C := by
  by_contra hBC
  obtain ⟨D,hD,hDn⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({B,C} : Finset (Finset (Fin 24)))) (t := S.parts)
    (by rw [S.card, Finset.card_pair hBC]; decide)
  have hDn' : D ≠ B ∧ D ≠ C := by simpa using hDn
  have hDB := hDn'.1
  have hDC := hDn'.2
  let w : golay := ⟨wordOfSet (B ∪ D), by
    rw [golay_eq_span_octads]
    exact Submodule.subset_span ⟨_, S.octad B hB D hD hDB.symm, rfl⟩⟩
  have hw := h w ((sextetCodeSpace_mk_iff S w).mpr (union_word_constant S hB hD))
  have hyB : y ∉ B := fun hyB =>
    Finset.disjoint_left.mp (S.disjoint B hB C hC hBC) hyB hy
  have hyD : y ∉ D := fun hyD =>
    Finset.disjoint_left.mp (S.disjoint D hD C hC hDC) hyD hy
  change wordOfSet (B ∪ D) x = wordOfSet (B ∪ D) y at hw
  simp [wordOfSet, hx, hyB, hyD] at hw

/-- The tetrad partition is recovered from equality of coordinates on the code space. -/
lemma sextetCodeSpace_stabilizer (S : Sextet) :
    subspaceStabilizer codeRepresentation (sextetCodeSpace S) = sextetStabilizer S := by
  apply le_antisymm
  · intro g hg
    apply MulAction.mem_stabilizer_finset'.mpr
    intro B hB
    obtain ⟨x,hx⟩ := sextetPart_nonempty S ⟨B,hB⟩
    obtain ⟨C,hxC⟩ := sextetPart_exists S (g • x)
    have hsub : g • B ⊆ C.val := by
      intro z hz
      obtain ⟨y,hy,rfl⟩ := Finset.mem_smul_finset.mp hz
      obtain ⟨D,hyD⟩ := sextetPart_exists S (g • y)
      have hCD : C.val = D.val := same_part_of_code_words S C.property D.property hxC hyD (by
        intro w hw
        have hmem := ((subspaceStabilizer codeRepresentation (sextetCodeSpace S)).inv_mem hg
          (codeLine.mkQ w)).mpr hw
        rw [codeRepresentation_mk] at hmem
        exact (sextetCodeSpace_mk_iff S (golayRepresentation g⁻¹ w)).mp hmem
          B hB x hx y hy)
      rwa [hCD]
    have he : g • B = C.val := Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_smul_finset, S.tetrad B hB, S.tetrad _ C.property])
    rw [he]
    exact C.property
  · exact le_subspaceStabilizer _ _ (fun g hg v hv => sextetCodeSpace_invariant S ⟨g,hg⟩ v hv)

lemma fixes_annihilator_iff (U : Submodule (ZMod 2) Cocode) (g : M24) :
    (∀ v ∈ annihilator U, codeRepresentation g v = v) ↔
      ∀ u, cocodeRepresentation g u - u ∈ U := by
  constructor
  · intro hfix u
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U _).mp
    intro f hf
    obtain ⟨v,rfl⟩ := codeDuality.surjective f
    have he := codeCocodePairing_invariant g v u
    rw [hfix v hf] at he
    exact (map_sub _ _ _).trans (sub_eq_zero.mpr he)
  · intro hmove v hv
    apply codeDuality.injective
    apply LinearMap.ext
    intro u
    have he := codeCocodePairing_invariant g v (cocodeRepresentation g⁻¹ u)
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] at he
    change codeCocodePairing (codeRepresentation g v) u = codeCocodePairing v u
    rw [he]
    have hz := (mem_annihilator U v).mp hv _
      (hmove (cocodeRepresentation g⁻¹ u))
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply, map_sub, sub_eq_zero] at hz
    exact hz.symm

lemma sextetCodeSpace_fixed_iff_partPerm (S : Sextet) (g : sextetStabilizer S) :
    (∀ v ∈ sextetCodeSpace S, codeRepresentation g.val v = v) ↔ sextetPartPerm S g = 1 := by
  rw [sextetCodeSpace, fixes_annihilator_iff]
  constructor
  · intro h
    apply sextetNatural_faithful S
    rw [map_one]
    apply LinearMap.ext
    intro v
    obtain ⟨u,rfl⟩ := sextetCocodeParity_surjective S v
    rw [← sextetCocodeParity_equivariant]
    change sextetCocodeParity S (cocodeRepresentation g.val u) = sextetCocodeParity S u
    apply sub_eq_zero.mp
    rw [← map_sub]
    have hm := h u
    rw [← sextetCocodeParity_ker S] at hm
    exact hm
  · intro hg u
    rw [← sextetCocodeParity_ker S]
    change sextetCocodeParity S (cocodeRepresentation g.val u - u) = 0
    rw [map_sub, sextetCocodeParity_equivariant, hg, map_one, Module.End.one_apply, sub_self]

/-- The full ambient pointwise centralizer is the column kernel of order 192. -/
lemma sextetCodeSpace_centralizer (S : Sextet) :
    subspaceKernel codeRepresentation (sextetCodeSpace S) ⊤ =
      (sextetPartPerm S).ker.map (sextetStabilizer S).subtype := by
  ext g
  constructor
  · rintro ⟨_,hg⟩
    have hstab : g ∈ sextetStabilizer S := by
      rw [← sextetCodeSpace_stabilizer S]
      intro v
      constructor
      · intro hv
        have he := (Representation.apply_bijective codeRepresentation g).injective (hg _ hv)
        rwa [he] at hv
      · intro hv
        rw [hg v hv]
        exact hv
    exact ⟨⟨g,hstab⟩, (sextetCodeSpace_fixed_iff_partPerm S ⟨g,hstab⟩).mp hg, rfl⟩
  · rintro ⟨s,hs,rfl⟩
    exact ⟨Subgroup.mem_top _, (sextetCodeSpace_fixed_iff_partPerm S s).mpr hs⟩

lemma sextetCodeSpace_centralizer_card (S : Sextet) :
    Nat.card (subspaceKernel codeRepresentation (sextetCodeSpace S) ⊤) = 192 := by
  rw [sextetCodeSpace_centralizer,
    Subgroup.card_map_of_injective (sextetStabilizer S).subtype_injective,
    nativePartPerm_kernel_card]

lemma sextet_fixed_centralizer_ne_core (S : Sextet) :
    subspaceKernel codeRepresentation (fixedSpace codeRepresentation (sextetCore S)) ⊤ ≠
      sextetCore S := by
  intro he
  have h := congrArg (fun H : Subgroup M24 => Nat.card H) he
  rw [sextetCore_fixedSpace, sextetCodeSpace_centralizer_card, sextetCore_card] at h
  norm_num at h

/-- The intrinsic two-core is properly contained in the ambient pointwise centralizer. -/
lemma sextetCore_lt_fixed_centralizer (S : Sextet) :
    sextetCore S <
      subspaceKernel codeRepresentation (fixedSpace codeRepresentation (sextetCore S)) ⊤ := by
  apply lt_of_le_of_ne
  · intro g hg
    exact ⟨Subgroup.mem_top _, fun v hv => hv ⟨g,hg⟩⟩
  · exact (sextet_fixed_centralizer_ne_core S).symm

end MathieuCode.CodeFlags
