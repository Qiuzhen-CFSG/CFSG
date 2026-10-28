/-
The Golay and affine sextet constructions used here are by Gerald Höhn and
ATLAS contributors, under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt. Their source modules record revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.HexacodeDual.Actions
public import Theory.AtlasPort.OtherSporadic.Codes.GolayDuality

/-!
# Perfect duality for the actual middle sextet cocode quotient

Pair a zero-column-parity word with the binary lift of a hexacode word.
Golay self-duality makes this independent of the Golay representative, and
whole columns pair to zero. Conversely, a word in the radical becomes a
Golay word after subtracting its dot product with the twist word times one
whole column. Thus the radical on the pair space is exactly the tetrad line.
Extending functionals to the ambient hexacode word space and using its
nondegenerate polar form proves surjectivity without a dimension assumption.

The pairing respects the actual affine sextet action: equal recoveries differ
by even repetitions, the recovery map is equivariant, and coordinate
permutations preserve dot products. This identifies the literal middle
quotient with the contragredient of the action already identified in `Actions`
with conjugation on the translation subgroup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.15.3(1),
printed p.400/PDF p.411; the licensed ATLAS Golay and hexacode constructions.
Dimension and irreducibility are left to the assembly module.
-/

public section

open scoped BigOperators
open Atlas.Codes
namespace MathieuCode.SextetLayers
noncomputable section

private lemma jWord_mem_golay (h : hexacode) : jWord h.val ∈ golay := by
  exact ⟨(h,0,0), by simp [golayEncoder, c0Encoder]⟩

private def coreHexPairing : AtlasCore →ₗ[Bit] Module.Dual Bit hexacode :=
  (jWord.comp hexacode.subtype).dualMap.comp (LinearMap.comp binaryDot AtlasCore.subtype)

private lemma code_le_pairing_ker : atlasCodeInCore ≤ coreHexPairing.ker := by
  intro w hw
  ext h
  change binaryDot w.val (jWord h.val) = 0
  exact golay_selfOrthogonal (jWord_mem_golay h) _ hw

/-- The binary dot pairing with lifted hexacode words descends through Golay. -/
def atlasCocodeHexPairing : AtlasCocode →ₗ[Bit] Module.Dual Bit hexacode :=
  atlasCodeInCore.liftQ coreHexPairing code_le_pairing_ker

lemma atlasCocodeHexPairing_mk (w : AtlasCore) (h : hexacode) :
    atlasCocodeHexPairing (atlasCodeInCore.mkQ w) h = binaryDot w.val (jWord h.val) := by
  rfl

private lemma evenColumns_rho_dot (w : BinaryWord) (hw : atlasColumnParity w = 0)
    (r : Fin 6 → Bit) : binaryDot w (rho r) = 0 := by
  rw [binaryDot_apply, Fintype.sum_prod_type]
  change (∑ i : HexIndex, ∑ k : Fin 4, w (i,k) * r (hexIndexEquiv i)) = 0
  simp only [← Finset.sum_mul]
  change (∑ i, atlasColumnParity w i * r (hexIndexEquiv i)) = 0
  simp [hw]

private lemma tetrad_dot (i : HexIndex) (w : BinaryWord) :
    binaryDot (atlasTetradCore i).val w = atlasColumnParity w i := by
  classical
  rw [binaryDot_apply, Fintype.sum_prod_type]
  change (∑ j : HexIndex, ∑ k : Fin 4, (if j = i then (1 : Bit) else 0) * w (j,k)) = _
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp [atlasColumnParity]

private lemma jWord_evenColumns (h : HexWord) : atlasColumnParity (jWord h) = 0 := by
  ext i
  exact j_sum (h i)

private lemma tetrad_pairing_zero (i : HexIndex) :
    atlasCocodeHexPairing (atlasCodeInCore.mkQ (atlasTetradCore i)) = 0 := by
  ext h
  rw [atlasCocodeHexPairing_mk, tetrad_dot, jWord_evenColumns]
  rfl

private lemma line_le_pairing_ker : atlasTetradLine ≤ atlasCocodeHexPairing.ker := by
  apply Submodule.span_le.mpr
  rw [Set.singleton_subset_iff]
  exact tetrad_pairing_zero (0,0)

/-- The pairing restricted to the actual pair space. -/
def atlasPairHexPairing : atlasPairSpace →ₗ[Bit] Module.Dual Bit hexacode :=
  atlasCocodeHexPairing.comp atlasPairSpace.subtype

/-- The tetrad line is killed, using precisely the pullback denominator. -/
lemma atlasLineInPair_le_pairing_ker : atlasLineInPair ≤ atlasPairHexPairing.ker := by
  intro v hv
  exact line_le_pairing_ker hv

/-- The binary pairing on the actual middle cocode quotient. -/
def atlasMiddlePairing : AtlasMiddle →ₗ[Bit] Module.Dual Bit hexacode :=
  atlasLineInPair.liftQ atlasPairHexPairing atlasLineInPair_le_pairing_ker

lemma atlasMiddlePairing_mk (v : atlasPairSpace) :
    atlasMiddlePairing (atlasLineInPair.mkQ v) = atlasPairHexPairing v := by
  rfl

private lemma radical_sub_tetrad_mem_golay (w : BinaryWord)
    (hw : atlasColumnParity w = 0)
    (hz : ∀ h : hexacode, binaryDot w (jWord h.val) = 0) :
    w - binaryDot w eta • (atlasTetradCore (0,0)).val ∈ golay := by
  rw [golay_selfDual]
  rintro _ ⟨⟨h,r,e⟩,rfl⟩
  rw [binaryDot_symmetric]
  have hj : binaryDot (atlasTetradCore (0,0)).val (jWord h.val) = 0 := by
    rw [tetrad_dot, jWord_evenColumns]
    rfl
  have hr : binaryDot (atlasTetradCore (0,0)).val (rho r.val) = 0 := by
    rw [atlasTetradCore_coe_eq_rho, rho_dot]
  have he : binaryDot (atlasTetradCore (0,0)).val eta = 1 := by
    rw [tetrad_dot]
    exact eta_block_sum _
  simp [golayEncoder, c0Encoder, map_sub, map_add, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply, hz h, evenColumns_rho_dot w hw r.val,
    hj, hr, he]

/-- On the pair space the exact radical is the published tetrad line. -/
theorem atlasPairHexPairing_ker : atlasPairHexPairing.ker = atlasLineInPair := by
  apply le_antisymm
  · intro v hv
    obtain ⟨w, hw, he⟩ := v.property
    have hz : ∀ h : hexacode, binaryDot w.val (jWord h.val) = 0 := by
      intro h
      have hh := DFunLike.congr_fun hv h
      change atlasCocodeHexPairing v.val h = 0 at hh
      rw [← he, atlasCocodeHexPairing_mk] at hh
      exact hh
    have hg : w - binaryDot w.val eta • atlasTetradCore (0,0) ∈ atlasCodeInCore :=
      radical_sub_tetrad_mem_golay w.val hw hz
    change v.val ∈ atlasTetradLine
    have heq : atlasCodeInCore.mkQ w =
        atlasCodeInCore.mkQ (binaryDot w.val eta • atlasTetradCore (0,0)) :=
      (Submodule.Quotient.eq atlasCodeInCore).mpr hg
    rw [← he, heq, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · exact atlasLineInPair_le_pairing_ker

/-- Nondegeneracy on the left follows from the exact radical computation. -/
theorem atlasMiddlePairing_injective : Function.Injective atlasMiddlePairing := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm
  · intro v hv
    obtain ⟨w,rfl⟩ := atlasLineInPair.mkQ_surjective v
    have hw : w ∈ atlasLineInPair := by
      rw [← atlasPairHexPairing_ker]
      exact hv
    exact (Submodule.Quotient.mk_eq_zero atlasLineInPair).mpr hw
  · exact bot_le

private lemma jWord_mem_core (h : HexWord) : jWord h ∈ AtlasCore := by
  change (∑ p, jWord h p) = 0
  rw [Fintype.sum_prod_type]
  change (∑ i, ∑ k, j (h i) k) = 0
  simp

/-- Every binary functional on the hexacode is represented by a lifted ambient word. -/
theorem atlasMiddlePairing_surjective : Function.Surjective atlasMiddlePairing := by
  intro f
  obtain ⟨F, hF⟩ := Subspace.dualRestrict_surjective (W := hexacode) f
  let x : HexWord := (wordPolar.toDual wordPolar_nondegenerate).symm F
  let w : AtlasCore := ⟨jWord x, jWord_mem_core x⟩
  have hw : atlasCodeInCore.mkQ w ∈ atlasPairSpace :=
    ⟨w, jWord_evenColumns x, rfl⟩
  refine ⟨atlasLineInPair.mkQ ⟨atlasCodeInCore.mkQ w, hw⟩, ?_⟩
  ext h
  change binaryDot (jWord x) (jWord h.val) = f h
  rw [jWord_dot]
  change wordPolar ((wordPolar.toDual wordPolar_nondegenerate).symm F) h.val = f h
  rw [LinearMap.BilinForm.apply_toDual_symm_apply]
  exact DFunLike.congr_fun hF h

/-- The actual middle cocode quotient is the binary dual hexacode. -/
def atlasMiddleDualEquiv : AtlasMiddle ≃ₗ[ZMod 2] Module.Dual (ZMod 2) hexacode :=
  LinearEquiv.ofBijective atlasMiddlePairing
    ⟨atlasMiddlePairing_injective, atlasMiddlePairing_surjective⟩

/-- The equivalence is the constructed dot pairing, with no change of model. -/
lemma atlasMiddleDualEquiv_apply (v : AtlasMiddle) :
    atlasMiddleDualEquiv v = atlasMiddlePairing v := by
  rfl

/-- Evaluation on an even-column representative is the specified binary dot product. -/
lemma atlasMiddleDualEquiv_mk (w : AtlasCore) (hw : atlasColumnParity w.val = 0)
    (h : hexacode) :
    atlasMiddleDualEquiv
      (atlasLineInPair.mkQ ⟨atlasCodeInCore.mkQ w, ⟨w, hw, rfl⟩⟩) h =
        binaryDot w.val (jWord h.val) := by
  rfl

private lemma evenColumns_dot_eq_of_recovery (w : BinaryWord)
    (hw : atlasColumnParity w = 0) (z z' : C0) (hz : recoverHex z = recoverHex z') :
    binaryDot w z.val = binaryDot w z'.val := by
  have hk : (z - z').val ∈ R0 := (recoverHex_kernel _).mp (by
    rw [map_sub, hz, sub_self])
  obtain ⟨r, _, hr⟩ := hk
  apply sub_eq_zero.mp
  rw [← map_sub]
  change binaryDot w (z-z').val = 0
  rw [← hr]
  exact evenColumns_rho_dot w hw r

private lemma evenColumns_recover_pairing (w : BinaryWord)
    (hw : atlasColumnParity w = 0) (z : C0) :
    binaryDot w (jWord (recoverHex z).val) = binaryDot w z.val := by
  have he := evenColumns_dot_eq_of_recovery w hw (c0Equiv (recoverHex z, 0)) z
    (recoverHex_apply _ _)
  change binaryDot w (jWord (recoverHex z).val + rho (0 : Fin 6 → Bit)) =
    binaryDot w z.val at he
  simpa only [map_zero, add_zero] using he

private lemma dot_permutation (s : SextetStabilizer) (w z : BinaryWord) :
    binaryDot (atlasFullRepresentation s w) (atlasFullRepresentation s z) =
      binaryDot w z := by
  change (∑ p, w (s.val.val.symm p) * z (s.val.val.symm p)) = ∑ p, w p * z p
  exact Equiv.sum_comp s.val.val.symm (fun p => w p * z p)

private lemma evenColumns_pairing_action (s : SextetStabilizer) (w : BinaryWord)
    (hw : atlasColumnParity w = 0) (h : hexacode) :
    binaryDot (atlasFullRepresentation s w)
        (jWord (hexAction (sextetQuotient s) h).val) = binaryDot w (jWord h.val) := by
  obtain ⟨z, rfl⟩ := recoverHex_surjective h
  have hsw : atlasColumnParity (atlasFullRepresentation s w) = 0 := by
    ext i
    rw [atlasColumnParity_equivariant, hw]
    rfl
  rw [← recoverHex_equivariant, evenColumns_recover_pairing _ hsw,
    evenColumns_recover_pairing _ hw]
  exact dot_permutation s w z.val

/-- The pair-space pairing intertwines with the contragredient of the actual
hexacode action, including every affine stabilizer element. -/
theorem atlasPairHexPairing_equivariant (s : SextetStabilizer) (v : atlasPairSpace) :
    atlasPairHexPairing (atlasPairRepresentation s v) =
      Representation.dual (Representation.Hexacode.action.comp sextetQuotient) s
        (atlasPairHexPairing v) := by
  obtain ⟨w, hw, he⟩ := v.property
  apply LinearMap.ext
  intro h
  change atlasCocodeHexPairing (atlasCocodeRepresentation s v.val) h =
    atlasCocodeHexPairing v.val (hexAction (sextetQuotient s⁻¹) h)
  rw [← he, atlasCocodeRepresentation_mk, atlasCocodeHexPairing_mk,
    atlasCocodeHexPairing_mk]
  have hh : hexAction (sextetQuotient s) (hexAction (sextetQuotient s⁻¹) h) = h := by
    rw [map_inv, map_inv]
    exact (hexAction (sextetQuotient s)).apply_symm_apply h
  have hp := evenColumns_pairing_action s w.val hw (hexAction (sextetQuotient s⁻¹) h)
  rw [hh] at hp
  exact hp

/-- The perfect pairing respects the literal middle quotient action and the
binary dual of the sextet quotient's hexacode representation. -/
theorem atlasMiddleDualEquiv_equivariant (s : SextetStabilizer) (v : AtlasMiddle) :
    atlasMiddleDualEquiv (atlasMiddleRepresentation s v) =
      Representation.dual (Representation.Hexacode.action.comp sextetQuotient) s
        (atlasMiddleDualEquiv v) := by
  obtain ⟨w, rfl⟩ := atlasLineInPair.mkQ_surjective v
  exact atlasPairHexPairing_equivariant s w

end
end MathieuCode.SextetLayers
