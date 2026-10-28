module
public import Theory.Representation.HexacodeAction.Field
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeZeroFibers
public import Theory.Representation.BinaryPermutation.SixPairsQuadratic

/-!
# Field points and coordinate pairs in the hexacode

A one-dimensional subspace over the actual four-element scalar field has
binary dimension two. If one of its nonzero words has a zero coordinate,
the hexacode minimum-distance theorem gives exactly one other zero. Scalar
multiplication preserves both zeros, so dimension identifies the point
with the whole double-zero plane. Otherwise the point is full-weight.

Double-zero planes are distinct, and the monomial action carries them
according to the actual coordinate permutation. Thus their stabilizers
are exactly the inverse images of the corresponding pair stabilizers.
This is the geometric part of the alternative-section argument for
Aschbacher–Smith 13.8.21(2), printed p.956 (PDF p.973).

The hexacode, monomial action and double-zero dimension theorem are the
attributed ATLAS constructions in the imported modules; their license
and source attribution remain in those modules. The present proofs use
the actual field structure from `HexacodeAction.Field`.
-/

@[expose] public section
open Atlas.Codes
namespace Representation.Hexacode
open BinaryPermutation.SixPairsQuadratic (Pair pairPerm)

/-- The binary scalar plane vanishing on the specified coordinate pair. -/
def zeroPairPlane (s : Pair) : Submodule Bit hexacode where
  carrier := {w | ∀ i ∈ s.val, w.val (hexPos i) = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw i hi; change v.val (hexPos i) + w.val (hexPos i) = 0; rw [hv i hi, hw i hi, zero_add]
  smul_mem' := by intro r w hw i hi; change r • w.val (hexPos i) = 0; rw [hw i hi, smul_zero]

theorem mem_zeroPairPlane (s : Pair) (w : hexacode) :
    w ∈ zeroPairPlane s ↔ ∀ i ∈ s.val, w.val (hexPos i) = 0 := Iff.rfl

theorem zeroPairPlane_eq_doubleZero (s : Pair) (i j : Fin 6) (hs : s.val = {i,j}) :
    zeroPairPlane s = hexDoubleZero (hexPos i) (hexPos j) := by
  ext w
  simp only [mem_zeroPairPlane, hs, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, hexDoubleZero, Submodule.mem_inf,
    LinearMap.mem_ker, hexCoordinate]
  rfl

theorem zeroPairPlane_finrank (s : Pair) : Module.finrank Bit (zeroPairPlane s) = 2 := by
  obtain ⟨i,j,hij,hs⟩ := Finset.card_eq_two.mp s.property
  rw [zeroPairPlane_eq_doubleZero s i j hs]
  exact hexDoubleZero_finrank _ _ (fun he => hij (hexIndexEquiv.symm.injective he))

theorem zeroPairPlane_coordinate (s : Pair) (i : Fin 6) :
    (∀ w ∈ zeroPairPlane s, w.val (hexPos i) = 0) ↔ i ∈ s.val := by
  constructor
  · intro h
    by_contra hi
    obtain ⟨j,k,hjk,hs⟩ := Finset.card_eq_two.mp s.property
    have hij : i ≠ j := by intro he; apply hi; simp [hs, he]
    have hik : i ≠ k := by intro he; apply hi; simp [hs, he]
    obtain ⟨w,hw⟩ := (hexDoubleZeroProjection_bijective (hexPos j) (hexPos k) (hexPos i)
      (fun he => hjk (hexIndexEquiv.symm.injective he))
      (fun he => hij (hexIndexEquiv.symm.injective he).symm)
      (fun he => hik (hexIndexEquiv.symm.injective he).symm)).2 a
    have hm : w.val ∈ zeroPairPlane s := by rw [zeroPairPlane_eq_doubleZero s j k hs]; exact w.property
    have hz := h w.val hm
    exact (by decide : (0 : K) ≠ a) (hz.symm.trans hw)
  · intro hi w hw
    exact hw i hi

theorem zeroPairPlane_injective : Function.Injective zeroPairPlane := by
  intro s t h
  apply Subtype.ext
  ext i
  rw [← zeroPairPlane_coordinate s i, ← zeroPairPlane_coordinate t i, h]

theorem fieldPoint_scalar_mem (D : Submodule F hexacode) :
    hexZ ∈ BinaryOffender.subspaceStabilizer action (D.restrictScalars Bit) := by
  intro w
  change action hexZ w ∈ D ↔ w ∈ D
  rw [scalar_eq_omega_smul]
  exact D.smul_mem_iff (by decide : omega ≠ 0)

theorem fieldPoint_binary_finrank (D : Submodule F hexacode)
    (hd : Module.finrank F D = 1) : Module.finrank Bit (D.restrictScalars Bit) = 2 := by
  have he : scalarSubmodule (D.restrictScalars Bit) (fieldPoint_scalar_mem D) = D := by
    ext w; rfl
  have h := scalarSubmodule_finrank (D.restrictScalars Bit) (fieldPoint_scalar_mem D)
  rw [he, hd] at h
  exact h.symm

private theorem field_smul_coordinate_zero (r : F) (w : hexacode) (i : HexIndex)
    (hw : w.val i = 0) : (r • w).val i = 0 := by
  rw [field_smul_formula]
  change r.re • w.val i + r.im • ((if i.2 = 0 then localKappa else localKappa⁻¹) (w.val i)) = 0
  rw [hw, map_zero, smul_zero, smul_zero, zero_add]

/-- Every field point is a full-weight plane or the double-zero plane of a pair. -/
theorem fieldPoint_full_or_pair (D : Submodule F hexacode) (hd : Module.finrank F D = 1) :
    IsFullWeightScalarPlane (D.restrictScalars Bit) ∨
      ∃ s : Pair, D.restrictScalars Bit = zeroPairPlane s := by
  classical
  by_cases hall : ∀ w : D.restrictScalars Bit, w ≠ 0 → hammingNorm w.val.val = 6
  · exact Or.inl ⟨fieldPoint_binary_finrank D hd, fieldPoint_scalar_mem D, hall⟩
  · right
    push Not at hall
    obtain ⟨w,hw,hweight⟩ := hall
    have hwn : w.val ≠ 0 := fun he => hw (Subtype.ext he)
    have hi : ∃ i : HexIndex, w.val.val i = 0 := by
      by_contra! h
      apply hweight
      simp [hammingNorm, h, HexIndex]
    obtain ⟨i,hi⟩ := hi
    obtain ⟨j,⟨hji,hj⟩,_⟩ := hexZeroCoordinate_unique_other_zero i ⟨w.val,hi⟩
      (fun he => hwn (congrArg Subtype.val he))
    let s : Pair := ⟨{hexIndexEquiv i, hexIndexEquiv j}, by
      simp [hexIndexEquiv.injective.ne hji.symm]⟩
    refine ⟨s, Submodule.eq_of_le_of_finrank_eq ?_ ?_⟩
    · intro v hv
      obtain ⟨r,hr⟩ := exists_smul_eq_of_finrank_eq_one hd
        (x := (⟨w.val,w.property⟩ : D)) (fun he => hwn (congrArg Subtype.val he)) ⟨v,hv⟩
      have hvw : v = r • w.val := (congrArg Subtype.val hr).symm
      rw [hvw, zeroPairPlane_eq_doubleZero s _ _ rfl]
      change (r • w.val).val (hexPos (hexIndexEquiv i)) = 0 ∧
        (r • w.val).val (hexPos (hexIndexEquiv j)) = 0
      simpa only [hexPos_index] using
        And.intro (field_smul_coordinate_zero r w.val i hi) (field_smul_coordinate_zero r w.val j hj)
    · rw [fieldPoint_binary_finrank D hd, zeroPairPlane_finrank]

/-- Zeros are permuted by the actual coordinate homomorphism. -/
theorem action_coordinate_zero (g : HexAutomorphisms) (w : hexacode) (i : Fin 6) :
    (action g w).val (hexPos i) = 0 ↔
      w.val (hexPos ((hexCoordinateSixHom g).symm i)) = 0 := by
  change g.val.localMap (hexPos i) (w.val (g.val.perm.symm (hexPos i))) = 0 ↔
    w.val (hexIndexEquiv.symm (hexIndexEquiv (g.val.perm.symm (hexPos i)))) = 0
  rw [hexIndexEquiv.symm_apply_apply]
  exact LinearEquiv.map_eq_zero_iff _

/-- Transport of the literal double-zero subspace under a monomial automorphism. -/
theorem zeroPairPlane_map (g : HexAutomorphisms) (s : Pair) :
    (zeroPairPlane s).map (action g) = zeroPairPlane (pairPerm (hexCoordinateSixHom g) s) := by
  ext w
  change w ∈ (zeroPairPlane s).map (hexAction g).toLinearMap ↔ _
  rw [Submodule.mem_map_equiv]
  have hinv : (hexAction g).symm = hexAction g⁻¹ := (map_inv hexAction g).symm
  rw [hinv]
  change (∀ i ∈ s.val, (action g⁻¹ w).val (hexPos i) = 0) ↔ _
  simp only [action_coordinate_zero, map_inv]
  change (∀ i ∈ s.val, w.val (hexPos (hexCoordinateSixHom g i)) = 0) ↔
    ∀ i ∈ s.val.map (hexCoordinateSixHom g).toEmbedding, w.val (hexPos i) = 0
  simp only [Finset.forall_mem_map, Equiv.toEmbedding_apply]

/-- The stabilizer of a double-zero plane is exactly the preimage of its pair stabilizer. -/
theorem zeroPairPlane_stabilizer_iff (g : HexAutomorphisms) (s : Pair) :
    g ∈ BinaryOffender.subspaceStabilizer action (zeroPairPlane s) ↔
      pairPerm (hexCoordinateSixHom g) s = s := by
  have hmap : g ∈ BinaryOffender.subspaceStabilizer action (zeroPairPlane s) ↔
      (zeroPairPlane s).map (action g) = zeroPairPlane s := by
    constructor
    · intro hg
      ext w
      constructor
      · rintro ⟨v,hv,rfl⟩
        exact (hg v).2 hv
      · intro hw
        refine ⟨action g⁻¹ w, ?_, ?_⟩
        · apply (hg (action g⁻¹ w)).1
          simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
            map_one, Module.End.one_apply] using hw
        · simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
            map_one, Module.End.one_apply]
    · intro he w
      constructor
      · intro hw
        have hh : action g w ∈ (zeroPairPlane s).map (action g) := he.symm ▸ hw
        obtain ⟨v,hv,hvw⟩ := hh
        exact (hexAction g).injective hvw ▸ hv
      · intro hw
        rw [← he]
        exact ⟨w,hw,rfl⟩
  rw [hmap, zeroPairPlane_map, zeroPairPlane_injective.eq_iff]

end Representation.Hexacode
