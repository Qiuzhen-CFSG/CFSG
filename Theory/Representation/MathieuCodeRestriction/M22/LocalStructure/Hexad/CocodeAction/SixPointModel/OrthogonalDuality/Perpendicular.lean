module
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.SixPointModel.OrthogonalDuality.DeletedDuality

/-!
# The marked pair perpendicular

Zero extension identifies the even six-coordinate words with the perpendicular
of the actual pair in the natural octad section. For surjectivity, subtract
the common value of the two pair coordinates; this changes only an octad
constant. The resulting perfect pairing computes both native cocode quotients.

Source: Aschbacher--Smith, H.15.2(2), printed pp.398--399.
-/
@[expose] public section
open scoped BigOperators
namespace MathieuCode.Hexad.CocodeAction.SixPointModel.OrthogonalDuality
noncomputable section
open BinaryPermutation

/-- The actual pair vector in the octad natural section. -/
def pairVector : natural O.val := coreToNatural O.val pairWord

/-- Perpendicular to the pair for the descended coordinate dot product. -/
def perpendicular : Submodule (ZMod 2) (natural O.val) :=
  (naturalPairing O.val pairVector).ker

lemma pairVector_cocode : (CocodeOctad.naturalEquiv O pairVector).val = m22PairClass :=
  (CocodeOctad.naturalEquiv_apply O pairWord).trans pairWord_cocode

private def coordinateEmbedding : H ↪ O.val :=
  ⟨inOctad, fun _ _ h => Subtype.ext (congrArg (fun i : O.val => i.val) h)⟩

lemma sum_octad {A : Type*} [AddCommMonoid A] (v : O.val → A) :
    ∑ i, v i = v anchor + v partner + ∑ i : H, v (inOctad i) := by
  have he : (Finset.univ : Finset O.val) =
      insert anchor (insert partner (Finset.univ.map coordinateEmbedding)) := by decide +kernel
  have ha : anchor ∉ insert partner (Finset.univ.map coordinateEmbedding) := by decide +kernel
  have hb : partner ∉ Finset.univ.map coordinateEmbedding := by decide +kernel
  rw [he, Finset.sum_insert ha, Finset.sum_insert hb, Finset.sum_map]
  simp only [add_assoc]
  rfl

/-- Extend a six-coordinate word by zero at the marked pair. -/
def zeroExtendFull : BinaryPermutation.Full H →ₗ[ZMod 2] BinaryPermutation.Full O.val where
  toFun v i := if hi : i.val ∈ coordinates then v ⟨i.val, hi⟩ else 0
  map_add' v w := by ext i; by_cases hi : i.val ∈ coordinates <;> simp [hi]
  map_smul' c v := by ext i; by_cases hi : i.val ∈ coordinates <;> simp [hi]

@[simp] lemma zeroExtendFull_inOctad (v : BinaryPermutation.Full H) (i : H) :
    zeroExtendFull v (inOctad i) = v i := by simp [zeroExtendFull, inOctad, i.property]

@[simp] lemma zeroExtendFull_anchor (v : BinaryPermutation.Full H) : zeroExtendFull v anchor = 0 := by
  simp [zeroExtendFull, anchor, show (0 : Fin 24) ∉ coordinates by decide +kernel]

@[simp] lemma zeroExtendFull_partner (v : BinaryPermutation.Full H) : zeroExtendFull v partner = 0 := by
  simp [zeroExtendFull, partner, show (9 : Fin 24) ∉ coordinates by decide +kernel]

lemma sum_zeroExtendFull (v : BinaryPermutation.Full H) : ∑ i, zeroExtendFull v i = ∑ i, v i := by
  rw [sum_octad]
  simp

/-- Even zero extension into the octad core. -/
def zeroExtend : core H →ₗ[ZMod 2] core O.val :=
  zeroExtendFull.restrict (fun v hv => by
    change (∑ i, zeroExtendFull v i) = 0
    rw [sum_zeroExtendFull]
    exact hv)

lemma restrict_zeroExtend (v : core H) : restrict (zeroExtend v) = v.val := by
  ext i
  exact zeroExtendFull_inOctad v.val i

lemma pairing_pair (v : core O.val) :
    naturalPairing O.val pairVector (coreToNatural O.val v) = v.val partner + v.val anchor := by
  rw [pairVector, naturalPairing_apply_core]
  change dotProduct (Pi.single partner 1 + Pi.single anchor 1) v.val = _
  simp [add_dotProduct]

lemma mem_perpendicular_iff (v : core O.val) :
    coreToNatural O.val v ∈ perpendicular ↔ v.val partner = v.val anchor := by
  change naturalPairing O.val pairVector (coreToNatural O.val v) = 0 ↔ _
  rw [pairing_pair]
  constructor
  · intro h
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h
  · intro h
    simp [h]

/-- The zero-extension map into the actual perpendicular. -/
def coreToPerpendicular : core H →ₗ[ZMod 2] perpendicular :=
  ((coreToNatural O.val).comp zeroExtend).codRestrict perpendicular (fun v => by
    apply (mem_perpendicular_iff _).mpr
    exact (zeroExtendFull_partner v.val).trans (zeroExtendFull_anchor v.val).symm)

lemma coreToPerpendicular_injective : Function.Injective coreToPerpendicular := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro v hv
  have he : (constants O.val).mkQ (zeroExtend v).val = 0 :=
    congrArg (fun u : perpendicular => u.val.val) hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((Submodule.Quotient.mk_eq_zero _).mp he)
  have hc0 : c = 0 := by
    have h := congrFun hc anchor
    simpa [allOne, show (zeroExtend v).val anchor = 0 from zeroExtendFull_anchor v.val] using h
  have hz : (zeroExtend v).val = 0 := by simpa [hc0] using hc.symm
  apply Subtype.ext
  have h := congrArg restrict (show zeroExtend v = 0 from Subtype.ext hz)
  simpa [restrict_zeroExtend] using h

/-- Subtracting the common pair coordinate produces an even six-coordinate word. -/
lemma coreToPerpendicular_surjective : Function.Surjective coreToPerpendicular := by
  intro v
  obtain ⟨w, hw⟩ := coreToNatural_surjective v.val
  have hp : w.val partner = w.val anchor := (mem_perpendicular_iff w).mp (hw ▸ v.property)
  let c : core O.val := ⟨allOne O.val, by
    change augmentation O.val (allOne O.val) = 0
    rw [augmentation_allOne]
    decide +kernel⟩
  let z := w - w.val anchor • c
  have ha : z.val anchor = 0 := by simp [z, c, allOne]
  have hb : z.val partner = 0 := by simp [z, c, allOne, hp]
  have hz : restrict z ∈ core H := by
    have hs := z.property
    change (∑ i, z.val i) = 0 at hs
    rw [sum_octad, ha, hb, zero_add, zero_add] at hs
    exact hs
  let u : core H := ⟨restrict z, hz⟩
  have hu : zeroExtend u = z := by
    apply Subtype.ext
    funext i
    change (if hi : i.val ∈ coordinates then (restrict z) ⟨i.val, hi⟩ else 0) = z.val i
    split_ifs with hi
    · rfl
    · have hi' : i = anchor ∨ i = partner := by
        have hm : i.val ∈ m22Pair := by
          by_contra h
          exact hi (Finset.mem_sdiff.mpr ⟨i.property, h⟩)
        simp only [m22Pair, Finset.mem_insert, Finset.mem_singleton] at hm
        exact hm.imp (fun h => Subtype.ext h) (fun h => Subtype.ext h)
      rcases hi' with rfl | rfl
      · exact ha.symm
      · exact hb.symm
  refine ⟨u, Subtype.ext ?_⟩
  change coreToNatural O.val (zeroExtend u) = v.val
  rw [hu, show z = w - w.val anchor • c from rfl, map_sub, map_smul]
  have hc : coreToNatural O.val c = 0 := by
    apply Subtype.ext
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.subset_span (Set.mem_singleton _)
  rw [hc, smul_zero, sub_zero, hw]

/-- The actual orthogonal module, rather than an assumed self-dual cocode module. -/
def corePerpendicularEquiv : core H ≃ₗ[ZMod 2] perpendicular :=
  LinearEquiv.ofBijective coreToPerpendicular
    ⟨coreToPerpendicular_injective, coreToPerpendicular_surjective⟩

lemma corePerpendicularEquiv_apply (v : core H) :
    (corePerpendicularEquiv v).val = coreToNatural O.val (zeroExtend v) := rfl

lemma pairing_zeroExtend (v : core O.val) (w : core H) :
    naturalPairing O.val (coreToNatural O.val v) (coreToNatural O.val (zeroExtend w)) =
      ∑ i, v.val (inOctad i) * w.val i := by
  rw [naturalPairing_apply_core, sum_octad]
  change v.val anchor * zeroExtendFull w.val anchor +
    v.val partner * zeroExtendFull w.val partner +
    (∑ i, v.val (inOctad i) * zeroExtendFull w.val (inOctad i)) = _
  simp

/-- Perfect pairing of the actual cocode image with the pair perpendicular. -/
def imagePerpendicularDualEquiv : imageSpace ≃ₗ[ZMod 2]
    Module.Dual (ZMod 2) perpendicular :=
  imageCoreDualEquiv.trans corePerpendicularEquiv.symm.dualMap

/-- Compatibility with restriction and both native cocode quotient maps. -/
lemma imagePerpendicularDualEquiv_apply (v : core O.val) (w : core H) :
    imagePerpendicularDualEquiv ⟨toM22 v, LinearMap.mem_range_self _ _⟩
        (corePerpendicularEquiv w) =
      naturalPairing O.val (coreToNatural O.val v) (corePerpendicularEquiv w).val := by
  change imageCoreDualEquiv ⟨toM22 v, LinearMap.mem_range_self _ _⟩
      (corePerpendicularEquiv.symm (corePerpendicularEquiv w)) = _
  rw [LinearEquiv.symm_apply_apply, imageCoreDualEquiv_apply, corePerpendicularEquiv_apply,
    pairing_zeroExtend]


/-- Zero extension intertwines the actual marked octad and hexad permutations. -/
lemma zeroExtend_equivariant {G : Type*} [Group G]
    (f : G →* m22PairStabilizer) (g : Stabilizer f) (v : core H) :
    zeroExtend (BinaryPermutation.coreRepresentation H (coordinateAction f g) v) =
      BinaryPermutation.coreRepresentation O.val (CocodeOctad.coordinateAction O (octadHom f g)) (zeroExtend v) := by
  apply Subtype.ext
  funext i
  let p := CocodeOctad.coordinateAction O (octadHom f g)
  have hm : (p.symm i).val ∈ coordinates ↔ i.val ∈ coordinates := by
    have h := preserves_coordinates f g (p.symm i).val
    have he : (f g.val).val.val (p.symm i).val = i.val :=
      congrArg Subtype.val (p.apply_symm_apply i)
    rw [he] at h
    exact h.symm
  change zeroExtendFull (BinaryPermutation.coreRepresentation H (coordinateAction f g) v).val i =
    zeroExtendFull v.val (p.symm i)
  by_cases hi : i.val ∈ coordinates
  · simp only [zeroExtendFull, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hi, dif_pos (hm.mpr hi)]
    rfl
  · simp only [zeroExtendFull, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hi,
      dif_neg (mt hm.mp hi)]

lemma perpendicular_invariant {G : Type*} [Group G]
    (f : G →* m22PairStabilizer) (g : Stabilizer f)
    {v : natural O.val} (hv : v ∈ perpendicular) :
    naturalRepresentation O.val (CocodeOctad.coordinateAction O (octadHom f g)) v ∈ perpendicular := by
  obtain ⟨w, hw⟩ := corePerpendicularEquiv.surjective ⟨v, hv⟩
  have he := congrArg Subtype.val hw
  change coreToNatural O.val (zeroExtend w) = v at he
  rw [← he, ← coreToNatural_equivariant, ← zeroExtend_equivariant f g]
  exact (coreToPerpendicular _).property

/-- The restriction of the actual octad action to the perpendicular space. -/
def perpendicularRepresentation {G : Type*} [Group G] (f : G →* m22PairStabilizer) :
    Representation (ZMod 2) (Stabilizer f) perpendicular where
  toFun g := (naturalRepresentation O.val (CocodeOctad.coordinateAction O (octadHom f g))).restrict
    (fun _ hv => perpendicular_invariant f g hv)
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change naturalRepresentation O.val (CocodeOctad.coordinateAction O (octadHom f 1)) v.val = v.val
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change naturalRepresentation O.val (CocodeOctad.coordinateAction O (octadHom f (g * h))) v.val =
      naturalRepresentation O.val (CocodeOctad.coordinateAction O (octadHom f g))
        (naturalRepresentation O.val (CocodeOctad.coordinateAction O (octadHom f h)) v.val)
    simp [map_mul]

lemma corePerpendicularEquiv_equivariant {G : Type*} [Group G]
    (f : G →* m22PairStabilizer) (g : Stabilizer f) (v : core H) :
    corePerpendicularEquiv (BinaryPermutation.coreRepresentation H (coordinateAction f g) v) =
      perpendicularRepresentation f g (corePerpendicularEquiv v) := by
  apply Subtype.ext
  change coreToNatural O.val (zeroExtend _) = naturalRepresentation O.val _ (coreToNatural O.val _)
  rw [zeroExtend_equivariant, coreToNatural_equivariant]

/-- The perfect pairing intertwines the native cocode action contragrediently. -/
lemma imagePerpendicularDualEquiv_equivariant {G : Type*} [Group G]
    (f : G →* m22PairStabilizer) (g : Stabilizer f) (v : imageSpace) :
    imagePerpendicularDualEquiv (imageRepresentation f g v) =
      (perpendicularRepresentation f).dual g (imagePerpendicularDualEquiv v) := by
  apply LinearMap.ext
  intro w
  obtain ⟨u, rfl⟩ := corePerpendicularEquiv.surjective w
  change imageCoreDualEquiv (imageRepresentation f g v)
      (corePerpendicularEquiv.symm (corePerpendicularEquiv u)) =
    imageCoreDualEquiv v (corePerpendicularEquiv.symm
      (perpendicularRepresentation f g⁻¹ (corePerpendicularEquiv u)))
  rw [← corePerpendicularEquiv_equivariant, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply, imageCoreDualEquiv_equivariant]
  change imageCoreDualEquiv v (BinaryPermutation.coreRepresentation H ((coordinateAction f g)⁻¹) u) =
    imageCoreDualEquiv v (BinaryPermutation.coreRepresentation H (coordinateAction f g⁻¹) u)
  rw [map_inv (coordinateAction f)]

/-- The quotient of the actual native octad cocode space into its M22 image. -/
def octadToImage : natural O.val →ₗ[ZMod 2] imageSpace :=
  ((m22PairLine.mkQ.comp (supportedPairSpace O.val).subtype).comp
    (CocodeOctad.naturalEquiv O).toLinearMap).codRestrict imageSpace (fun v => by
      rw [show imageSpace = (supportedPairSpace O.val).map m22PairLine.mkQ from range_toM22]
      exact Submodule.mem_map_of_mem (CocodeOctad.naturalEquiv O v).property)

lemma octadToImage_apply_core (v : core O.val) :
    octadToImage (coreToNatural O.val v) = ⟨toM22 v, LinearMap.mem_range_self _ _⟩ := by
  apply Subtype.ext
  change m22PairLine.mkQ (CocodeOctad.naturalEquiv O (coreToNatural O.val v)).val = _
  have he : (CocodeOctad.naturalEquiv O (coreToNatural O.val v)).val =
      CocodeOctad.toCocode O.val v := CocodeOctad.naturalEquiv_apply O v
  rw [he]
  rfl

/-- The perfect pairing is the original octad dot product through both quotient maps. -/
lemma imagePerpendicularDualEquiv_octad (v : natural O.val) (w : perpendicular) :
    imagePerpendicularDualEquiv (octadToImage v) w = naturalPairing O.val v w.val := by
  obtain ⟨a, rfl⟩ := coreToNatural_surjective v
  obtain ⟨b, rfl⟩ := corePerpendicularEquiv.surjective w
  rw [octadToImage_apply_core, imagePerpendicularDualEquiv_apply]

lemma finrank_perpendicular : Module.finrank (ZMod 2) perpendicular = 5 := by
  rw [← corePerpendicularEquiv.finrank_eq, finrank_core, card_H]


end
end MathieuCode.Hexad.CocodeAction.SixPointModel.OrthogonalDuality
