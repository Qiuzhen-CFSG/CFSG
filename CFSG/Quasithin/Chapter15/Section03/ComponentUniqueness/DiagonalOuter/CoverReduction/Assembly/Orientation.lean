module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.Inputs

/-!
# Compatible relabelling of the two natural planes

Conjugating the wreath actor and its vector coordinates together reindexes
the planes. The plane stabilizer remains the kernel of the shift. This lets
the Sylow-normalizer construction use the centre plane chosen by the Borel
argument, without changing the projective quotient marking.
Source: Aschbacher--Smith, proof of 15.3.38, printed p.1136.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open LocalCover.SourceBorel
variable {G : Type*} [Group G]

/-- Change the actor and vector coordinates by the same genuine model action. -/
def reorient {M V : Subgroup G} (a : NaturalOrthogonalAction M V) (q : OrthogonalActor) :
    NaturalOrthogonalAction M V := by
  let _ := orthogonalAction
  exact {
    normalizes := a.normalizes
    coordinates := a.coordinates.trans (MulDistribMulAction.toMulAut _ _ q)
    actor := (MulAut.conj q).toMonoidHom.comp a.actor
    onto := (MulAut.conj q).surjective.comp a.onto
    compatible := by
      intro m v
      change q • a.coordinates (V.normalizerMonoidHom ⟨m, a.normalizes m.property⟩ v) =
        (q * a.actor m * q⁻¹) • (q • a.coordinates v)
      rw [a.compatible]
      simp only [mul_smul, inv_smul_smul] }

private theorem plane_mem {M V : Subgroup G} (a : NaturalOrthogonalAction M V)
    (i : OrthogonalPlaneIndex) (v : V) :
    (v : G) ∈ a.plane i ↔ a.coordinates v ∈ orthogonalCoordinatePlane i := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact (Subtype.ext he : w = v) ▸ hw
  · exact fun hv => ⟨v, hv, rfl⟩

/-- The plane transformation is the actual shift of the wreath element. -/
theorem reorient_plane [Finite G] {M V : Subgroup G}
    (a : NaturalOrthogonalAction M V) (q : OrthogonalActor) (i : OrthogonalPlaneIndex) :
    (reorient a q).plane (q.right * i) = a.plane i := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := orthogonalAction
  symm
  apply eq_of_le_of_card_ge
  · intro v hv
    let v₀ : V := ⟨v, a.plane_le i hv⟩
    apply (plane_mem (reorient a q) (q.right * i) v₀).mpr
    intro j hj
    change q.left j • a.coordinates v₀ (q.right⁻¹ * j) = 1
    rw [(plane_mem a i v₀).mp hv _ ?_, smul_one]
    exact fun he => hj (inv_mul_eq_iff_eq_mul.mp he)
  · rw [a.card_plane, (reorient a q).card_plane]

/-- Reindexing preserves the literal plane stabilizer. -/
theorem reorient_shift {M V : Subgroup G} (a : NaturalOrthogonalAction M V)
    (q : OrthogonalActor) (m : M) : ((reorient a q).actor m).right = (a.actor m).right := by
  change (q * a.actor m * q⁻¹).right = _
  change RegularWreathProduct.rightHom (q * a.actor m * q⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  change q.right * (a.actor m).right * q.right⁻¹ = (a.actor m).right
  calc
    _ = (a.actor m).right * (q.right * q.right⁻¹) := by ac_rfl
    _ = _ := by rw [mul_inv_cancel, mul_one]

/-- Produce coordinates with any specified original plane in the first slot. -/
theorem exists_oriented_action [Finite G] (d : CharacteristicTwo.LocalData G)
    (i : OrthogonalPlaneIndex) :
    ∃ a : NaturalOrthogonalAction d.M d.V,
      a.plane 1 = d.action.plane i ∧
      ∀ t : d.T, (t : G) ∈ d.S ↔ (a.actor (inclusion d.sylow_le t)).right = 1 := by
  let q : OrthogonalActor := RegularWreathProduct.inl i⁻¹
  refine ⟨reorient d.action q, ?_, ?_⟩
  · have hp := reorient_plane d.action q i
    simpa only [show q.right = i⁻¹ from rfl, inv_mul_cancel] using hp
  · intro t
    rw [reorient_shift]
    change ((t : G) ∈ (d.T : Subgroup G) ∧ (t : G) ∈ normalizer (d.V₁ : Set G)) ↔ _
    exact ⟨fun ht => (cyclic_mem_plane_normalizer_iff d.action
      (inclusion d.sylow_le t) 1).mp ht.2, fun ht => ⟨t.property,
      (cyclic_mem_plane_normalizer_iff d.action (inclusion d.sylow_le t) 1).mpr ht⟩⟩

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
