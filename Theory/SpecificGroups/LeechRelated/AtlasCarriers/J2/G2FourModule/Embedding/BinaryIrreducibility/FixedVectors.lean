module

public import Theory.Representation.G2NaturalTransitivity
public import Theory.AtlasPort.LinearGroups.G2.OrderChecks
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order

/-!
# No fixed nonzero vector for an embedded Hall--Janko group

The full natural G₂(4) action is transitive on its 4095 nonzero vectors.
Orbit--stabilizer and the proved ambient order give stabilizer order 61440.
An injective image of the actual degree-100 J₂ carrier, of order 604800,
cannot lie in such a stabilizer. This uses no simplicity assumption.

This is the fixed-vector obstruction used to establish irreducibility of the
restriction in Aschbacher--Smith, K.4.5, printed p.460. The concrete group,
octonion, and order certificates retain their ATLAS attribution in the imports.
-/

public noncomputable section
namespace Sporadic.LeechRelated.J2.G2FourModule.Embedding.BinaryIrreducibility
private abbrev F := GaloisField 2 2
private abbrev V := Atlas.G2.Natural.Space F
private abbrev M := Atlas.G2.Model F

@[instance_reducible] private def naturalMulAction : MulAction M V where
  smul g v := Atlas.G2.Natural.action F g v
  one_smul v := by change Atlas.G2.Natural.action F 1 v = v; simp
  mul_smul g h v := by
    change Atlas.G2.Natural.action F (g * h) v =
      Atlas.G2.Natural.action F g (Atlas.G2.Natural.action F h v)
    simp

attribute [local instance] naturalMulAction

private theorem orbit_eq_nonzero {v : V} (hv : v ≠ 0) :
    MulAction.orbit M v = {w : V | w ≠ 0} := by
  ext w
  constructor
  · rintro ⟨g, rfl⟩ h
    apply hv
    change Atlas.G2.Natural.action F g v = 0 at h
    have h' := congrArg (Atlas.G2.Natural.action F g⁻¹) h
    simpa using h'
  · intro hw
    obtain ⟨g, hg⟩ := Atlas.G2.Natural.action_transitive hv hw
    exact ⟨g, hg⟩

private theorem card_orbit {v : V} (hv : v ≠ 0) :
    Nat.card (MulAction.orbit M v) = 4095 := by
  classical
  rw [orbit_eq_nonzero hv]
  have hc : Nat.card V = 4096 := by
    rw [Nat.card_congr (Atlas.G2.Restricted.NaturalCoordinates.equiv F).toEquiv]
    rw [Nat.card_fun, Nat.card_fin, GaloisField.card 2 2 (by decide)]
    norm_num
  let : Finite V := Finite.of_injective _
    (Atlas.G2.Restricted.NaturalCoordinates.equiv F).injective
  let := Fintype.ofFinite V
  change Nat.card {w : V // w ≠ 0} = _
  simp only [Nat.card_eq_fintype_card] at hc ⊢
  simp [Fintype.card_subtype_compl, hc]

private theorem card_stabilizer {v : V} (hv : v ≠ 0) :
    Nat.card (MulAction.stabilizer M v) = 61440 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup M v)
  rw [Nat.card_prod, card_orbit hv, Atlas.G2.OrderChecks.four_order] at h
  omega

/-- No embedded copy of the actual J₂ carrier fixes a nonzero natural vector. -/
theorem fixed_vector_eq_zero
    (f : Carrier →* Atlas.G2.Model (GaloisField 2 2)) (hf : Function.Injective f)
    (v : Atlas.G2.Natural.Space (GaloisField 2 2))
    (hfix : ∀ j, Atlas.G2.Natural.action (GaloisField 2 2) (f j) v = v) : v = 0 := by
  by_contra hv
  let e : Carrier → MulAction.stabilizer M v := fun j => ⟨f j, hfix j⟩
  have he : Function.Injective e := fun a b h => hf (congrArg Subtype.val h)
  have hc := Nat.card_le_card_of_injective e he
  rw [ExceptionalParabolics.FirstParabolic.card_carrier, card_stabilizer hv] at hc
  omega

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.BinaryIrreducibility
