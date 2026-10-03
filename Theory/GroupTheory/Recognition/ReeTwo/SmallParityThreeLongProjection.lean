module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityThreeLongTransitions

/-!
# Quotient homomorphisms for the long rank-three parity candidates

Collected right multiplication by each defining generator preserves the proposed
carrier and adds its quotient coordinates. The finite generator certificates
propagate through monoid closure; in this finite group, monoid and subgroup
closure agree. This proves both carrier containment and multiplicativity without
checking every pair of elements.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified generators in
`SmallParityThreeGenerators` and coordinates in `SmallParityThreeLongCoordinates`.
-/

@[expose] public section

namespace ReeTwo.SylowModel.SmallParityLong
set_option maxRecDepth 32768
private theorem candidate_induction (c : Fin 3) (P : SylowModel → Prop)
    (hone : P 1)
    (hstep : ∀ x, x ∈ Candidate c → ∀ j, P x → P (x * smallParityThreeGenerator (index c) j))
    (x : SylowModel) (hx : x ∈ Candidate c) : P x := by
  have he : (Candidate c).toSubmonoid =
      Submonoid.closure (Set.range (smallParityThreeGenerator (index c))) := by
    rw [Candidate, smallParityThreeCandidate_eq_closure,
      Subgroup.closure_toSubmonoid_of_finite]
  have hx' : x ∈ Submonoid.closure (Set.range (smallParityThreeGenerator (index c))) :=
    he ▸ hx
  induction hx' using Submonoid.closure_induction_right with
  | one => exact hone
  | mul_right y hy z hz ih =>
    obtain ⟨j, rfl⟩ := hz
    have hy' : y ∈ (Candidate c).toSubmonoid := he.symm ▸ hy
    exact hstep y hy' j (ih hy')

theorem candidate_carrier (c : Fin 3) (x : SylowModel) (hx : x ∈ Candidate c) :
    carrier c x := by
  apply candidate_induction c (carrier c) _ _ x hx
  · exact (by decide +kernel : ∀ c, carrier c 1) c
  · intro y hy j ih
    rw [← ih]
    exact (carrier_coordinates_generator c _ j).1

private theorem coordinates_mul (c : Fin 3) (x y : SylowModel)
    (hx : x ∈ Candidate c) (hy : y ∈ Candidate c) :
    coordinates c (x * y) = coordinates c x * coordinates c y := by
  have hstep (z : SylowModel) (hz : z ∈ Candidate c) (j : Fin 9) :
      coordinates c (z * smallParityThreeGenerator (index c) j) = coordinates c z * coordinates c (smallParityThreeGenerator (index c) j) := by
    rw [← candidate_carrier c z hz]
    exact (carrier_coordinates_generator c _ j).2
  apply candidate_induction c (fun y => coordinates c (x*y) = coordinates c x * coordinates c y) _ _ y hy
  · rw [mul_one, show coordinates c 1 = 1 from (by decide +kernel : ∀ c, coordinates c 1 = 1) c, mul_one]
  · intro z hz j ih
    rw [← mul_assoc, hstep _ ((Candidate c).mul_mem hx hz), hstep z hz, ih, mul_assoc]

def projection (c : Fin 3) : Candidate c →* SmallParityThreeQuotient where
  toFun x := coordinates c x.val
  map_one' := (by decide +kernel : ∀ c, coordinates c 1 = 1) c
  map_mul' x y := by exact coordinates_mul c x.val y.val x.property y.property

end ReeTwo.SylowModel.SmallParityLong
