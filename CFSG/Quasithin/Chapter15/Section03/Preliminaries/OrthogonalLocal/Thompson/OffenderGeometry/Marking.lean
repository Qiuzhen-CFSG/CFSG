module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Thompson.OffenderGeometry.Dihedral

/-!
# Transport of orthogonal offender control through a compatible marking

An injective marking of the dihedral Sylow, together with an equivariant
bijection of the literal vector module, preserves both subgroup orders and
fixed-vector orders. Pulling an elementary offender back to the standard
model therefore places it in the marked base four-group. A nontrivial
such offender normally generates that base. The same vector bijection
transports the pointwise-fixer bound. Finally, an elementary subgroup of
order four with four fixed vectors equals the marked base by containment
and equality of orders.

Source: the finite natural-action step in Aschbacher–Smith 15.3.5,
combined manuscript (1 March 2004), printed p.1122.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.OrthogonalOffenderGeometry
local instance : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction
open DihedralGroup

variable (f : D →* OrthogonalActor) (hf : Function.Injective f)
    (e : OrthogonalVector ≃ OrthogonalVector)
    (he : ∀ x v, f x • e v = e (wreathTwoDihedralHom x • v))

include he in
private theorem marked_mem_fixed (H : Subgroup D) (v : OrthogonalVector) :
    e v ∈ orthogonalFixedVectors (H.map f) ↔ v ∈ dihedralFixed H := by
  rw [dihedral_mem_fixed_iff]
  constructor
  · intro hv x hx
    exact e.injective ((he x v).symm.trans (hv _ (mem_map_of_mem _ hx)))
  · rintro hv a ⟨x,hx,rfl⟩
    exact (he x v).trans (congrArg e (hv x hx))

private def markedFixedEquiv (H : Subgroup D) :
    dihedralFixed H ≃ orthogonalFixedVectors (H.map f) :=
  Equiv.subtypeEquiv e (fun v => (marked_mem_fixed f e he H v).symm)

include hf he in
private theorem marked_preimage_offender (R : Subgroup OrthogonalActor)
    (hR : R ≤ f.range) (hRe : IsElementaryAbelian 2 R)
    (hbound : 16 ≤ Nat.card (orthogonalFixedVectors R) * Nat.card R) :
    R.comap f ≤ dihedralBase ∧ (R.comap f = ⊥ ∨ sr 1 ∈ R.comap f ∨ sr 3 ∈ R.comap f) := by
  let _ := hRe
  have hfixed : Nat.card (dihedralFixed (R.comap f)) = Nat.card (orthogonalFixedVectors R) := by
    have h := Nat.card_congr (markedFixedEquiv f e he (R.comap f))
    rwa [map_comap_eq_self hR] at h
  have hcard : Nat.card (R.comap f) = Nat.card R := by
    calc
      Nat.card (R.comap f) = Nat.card ((R.comap f).map f) := (card_map_of_injective hf).symm
      _ = Nat.card R := by rw [map_comap_eq_self hR]
  apply dihedral_offender
  · intro x hx
    apply hf
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (f x) hx
  · rwa [hfixed, hcard]

include hf he in
/-- Offender control is preserved by any marking compatible with the natural action. -/
theorem marked_offender_control : OrthogonalOffenderControl f.range (dihedralBase.map f) := by
  intro R hR hRe hb
  obtain ⟨hle, hseed⟩ := marked_preimage_offender f hf e he R hR hRe hb
  constructor
  · have h := map_mono (f := f) hle
    rwa [map_comap_eq_self hR] at h
  · intro hne N hRN _ hnorm
    have hseed' : sr 1 ∈ N.comap f ∨ sr 3 ∈ N.comap f := by
      rcases hseed with hbot | ha | hb
      · exfalso
        apply hne
        rw [← map_comap_eq_self hR, hbot, Subgroup.map_bot]
      · exact Or.inl (hRN ha)
      · exact Or.inr (hRN hb)
    apply map_le_iff_le_comap.mpr
    apply dihedral_base_le _ _ hseed'
    intro x y hy
    change f (x * y * x⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp (hnorm ⟨x,rfl⟩) (f y)).mp hy

include he in
/-- The compatible marking also transports the pointwise-fixer bound. -/
theorem marked_fixer_control :
    f.range ⊓ orthogonalFixedSpaceFixer (dihedralBase.map f) ≤ dihedralBase.map f := by
  rintro a ⟨⟨x,rfl⟩,ha⟩
  apply mem_map_of_mem
  apply dihedral_fixer
  intro v hv
  have hfix : f x • e v = e v := by
    change f x ∈ fixingSubgroup OrthogonalActor (orthogonalFixedVectors (dihedralBase.map f) : Set OrthogonalVector) at ha
    rw [mem_fixingSubgroup_iff] at ha
    exact ha (e v) ((marked_mem_fixed f e he dihedralBase v).mpr hv)
  exact e.injective ((he x v).symm.trans hfix)

include hf he in
/-- The order-four subgroup with four fixed vectors is the marked base four-group. -/
theorem marked_base_eq (Q : Subgroup OrthogonalActor) (hQ : Q ≤ f.range)
    (hQe : IsElementaryAbelian 2 Q) (hQc : Nat.card Q = 4)
    (hQf : Nat.card (orthogonalFixedVectors Q) = 4) : Q = dihedralBase.map f := by
  have hbound : 16 ≤ Nat.card (orthogonalFixedVectors Q) * Nat.card Q := by
    rw [hQf,hQc]
  exact eq_of_le_of_card_ge ((marked_offender_control f hf e he) Q hQ hQe hbound).1
    (by rw [card_map_of_injective hf, dihedral_base_card, hQc])

end CFSG.Quasithin.Chapter15.Section03.OrthogonalOffenderGeometry

end
