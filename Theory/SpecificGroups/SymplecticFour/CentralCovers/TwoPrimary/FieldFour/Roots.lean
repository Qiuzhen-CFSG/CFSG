module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.FieldFour.Geometry
public import Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual.Weyl
public import Theory.GroupTheory.Commutator.CentralExtensionPairing

/-!
# Additive root sections including the field of four elements

A torus which moves one root and fixes another kills the commutator between
arbitrary lifts of the two commuting roots. The x₂–x₆ commutator projects to
x₀(v)x₄(v). A lift of either central root commutes with both inputs and with
the other central root, so its commutator with its own root also vanishes.
Weyl conjugation proves abelianness of all eight root preimages.

Commutating a root lift with a nontrivial scalar torus then gives an additive
section. Independence of choices of lifts also makes this section equivariant
under the whole diagonal torus. The argument requires only |F| > 2 and works
in particular over F₄, where scalar invariance on one root alone is insufficient.

Source: the type-C₂ central-extension calculation underlying Aschbacher–Smith
I.1.3, printed p.407, and GLS3 §6.1. These sections are used by the positive-root
relation calculation in `FieldFour.Relations`.
-/

public section

open Matrix
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.FieldFour

variable {F : Type*} [Field F]

variable {E : Type*} [Group E]

private theorem commute_commutator_of_images (f : E →* Sp F)
    (hk : f.ker ≤ Subgroup.center E) {a b w : E}
    (ha : Commute (f w) (f a)) (hb : Commute (f w) (f b)) :
    Commute w ⁅a,b⁆ := by
  apply (mul_inv_eq_iff_eq_mul).mp
  rw [conjugate_commutatorElement]
  apply CentralExtension.commutator_eq_of_image_eq f hk
  · simpa only [map_mul, map_inv] using ha.mul_inv_cancel
  · simpa only [map_mul, map_inv] using hb.mul_inv_cancel

/-- Arbitrary lifts of each distinct commuting positive-root pair commute. -/
theorem commuting_pair_lifts [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (f : E →* Sp F) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    {r s : Fin 8} (h : CommutingPair r s) {x y : E} {v w : F}
    (hx : f x = rootElement r v) (hy : f y = rootElement s w) : Commute x y := by
  obtain ⟨a,b,hs,hr⟩ := separating_torus (F := F) hF h
  let c : F := diagonalWeight r a b
  have hc : c - 1 ≠ 0 := sub_ne_zero.mpr (fun he => hr (Units.ext he))
  obtain ⟨d,hd⟩ := hf (diagonalTorus a b)
  obtain ⟨z,hz⟩ := hf (rootElement r ((c-1)⁻¹*v))
  have hproj : f ⁅d,z⁆ = rootElement r v := by
    rw [map_commutatorElement, commutatorElement_def, hd, hz, diagonal_conjugate]
    have hinv (t : F) : (rootElement r t)⁻¹ = rootElement r (-t) :=
      ((RootSubgroup.parameter (F := F) r).map_inv (.ofAdd t)).symm
    rw [hinv, RootSubgroup.element_add]
    congr 1
    change c*((c-1)⁻¹*v) + -((c-1)⁻¹*v) = v
    calc
      _ = (c-1)*((c-1)⁻¹*v) := by ring
      _ = v := mul_inv_cancel_left₀ hc v
  have hcomm : Commute y ⁅d,z⁆ := by
    apply commute_commutator_of_images f hk
    · rw [hy, hd]
      apply Commute.symm
      apply (mul_inv_eq_iff_eq_mul).mp
      rw [diagonal_conjugate, hs]
      simp
    · rw [hy,hz]
      exact (matrix_commute h _ _).symm
  apply commutatorElement_eq_one_iff_commute.mp
  rw [CentralExtension.commutator_eq_of_image_eq f hk (hx.trans hproj.symm) rfl]
  exact hcomm.symm.commutator_eq

private theorem commute_of_image_eq (f : E →* Sp F)
    (hk : f.ker ≤ Subgroup.center E) {x y z : E} (h : Commute x y)
    (hz : f z = f y) : Commute x z := by
  apply commutatorElement_eq_one_iff_commute.mp
  rw [CentralExtension.commutator_eq_of_image_eq f hk rfl hz]
  exact h.commutator_eq

/-- The mixed-root commutator eliminates the individual-root obstruction for
roots 0 and 4, the central roots of the standard unipotent subgroup. -/
theorem central_root_preimage_commute [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) (f : E →* Sp F) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) {r : Fin 8} (hr : r = 0 ∨ r = 4)
    {x y : E} {u v : F} (hx : f x = rootElement r u) (hy : f y = rootElement r v) :
    Commute x y := by
  obtain ⟨a,ha⟩ := hf (rootElement 2 v)
  obtain ⟨b,hb⟩ := hf (rootElement 6 1)
  have hab : f ⁅a,b⁆ = rootElement 0 v * rootElement 4 v := by
    rw [map_commutatorElement, ha, hb, matrix_commutator]
    simp
  rcases hr with rfl | rfl
  · obtain ⟨d,hd⟩ := hf (rootElement 4 v)
    have hxa : Commute x a := commuting_pair_lifts hF f hf hk
      (by simp [CommutingPair]) hx ha
    have hxb : Commute x b := (commuting_pair_lifts hF f hf hk
      (by simp [CommutingPair]) hb hx).symm
    have hxd : Commute x d := commuting_pair_lifts hF f hf hk
      (by simp [CommutingPair]) hx hd
    apply commute_of_image_eq f hk
      ((hxa.mul_right hxb |>.mul_right hxa.inv_right |>.mul_right hxb.inv_right).mul_right hxd.inv_right)
    change f y = f (⁅a,b⁆ * d⁻¹)
    rw [map_mul, map_inv, hab, hd, hy, mul_inv_cancel_right]
  · obtain ⟨d,hd⟩ := hf (rootElement 0 v)
    have hxa : Commute x a := commuting_pair_lifts hF f hf hk
      (by simp [CommutingPair]) hx ha
    have hxb : Commute x b := (commuting_pair_lifts hF f hf hk
      (by simp [CommutingPair]) hb hx).symm
    have hxd : Commute x d := (commuting_pair_lifts hF f hf hk
      (by simp [CommutingPair]) hd hx).symm
    apply commute_of_image_eq f hk
      ((hxa.mul_right hxb |>.mul_right hxa.inv_right |>.mul_right hxb.inv_right).mul_right hxd.inv_right)
    change f y = f (⁅a,b⁆ * d⁻¹)
    rw [map_mul, map_inv, hab, hd, hy]
    exact (matrix_commute (by simp [CommutingPair]) v v).mul_inv_cancel.symm

/-- The full preimage of every matrix root subgroup is abelian. -/
theorem root_preimage_commute [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) (f : E →* Sp F) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (r : Fin 8) {x y : E}
    (hx : f x ∈ RootSubgroup.group r) (hy : f y ∈ RootSubgroup.group r) :
    Commute x y := by
  obtain ⟨w,hw⟩ := RootNormalizerResidual.exists_root_conjugation (F := F) r
  rw [← hw] at hx hy
  obtain ⟨v,hv,hvx⟩ := hx
  obtain ⟨z,hz,hzy⟩ := hy
  obtain ⟨a,ha⟩ := hf w
  obtain ⟨b,hb⟩ := hf v
  obtain ⟨c,hc⟩ := hf z
  obtain ⟨s,hs⟩ := (RootSubgroup.mem_group_iff _ _).mp hv
  obtain ⟨t,ht⟩ := (RootSubgroup.mem_group_iff _ _).mp hz
  have hbc : Commute b c := central_root_preimage_commute hF f hf hk
    (by split <;> simp) (hb.trans hs.symm) (hc.trans ht.symm)
  apply commutatorElement_eq_one_iff_commute.mp
  rw [CentralExtension.commutator_eq_of_image_eq f hk
    (show f x = f (a*b*a⁻¹) by
      simpa only [map_mul, map_inv, ha, hb, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply] using hvx.symm)
    (show f y = f (a*c*a⁻¹) by
      simpa only [map_mul, map_inv, ha, hc, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply] using hzy.symm)]
  exact (hbc.conj a).commutator_eq

/-- An additive root section equivariant under the literal diagonal torus. -/
structure RootSection (f : E →* Sp F) (r : Fin 8) where
  lift : Multiplicative F →* E
  project : f.comp lift = RootSubgroup.parameter r
  equivariant : ∀ (a b : Fˣ) (d : E), f d = diagonalTorus a b → ∀ x : F,
    d * lift (.ofAdd x) * d⁻¹ = lift (.ofAdd ((diagonalWeight r a b : F)*x))

/-- Every root has an additive section with its exact diagonal-torus action. -/
theorem exists_root_section [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (f : E →* Sp F) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (r : Fin 8) : Nonempty (RootSection f r) := by
  classical
  have hc : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := (Finite.one_lt_card_iff_nontrivial).mp hc
  obtain ⟨c, hc⟩ := exists_ne (1 : Fˣ)
  have hc1 : (c : F) ≠ 1 := fun h => hc (Units.ext h)
  obtain ⟨t, ht⟩ := RootTori.weight_surjective r c
  obtain ⟨a, ha⟩ := hf (RootTori.element r t)
  choose b hb using fun x : F => hf (rootElement r x)
  let δ : F := (c : F) - 1
  have hδ : δ ≠ 0 := sub_ne_zero.mpr hc1
  let s : F → E := fun x => ⁅a, b (δ⁻¹ * x)⁆
  have hs (x : F) : f (s x) = rootElement r x := by
    dsimp [s]
    rw [map_commutatorElement, commutatorElement_def, ha, hb, RootTori.conjugate, ht]
    have hinv (z : F) : (rootElement r z)⁻¹ = rootElement r (-z) :=
      ((RootSubgroup.parameter (F := F) r).map_inv (.ofAdd z)).symm
    rw [hinv, RootSubgroup.element_add]
    congr 1
    calc
      (c : F) * (δ⁻¹ * x) + -(δ⁻¹ * x) = δ * (δ⁻¹ * x) := by dsimp [δ]; ring
      _ = x := mul_inv_cancel_left₀ hδ x
  have hs0 : s 0 = 1 := by
    dsimp [s]
    rw [mul_zero]
    have h0 : f (b 0) = f 1 := by rw [hb, RootSubgroup.element_zero, map_one]
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl h0]
    simp
  have hsadd (x y : F) : s (x + y) = s x * s y := by
    have hsum : f (b (δ⁻¹ * (x + y))) = f (b (δ⁻¹ * x) * b (δ⁻¹ * y)) := by
      rw [map_mul, hb, hb, hb, RootSubgroup.element_add, mul_add]
    have hcomm : Commute (b (δ⁻¹ * x)) (s y) :=
      root_preimage_commute hF f hf hk r
        (by rw [hb]; exact (RootSubgroup.mem_group_iff r _).mpr ⟨_, rfl⟩)
        (by rw [hs]; exact (RootSubgroup.mem_group_iff r _).mpr ⟨_, rfl⟩)
    change ⁅a, b (δ⁻¹ * (x + y))⁆ = _
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl hsum,
      commutatorElement_mul_right_eq_mul_conj]
    change s x * b (δ⁻¹ * x) * s y * (b (δ⁻¹ * x))⁻¹ = _
    rw [mul_assoc (s x), hcomm.eq, ← mul_assoc, mul_assoc (s x * s y), mul_inv_cancel, mul_one]
  refine ⟨⟨{ toFun x := s x.toAdd, map_one' := hs0, map_mul' x y := hsadd x.toAdd y.toAdd },
    ?_, ?_⟩⟩
  · apply MonoidHom.ext
    intro x
    exact hs x.toAdd
  · intro u v d hd x
    change d * ⁅a,b (δ⁻¹*x)⁆ * d⁻¹ = ⁅a,b (δ⁻¹*((diagonalWeight r u v : F)*x))⁆
    rw [conjugate_commutatorElement]
    apply CentralExtension.commutator_eq_of_image_eq f hk
    · rw [map_mul, map_mul, map_inv, hd, ha]
      exact (diagonal_commute u v _ _).mul_inv_cancel
    · rw [map_mul, map_mul, map_inv, hd, hb, hb, diagonal_conjugate]
      congr 1
      ring

end Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.FieldFour
