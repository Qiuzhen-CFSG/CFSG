module
public import ABG.ChapterII.Section1.WreathedEmbeddedLayer
public import GorensteinWalter.SL2SylowTwoPart
public import BenderSuzuki.External.Hall.Basic

/-!
# Field two-part and center radius of an actual wreathed SL2 layer

Suppose an ambient Sylow subgroup R embeds into a wreathed presentation of
height n, and the image of its intersection with a supplied normal SL2(F)
subgroup is the designated quaternion layer. Then the exact two-part of
|F|−1 or |F|+1 is 2^n according to |F| modulo four. The same n controls
the center radius and central-product versus exterior-square alternative
in the original R.

The embedded quaternion layer has order 2^(n+1). Identify it with the
actual normal Sylow restriction in L0 and transport that Sylow through
the supplied SL2 equivalence. The proved Sylow order calculation supplies
the field two-part; WreathedEmbeddedLayer supplies the original-group
center and exterior data. No full wreathed shape is required of R.

This combines the exact group and field parameters in
Alperin--Brauer--Gorenstein II.3 Proposition 3, article p26, for the
subsequent linear/unitary central-product and index-two model comparison.
-/

namespace ABG

public theorem wreathed_sylow_sl2_radius_data
    {H S : Type*} [Group H] [Finite H] [Group S] {n : ℕ}
    (P : Wreathed.Presentation S n) (R : Sylow 2 H)
    (L0 : Subgroup H) [L0.Normal]
    (F : Type*) [Field F] [Finite F] (hF : Odd (Nat.card F))
    (eL0 : L0 ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (f : R →* S) (hf : Function.Injective f)
    (hlink : (L0.comap (R : Subgroup H).subtype).map f = P.Y) :
    ((Nat.card F % 4 = 1 ∧ 2 ^ n ∣ Nat.card F - 1 ∧ Odd ((Nat.card F - 1) / 2 ^ n)) ∨
      (Nat.card F % 4 = 3 ∧ 2 ^ n ∣ Nat.card F + 1 ∧ Odd ((Nat.card F + 1) / 2 ^ n))) ∧
      ∃ r < n, Nat.card (Subgroup.center R) = 2 ^ (r + 1) ∧
        (L0.comap (R : Subgroup H).subtype ⊔ Subgroup.center R = ⊤ ∨
          (Function.Surjective f ∧ r = n - 1 ∧
            (L0.comap (R : Subgroup H).subtype ⊔ Subgroup.center R).index = 2 ∧
            ∃ a : R, a ∉ L0.comap (R : Subgroup H).subtype ⊔ Subgroup.center R ∧
              Subgroup.zpowers (a ^ 2) = Subgroup.center R)) := by
  let A := L0.comap (R : Subgroup H).subtype
  obtain ⟨hAcard, hgeo⟩ := P.embedded_quaternion_layer_data f hf A hlink
  let T := BenderSuzuki.External.hallSylowSubgroupOfNormal R L0
  let eA : A ≃* T := {
    toFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
    invFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  let U := T.mapSurjective (f := eL0.toMonoidHom) eL0.surjective
  have hUc : Nat.card U = 2 ^ (n + 1) := by
    change Nat.card ((T : Subgroup L0).map eL0.toMonoidHom) = _
    rw [Subgroup.card_map_of_injective eL0.injective]
    exact (Nat.card_congr eA.symm.toEquiv).trans hAcard
  exact ⟨GorensteinWalter.sl2_sylow_two_part_of_card F hF U n P.height hUc, hgeo⟩

end ABG

