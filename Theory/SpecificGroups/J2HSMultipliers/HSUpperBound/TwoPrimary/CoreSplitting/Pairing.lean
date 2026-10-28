module

public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary.CoreSplitting.Seven
public import Theory.GroupTheory.Commutator.CentralExtensionPairing

/-!
# Vanishing of the HS core commutator pairing

Pull back the central-extension commutator pairing along the actual C₄³
coordinate homomorphism. Conjugating both lifts leaves this pairing fixed.
The concrete actor of `Seven` gives three equations on its alternating
basis values a, b, c: b + c = 0, 3a - 2c = b, and a + b = c.
They imply 5b = 0, while the coordinate exponent gives 4b = 0. Thus all
three values vanish, and arbitrary elements of the core preimage commute.

No bound on the central kernel and no perfectness hypothesis is used.
This is an independent local input to Aschbacher–Smith I.1.3(1), printed
p.407, using the literal model geometry of GLS3 Table 5.3m. It does not
use the covering conclusions of Aschbacher–Smith I.2.2.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.CoreSplitting
open Sporadic.LeechRelated.HS BlockNormalizer BlockNormalizer.CoreGeometry

private theorem pairing_eq_zero {C : Type*} [AddCommGroup C]
    (B : (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4) →+ C)
    (halt : ∀ x, B x x = 0)
    (hinv : ∀ i j, B (sevenAxis i) (sevenAxis j) = B (axis i) (axis j)) :
    ∀ x y, B x y = 0 := by
  have hskew (x y) : B y x = -B x y := by
    have h := halt (x + y)
    simp only [map_add, AddMonoidHom.add_apply, halt, zero_add, add_zero] at h
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using h
  have h01 : B (axis 0) (axis 1) - B (axis 0) (axis 2) - B (axis 1) (axis 2) =
      B (axis 0) (axis 1) := by
    calc
      _ = B (sevenAxis 0) (sevenAxis 1) := by
        change _ = B (3 • axis 0 + axis 1 + 2 • axis 2) (2 • axis 0 + axis 1 + axis 2)
        simp only [map_add, map_nsmul, AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply,
          halt, hskew (axis 0) (axis 1), hskew (axis 0) (axis 2), hskew (axis 1) (axis 2)]
        abel
      _ = _ := hinv 0 1
  have h02 : 3 • B (axis 0) (axis 1) - 2 • B (axis 1) (axis 2) = B (axis 0) (axis 2) := by
    calc
      _ = B (sevenAxis 0) (sevenAxis 2) := by
        change _ = B (3 • axis 0 + axis 1 + 2 • axis 2) (3 • axis 0 + 2 • axis 1 + 2 • axis 2)
        simp only [map_add, map_nsmul, AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply,
          halt, hskew (axis 0) (axis 1), hskew (axis 0) (axis 2), hskew (axis 1) (axis 2)]
        abel
      _ = _ := hinv 0 2
  have h12 : B (axis 0) (axis 1) + B (axis 0) (axis 2) = B (axis 1) (axis 2) := by
    calc
      _ = B (sevenAxis 1) (sevenAxis 2) := by
        change _ = B (2 • axis 0 + axis 1 + axis 2) (3 • axis 0 + 2 • axis 1 + 2 • axis 2)
        simp only [map_add, map_nsmul, AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply,
          halt, hskew (axis 0) (axis 1), hskew (axis 0) (axis 2), hskew (axis 1) (axis 2)]
        abel
      _ = _ := hinv 1 2
  have h1 : B (axis 0) (axis 2) + B (axis 1) (axis 2) = 0 := by
    calc
      _ = B (axis 0) (axis 1) -
          (B (axis 0) (axis 1) - B (axis 0) (axis 2) - B (axis 1) (axis 2)) := by abel
      _ = 0 := by rw [h01, sub_self]
  have h2 : 3 • B (axis 0) (axis 1) - 2 • B (axis 1) (axis 2) -
      B (axis 0) (axis 2) = 0 := sub_eq_zero.mpr h02
  have h3 : B (axis 0) (axis 1) + B (axis 0) (axis 2) - B (axis 1) (axis 2) = 0 :=
    sub_eq_zero.mpr h12
  have hb5 : 5 • B (axis 0) (axis 2) = 0 := by
    calc
      _ = 3 • (B (axis 0) (axis 1) + B (axis 0) (axis 2) - B (axis 1) (axis 2)) +
          (B (axis 0) (axis 2) + B (axis 1) (axis 2)) -
          (3 • B (axis 0) (axis 1) - 2 • B (axis 1) (axis 2) - B (axis 0) (axis 2)) := by abel
      _ = 0 := by rw [h1, h2, h3]; simp
  have hb4 : 4 • B (axis 0) (axis 2) = 0 := by
    rw [← map_nsmul]
    have hz : 4 • axis 2 = 0 := by ext i; exact ZModModule.char_nsmul_eq_zero 4 _
    rw [hz, map_zero]
  have hb : B (axis 0) (axis 2) = 0 := by
    calc
      _ = 5 • B (axis 0) (axis 2) - 4 • B (axis 0) (axis 2) := by abel
      _ = 0 := by rw [hb5, hb4]; simp
  have hc : B (axis 1) (axis 2) = 0 := by simpa [hb] using h1
  have ha : B (axis 0) (axis 1) = 0 := by simpa [hb, hc] using h3
  have hbasis (i j : Fin 3) : B (axis i) (axis j) = 0 := by
    fin_cases i <;> fin_cases j
    · exact halt _
    · exact ha
    · exact hb
    · exact (hskew _ _).trans ((congrArg Neg.neg ha).trans neg_zero)
    · exact halt _
    · exact hc
    · exact (hskew _ _).trans ((congrArg Neg.neg hb).trans neg_zero)
    · exact (hskew _ _).trans ((congrArg Neg.neg hc).trans neg_zero)
    · exact halt _
  have hcoord (x : Fin 3 → ZMod 4) :
      x = (x 0).val • axis 0 + (x 1).val • axis 1 + (x 2).val • axis 2 := by
    ext i
    change x i = (x 0).val • axis 0 i + (x 1).val • axis 1 i + (x 2).val • axis 2 i
    fin_cases i <;> simp [axis, nsmul_eq_mul]
  intro x y
  rw [hcoord x, hcoord y]
  simp only [map_add, map_nsmul, AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply,
    hbasis, nsmul_zero, add_zero]

/-- The full inverse image of the actual C₄³ core is abelian in every
surjective central extension of the literal normalizer. -/
public theorem core_preimage_isMulCommutative {D : Type*} [Group D] (g : D →* baseNormalizer)
    (hg : Function.Surjective g) (hk : g.ker ≤ center D) :
    IsMulCommutative ((pCore 2 baseNormalizer).comap g) := by
  obtain ⟨B, hB⟩ := CentralExtension.exists_lift_commutator_pairing g hg hk coordinateInNormalizer
  have halt (x) : B x x = 0 := by
    obtain ⟨a, ha⟩ := hg (coordinateInNormalizer (.ofAdd x))
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((B x x).toMul : D) = 1
    rw [hB x x a a ha ha, commutatorElement_self]
  obtain ⟨y, hy⟩ := exists_coordinate_actor
  obtain ⟨d, hd⟩ := hg y
  have hinv (i j : Fin 3) : B (sevenAxis i) (sevenAxis j) = B (axis i) (axis j) := by
    obtain ⟨a, ha⟩ := hg (coordinateInNormalizer (.ofAdd (axis i)))
    obtain ⟨b, hb⟩ := hg (coordinateInNormalizer (.ofAdd (axis j)))
    have hca : g (d * a * d⁻¹) = coordinateInNormalizer (.ofAdd (sevenAxis i)) := by
      rw [map_mul, map_mul, map_inv, hd, ha, hy]
    have hcb : g (d * b * d⁻¹) = coordinateInNormalizer (.ofAdd (sevenAxis j)) := by
      rw [map_mul, map_mul, map_inv, hd, hb, hy]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hB _ _ _ _ hca hcb, hB _ _ _ _ ha hb]
    have hcent : ⁅a, b⁆ ∈ center D := (hB _ _ _ _ ha hb) ▸ (B (axis i) (axis j)).toMul.property
    calc
      _ = d * ⁅a, b⁆ * d⁻¹ := by simp only [commutatorElement_def]; group
      _ = ⁅a, b⁆ := by rw [Subgroup.mem_center_iff.mp hcent d, mul_inv_cancel_right]
  have hzero := pairing_eq_zero B halt hinv
  apply IsMulCommutative.of_comm
  intro a b
  obtain ⟨x, hx⟩ := coreCoordinates_bijective.surjective
    (⟨g a, a.property⟩ : pCore 2 baseNormalizer)
  obtain ⟨z, hz⟩ := coreCoordinates_bijective.surjective
    (⟨g b, b.property⟩ : pCore 2 baseNormalizer)
  have ha : g a = coordinateInNormalizer (.ofAdd x.toAdd) :=
    (congrArg Subtype.val hx).symm
  have hb : g b = coordinateInNormalizer (.ofAdd z.toAdd) :=
    (congrArg Subtype.val hz).symm
  have hcomm : ⁅(a : D), (b : D)⁆ = 1 := by
    rw [← hB _ _ _ _ ha hb, hzero]
    rfl
  exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp hcomm)

end Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.CoreSplitting
