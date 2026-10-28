module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiFrattini
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.FrattiniActions
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanCyclic
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.FixedActionImage
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.OctagonRoots

/-!
# The perpendicular Suzuki action on the source Cartan

On a positive-parameter Suzuki root, the actual Frattini quotient has
order q. The odd cyclic Cartan image of order q-1 embeds faithfully in
its automorphism group. The involutory source reflection preserves this
root and normalizes its Cartan image; the odd-dimensional Singer argument
forces conjugation by that reflection to fix the entire image.

At m=0 the actual odd Cartan image is trivial, so the same conclusion
holds directly. No perfectness or simplicity of Sz(2) is used. The
conclusion concerns the actual root action, not an unrelated module.

Source: Fong--Seitz I (1973), the second divisibility in the proof of
(6H)(a), p.51. CommonField combines this with the linear direction on
the same marked quotient.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure (rootAt rootAt_torus_normalizes)
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2) (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

include μ hB in
/-- The source reflection centralizes the actual odd Cartan image on the
perpendicular Suzuki root. This includes m=0, where that image is trivial. -/
theorem suzuki_perpendicular_action_eq (hm : rotationOrder Q = 8)
    (j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split i)
    (h : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
    rootAction Q split i (Q.simple j*Q.simple i*Q.simple j) (simpleCartanAction Q split i h) =
      rootAction Q split i (Q.simple j*Q.simple i*Q.simple j) h := by
  let w := Q.simple j*Q.simple i*Q.simple j
  let A := rootAt Q split i w
  let H := Q.tits.B ⊓ Q.tits.N
  let a := rootAction Q split i w
  have hc : Nat.card a.range = 2^(2*m+1)-1 := by
    rw [Nat.card_congr (rootActionImageEquiv Q split i w).toEquiv]
    exact suzuki_cartanImage_card Q split i m μ hB s
  by_cases hm0 : m = 0
  · subst m
    have hc1 : Nat.card a.range = 1 := by simpa using hc
    have hsub : Subsingleton a.range := (Nat.card_eq_one_iff_unique.mp hc1).1
    exact congrArg Subtype.val (@Subsingleton.elim _ hsub
      (a.rangeRestrict (simpleCartanAction Q split i h)) (a.rangeRestrict h))
  · have hmpos := Nat.pos_of_ne_zero hm0
    let r := involutoryRootReflection Q split i s
    have hrA := perpendicular_root_normalizes Q split hm i j hij r.val r.class_eq
    let t : MulAut A := A.normalizerMonoidHom ⟨r.val,hrA⟩
    have ht2 : t^2 = 1 := by
      change (A.normalizerMonoidHom ⟨r.val,hrA⟩)^2 = 1
      rw [← map_pow]
      have hr2 : (⟨r.val,hrA⟩ : normalizer (A : Set (X ⧸ Q.D)))^2 = 1 :=
        Subtype.ext (involutoryRootReflection_sq Q split i s)
      rw [hr2,map_one]
    have htwo : IsPGroup 2 A :=
      (split.isTwo.to_le (simpleRoot_le Q split i)).of_equiv
        (RootAction.conjugateEquiv (simpleRoot Q split i) (representative w)).symm
    let : IsCyclic a.range := (rootActionImageEquiv Q split i w).isCyclic.mpr
      (suzuki_cartanImage_cyclic Q split i m μ hB s)
    have ho : Nat.Coprime (Nat.card a.range) 2 :=
      (split.odd.of_dvd_right (card_dvd_of_surjective a.rangeRestrict a.rangeRestrict_surjective)).symm
    have hnorm : t ∈ normalizer (a.range : Set (MulAut A)) :=
      RootAction.action_normalizes_image H A (rootAt_torus_normalizes Q split i w)
        ⟨r.val,hrA⟩ (torus_normalizes r.val)
    have htC := RootAction.involution_centralizes_odd_image htwo a.range ho
      (show Odd (2*m+1) from ⟨m,rfl⟩) hc
      (suzuki_rootAt_frattini_card Q split i m μ hB hmpos w) t ht2 hnorm
    rw [rootAction_reflection Q split i i w r hrA]
    have he : a h*t = t*a h := (mem_centralizer_iff.mp htC) _ ⟨h,rfl⟩
    change t⁻¹*a h*t = a h
    rw [mul_assoc,he,inv_mul_cancel_left]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
