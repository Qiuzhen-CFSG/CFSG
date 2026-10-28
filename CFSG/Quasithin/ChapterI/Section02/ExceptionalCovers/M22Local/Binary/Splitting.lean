module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Binary.Recognition
public import Theory.Mathieu.M22.Properties.HexadSplitCoordinates
public import Theory.GroupTheory.CentralExtensionCommutingPair
public import Theory.Mathieu.M22.CentralCoverPrelude.InvolutionSquares

/-!
# Lifting the native hexad complement through the double cover

Every lift of a square-one element of M₂₂ has square one, since the central
kernel has order two and quotient involutions lift. Consequently lifts of a
Klein four pair in the native A₆ complement commute. The earlier A₆ covering
identification excludes the nontrivial perfect derived cover and constructs
a lifted section. Its projection is the specified native section, so the
comparison with the original six-point labels is retained exactly.

Source: Aschbacher–Smith I.2.2(1), (ii), and (6), printed pp.410 and 412.
Only the earlier A₆ covering data remains an explicit input.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Binary
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open scoped Pointwise
universe u
variable {K : Type u} [Group K] [Finite K]

/-- The actual native A₆ section lifts, retaining its natural-module marking. -/
theorem exists_naturally_marked_section
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 2)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hcover : CentralExtension.TwoPrimaryInvolutionData.{u} (alternatingGroup (Fin 6))) :
    ∃ s : alternatingGroup (Fin 6) →* hexadPreimage e B,
      (∀ a, hexadSixMap e hB (s a) = m22HexadMarking hB a) ∧
      (localProjection e (MulAction.stabilizer M22 B)).comp s = m22HexadSection hB := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let j := (MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)
  have hj : Function.Injective j :=
    Subtype.val_injective.comp (m22HexadSection_injective hB)
  let a : alternatingGroup (Fin 6) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by simp [Equiv.Perm.mem_alternatingGroup]⟩
  let b : alternatingGroup (Fin 6) :=
    ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by simp [Equiv.Perm.mem_alternatingGroup]⟩
  have ha : a ^ 2 = 1 := by decide
  have hb : b ^ 2 = 1 := by decide
  have hab2 : (a * b) ^ 2 = 1 := by decide
  have hcomm (x y : K) (hx : projection e x = j a) (hy : projection e y = j b) :
      Commute x y := by
    have hx2 := square_eq_one e hZ x (by rw [hx, ← map_pow, ha, map_one])
    have hy2 := square_eq_one e hZ y (by rw [hy, ← map_pow, hb, map_one])
    have hxy2 := square_eq_one e hZ (x * y) (by
      rw [map_mul, hx, hy, ← map_mul, ← map_pow, hab2, map_one])
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx2)
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hy2)
    have hxyi : (x * y)⁻¹ = x * y :=
      inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hxy2)
    exact hxyi.symm.trans (by rw [mul_inv_rev, hxi, hyi])
  obtain ⟨t, ht⟩ := CentralExtension.exists_lift_of_commuting_involution_lifts
    hcover (projection e) (projection_surjective e) (projection_ker e).le
    (by rw [projection_ker]; exact IsPGroup.of_card (n := 1) (by simpa using hZ))
    j hj a b ha hb (by decide) (by decide) (by decide) hcomm
  have ht' (a : alternatingGroup (Fin 6)) : projection e (t a) = j a :=
    DFunLike.congr_fun ht a
  let s : alternatingGroup (Fin 6) →* hexadPreimage e B := t.codRestrict _ (fun a => by
    change projection e (t a) ∈ MulAction.stabilizer M22 B
    rw [ht']
    exact (m22HexadSection hB a).property)
  have hs (a : alternatingGroup (Fin 6)) :
      localProjection e (MulAction.stabilizer M22 B) (s a) = m22HexadSection hB a :=
    Subtype.ext (ht' a)
  refine ⟨s, ?_, MonoidHom.ext hs⟩
  intro a
  apply Subtype.ext
  change m22HexadAction hB (localProjection e (MulAction.stabilizer M22 B) (s a)) = _
  rw [hs]
  exact congrArg Subtype.val (m22HexadSixMap_section hB a)

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Binary
