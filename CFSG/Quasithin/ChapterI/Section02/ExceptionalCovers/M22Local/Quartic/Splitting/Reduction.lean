module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Binary.Recognition
public import Theory.Mathieu.M22.Properties.HexadFourSquare.Basic
public import Theory.Mathieu.M22.CyclicFourCover
public import Theory.GroupTheory.CentralExtensionCommutingPair
public import Theory.GroupTheory.Commutator.PerfectSplitSolvable

/-!
# A native square-root criterion for the quartic hexad complement

The actual six-point quotient is `hexadSixMap`. A section of the native hexad
stabilizer lifts through the central cover if two independent involutions in
its image have a commuting square root in M₂₂. This root forces commuting
lifts; the earlier A₆ covering identification then excludes the nontrivial
perfect cover in the derived subgroup of the full preimage. The resulting
section has the original six-point marking. Perfectness of I forces R=[R,L],
without assuming that the quartic radical is abelian.

The native square-root identity is an explicit, still independent premise.
Involution lifting alone does not supply it: C₄ ◦ SL₂(9) is the local obstruction.
Thus this module is a reduction, not the completed splitting assertion of
Aschbacher–Smith I.2.2(6), printed pp.410 and 412 / PDF pp.421 and 423.
The native splitting and earlier covering input retain their assembly owners.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic.Splitting
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open scoped Pointwise
universe u
variable {K : Type u} [Group K] [Finite K]

/-- Once a genuine section exists, perfectness discharges the complete
commutator-generation clause for the nonabelian radical. -/
theorem radical_commutator_of_section
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    [Group.IsPerfect (hexadPreimage e B)]
    (s : alternatingGroup (Fin 6) →* hexadPreimage e B)
    (hs : (hexadSixMap e hB).comp s = MonoidHom.id _) :
    ⁅(hexadRadical e B).subgroupOf (hexadPreimage e B), s.range⁆ =
      (hexadRadical e B).subgroupOf (hexadPreimage e B) := by
  let R := (hexadRadical e B).subgroupOf (hexadPreimage e B)
  have hp : IsPGroup 2 (hexadRadical e B) := IsPGroup.of_card (n := 6) (by
    rw [hexadRadical_card e hB, hZ]
    decide)
  have hpR : IsPGroup 2 R := hp.of_equiv (subgroupOfEquivOfLe (hexadRadical_le e B)).symm
  let : Group.IsNilpotent R := hpR.isNilpotent
  exact commutator_eq_left_of_perfect_complement R s.range
    (hexadSection_isComplement e hB (MulEquiv.refl _) s (fun a => DFunLike.congr_fun hs a))

/-- Construct the actual marked A₆ section and discharge its complement and
commutator clauses, conditional on the native commuting-square identity.
`hcover` is precisely the earlier two-primary covering input, not an assumed
splitting theorem. The native square-root premise remains to be proved. -/
theorem exists_section_of_native_four_square
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    [Group.IsPerfect (hexadPreimage e B)]
    (hcover : CentralExtension.TwoPrimaryInvolutionData.{u} (alternatingGroup (Fin 6)))
    (j : alternatingGroup (Fin 6) →* MulAction.stabilizer M22 B)
    (hjmark : ∀ a, m22HexadAction hB (j a) = a.val)
    (hfour : M22HexadFourSquare.HasSquare j) :
    ∃ s : alternatingGroup (Fin 6) →* hexadPreimage e B,
      (hexadSixMap e hB).comp s = MonoidHom.id _ ∧
      (localProjection e (MulAction.stabilizer M22 B)).comp s = j ∧
      ((hexadRadical e B).subgroupOf (hexadPreimage e B)).IsComplement' s.range ∧
      ⁅(hexadRadical e B).subgroupOf (hexadPreimage e B), s.range⁆ =
        (hexadRadical e B).subgroupOf (hexadPreimage e B) := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let j₀ := (MulAction.stabilizer M22 B).subtype.comp j
  have hj : Function.Injective j₀ := by
    intro a b hab
    have he : j a = j b := Subtype.ext hab
    apply Subtype.ext
    rw [← hjmark a, ← hjmark b, he]
  have hc : (projection e).ker ≤ center K := (projection_ker e).le
  have hp : IsPGroup 2 (projection e).ker := by
    rw [projection_ker]
    exact IsPGroup.of_card (n := 2) hZ
  obtain ⟨a, b, ha, hb, ha1, hb1, hab, r, hr, hrb⟩ := hfour
  have hcomm (x y : K) (hx : projection e x = j₀ a) (hy : projection e y = j₀ b) :
      Commute x y := CentralExtension.commute_lifts_of_commuting_square_root
    (projection e) (projection_surjective e) hc (j₀ a) (j₀ b) r hr
      (by rw [← map_pow, hb, map_one]) hrb x y hx hy
  obtain ⟨t, ht⟩ := CentralExtension.exists_lift_of_commuting_involution_lifts
    hcover (projection e) (projection_surjective e) hc hp j₀ hj
      a b ha hb ha1 hb1 hab hcomm
  have ht' (a : alternatingGroup (Fin 6)) : projection e (t a) = j₀ a :=
    DFunLike.congr_fun ht a
  let s : alternatingGroup (Fin 6) →* hexadPreimage e B := t.codRestrict _ (fun a => by
    change projection e (t a) ∈ MulAction.stabilizer M22 B
    rw [ht']
    exact (j a).property)
  have hs : (hexadSixMap e hB).comp s = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro a
    apply Subtype.ext
    change m22HexadAction hB (localProjection e (MulAction.stabilizer M22 B) (s a)) = a.val
    have hl : localProjection e (MulAction.stabilizer M22 B) (s a) = j a :=
      Subtype.ext (ht' a)
    rw [hl, hjmark]
  have hnative : (localProjection e (MulAction.stabilizer M22 B)).comp s = j := by
    apply MonoidHom.ext
    intro a
    exact Subtype.ext (ht' a)
  exact ⟨s, hs, hnative, hexadSection_isComplement e hB (MulEquiv.refl _) s
    (fun a => DFunLike.congr_fun hs a), radical_commutator_of_section e hZ hB s hs⟩

/-- The native actor may arrive with a comparison automorphism. Precomposing
by its inverse gives a section of the literal six-point quotient and retains
the exact comparison triangle to the original native actor. -/
theorem exists_section_of_marked_native_four_square
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    [Group.IsPerfect (hexadPreimage e B)]
    (hcover : CentralExtension.TwoPrimaryInvolutionData.{u} (alternatingGroup (Fin 6)))
    (alpha : alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6))
    (j : alternatingGroup (Fin 6) →* MulAction.stabilizer M22 B)
    (hjmark : ∀ a, m22HexadAction hB (j a) = (alpha a).val)
    (hfour : M22HexadFourSquare.HasSquare j) :
    ∃ s : alternatingGroup (Fin 6) →* hexadPreimage e B,
      (hexadSixMap e hB).comp s = MonoidHom.id _ ∧
      (localProjection e (MulAction.stabilizer M22 B)).comp s =
        j.comp alpha.symm.toMonoidHom ∧
      ((hexadRadical e B).subgroupOf (hexadPreimage e B)).IsComplement' s.range ∧
      ⁅(hexadRadical e B).subgroupOf (hexadPreimage e B), s.range⁆ =
        (hexadRadical e B).subgroupOf (hexadPreimage e B) :=
  exists_section_of_native_four_square e hZ hB hcover (j.comp alpha.symm.toMonoidHom)
    (fun a => by simpa using hjmark (alpha.symm a)) (hfour.comp_mulEquiv alpha.symm)

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic.Splitting
