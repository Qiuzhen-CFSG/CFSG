module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic.Splitting.Reduction
public import Theory.Mathieu.M22.Properties.HexadFourSquare

/-!
# The actual quartic hexad complement

For every native hexad, the certified commuting square in its point complement
forces commuting involution lifts in the central cover. The earlier A₆ covering
data then supplies a section of the literal six-point quotient. Its range
complements the actual radical, and perfectness of the hexad preimage gives
the full identity R = [R,L]. The comparison with the native actor is retained.

`exists_section` uses the original six-point labels; `exists_naturally_marked_section`
uses the native natural-module actor and displays the comparison automorphism
in its quotient formula. Both construct the complement without any native
splitting or square-root premise.

The earlier A₆ two-primary covering identification and perfectness of I remain
explicit inputs, as authorized by the source assembly owner. This completes the
splitting step with those inputs, not the subsequent central-product and action
recognition of Aschbacher–Smith I.2.2(6), printed pp.410 and 412 / PDF pp.421 and 423.
-/

public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic.Splitting
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open scoped Pointwise
universe u
variable {K : Type u} [Group K] [Finite K]

/-- A section of the literal six-point quotient, together with the exact
projection to the native naturally marked actor, complementarity, and R=[R,L].
Only the earlier covering data and perfectness remain source inputs. -/
theorem exists_section
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    [Group.IsPerfect (hexadPreimage e B)]
    (hcover : CentralExtension.TwoPrimaryInvolutionData.{u} (alternatingGroup (Fin 6))) :
    ∃ s : alternatingGroup (Fin 6) →* hexadPreimage e B,
      (hexadSixMap e hB).comp s = MonoidHom.id _ ∧
      (localProjection e (MulAction.stabilizer M22 B)).comp s =
        (m22HexadSection hB).comp (m22HexadMarking hB).symm.toMonoidHom ∧
      ((hexadRadical e B).subgroupOf (hexadPreimage e B)).IsComplement' s.range ∧
      ⁅(hexadRadical e B).subgroupOf (hexadPreimage e B), s.range⁆ =
        (hexadRadical e B).subgroupOf (hexadPreimage e B) :=
  exists_section_of_marked_native_four_square e hZ hB hcover
    (m22HexadMarking hB) (m22HexadSection hB)
    (fun a => congrArg Subtype.val (m22HexadSixMap_section hB a))
    (M22HexadFourSquare.section_hasSquare hB)

/-- The same complement parametrized by the actual native natural-module
actor. The quotient retains the original six-point comparison automorphism;
the parent action-recognition proof can use the native coordinates directly. -/
theorem exists_naturally_marked_section
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    [Group.IsPerfect (hexadPreimage e B)]
    (hcover : CentralExtension.TwoPrimaryInvolutionData.{u} (alternatingGroup (Fin 6))) :
    ∃ s : alternatingGroup (Fin 6) →* hexadPreimage e B,
      (hexadSixMap e hB).comp s = (m22HexadMarking hB).toMonoidHom ∧
      (localProjection e (MulAction.stabilizer M22 B)).comp s = m22HexadSection hB ∧
      ((hexadRadical e B).subgroupOf (hexadPreimage e B)).IsComplement' s.range ∧
      ⁅(hexadRadical e B).subgroupOf (hexadPreimage e B), s.range⁆ =
        (hexadRadical e B).subgroupOf (hexadPreimage e B) := by
  obtain ⟨s, hs, hnative, hcomp, hcomm⟩ := exists_section e hZ hB hcover
  let alpha := m22HexadMarking hB
  let t := s.comp alpha.toMonoidHom
  have hrange : t.range = s.range := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨alpha a, rfl⟩
    · rintro ⟨a, rfl⟩
      refine ⟨alpha.symm a, ?_⟩
      change s (alpha (alpha.symm a)) = s a
      rw [alpha.apply_symm_apply]
  refine ⟨t, ?_, ?_, hrange.symm ▸ hcomp, hrange.symm ▸ hcomm⟩
  · apply MonoidHom.ext
    intro a
    exact DFunLike.congr_fun hs (alpha a)
  · apply MonoidHom.ext
    intro a
    change localProjection e (MulAction.stabilizer M22 B) (s (alpha a)) = m22HexadSection hB a
    have hn := DFunLike.congr_fun hnative (alpha a)
    change localProjection e (MulAction.stabilizer M22 B) (s (alpha a)) =
      m22HexadSection hB (alpha.symm (alpha a)) at hn
    rw [alpha.symm_apply_apply] at hn
    exact hn

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic.Splitting
