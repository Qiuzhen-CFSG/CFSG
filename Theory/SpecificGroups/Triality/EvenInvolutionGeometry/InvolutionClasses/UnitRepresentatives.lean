module

public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.Complete
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic

/-!
# Parameter-one representatives for every native triality involution

Squaring is onto each finite characteristic-two root field. The literal SL₂
coroot action therefore conjugates each nonzero root parameter to one.
Combining this with the proved two-root-class theorem gives the two fixed
representatives needed by the module displacement calculation, including q=2.
Source: GLS3 1.12.1 and Aschbacher–Smith 16.1.4(1).
-/

@[expose] public noncomputable section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.EvenInvolutionGeometry
private theorem upper_conjugate_one {F : Type*} [Field F] [Finite F] [CharP F 2]
    (t : F) (ht : t ≠ 0) :
    IsConj (SpecialLinearGroup.upperUnipotentHom F (Multiplicative.ofAdd (1:F)))
      (SpecialLinearGroup.upperUnipotentHom F (Multiplicative.ofAdd t)) := by
  obtain ⟨a,ha⟩ := (frobeniusEquiv F 2).surjective t
  change a^2=t at ha
  have ha0 : a≠0 := by intro he; subst a; simp at ha; exact ht ha.symm
  apply isConj_iff.mpr
  refine ⟨SpecialLinearGroup.diag2 a ha0, ?_⟩
  change _ * SpecialLinearGroup.transvection zero_ne_one 1 * _ =
    SpecialLinearGroup.transvection zero_ne_one t
  rw [SpecialLinearGroup.diag_conj_upper, mul_one, ha]

variable (n : ℕ) (hn : 0<n)
local notation "P" => binaryParameters n hn

theorem longRoot_conjugate_one (t : GaloisField 2 n) (ht : t≠0) :
    IsConj (longRoot n hn 1) (longRoot n hn t) :=
  ((toCarrier P).comp (Parabolics.sl2ElementaryLift P rfl (longRankOneFixed n hn))).map_isConj
    (upper_conjugate_one t ht)

theorem shortRoot_conjugate_one (t : ExtensionField P) (ht : t≠0) :
    IsConj (shortRoot n hn 1) (shortRoot n hn t) :=
  ((toCarrier P).comp (Parabolics.sl2ElementaryLift P rfl (shortRankOneFixed n hn))).map_isConj
    (upper_conjugate_one t ht)

def rootOne (short : Bool) : BinaryCarrier n hn :=
  if short then shortRoot n hn 1 else longRoot n hn 1

theorem involution_conjugate_rootOne (t : BinaryCarrier n hn) (ht : orderOf t=2) :
    ∃ short : Bool, IsConj (rootOne n hn short) t := by
  rcases involution_isLongRoot_or_isShortRoot n hn t ht with h|h
  · obtain ⟨a,ha,hc⟩ := h
    exact ⟨false,(longRoot_conjugate_one n hn a ha).trans hc⟩
  · obtain ⟨a,ha,hc⟩ := h
    exact ⟨true,(shortRoot_conjugate_one n hn a ha).trans hc⟩
end Triality.Standard.EvenInvolutionGeometry
