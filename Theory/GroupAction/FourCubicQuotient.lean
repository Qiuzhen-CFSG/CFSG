module
public import Theory.Representation.InvertedCubicTensor.NaturalFactors
public import Theory.GroupAction.OddFourGroupLine

/-!
# The cubic acts freely on an actual four-group quotient action

When a surjective S3 quotient and the conjugation action have the same
kernel, the quotient action is faithful. Its cubic has nonidentity odd
order, and therefore fixes no nonidentity element of the four-group.
-/

public noncomputable section
open InvertedCubicTensor
namespace Theory.GroupAction

public theorem cubic_four_action_fixed_free
    {H V : Type*} [Group H] [Group V] [Finite V]
    (π:H→*S₃) (hπ:Function.Surjective π)
    (act:H→*MulAut V) (hk:π.ker=act.ker) (hc:Nat.card V=4)
    (h:H) (hh:π h=cubic) (v:V) (hv:act h v=v) : v=1 := by
  let q := π.liftOfSurjective hπ ⟨act,hk.le⟩
  have hq (x:H) : q (π x)=act x := by simp [q,MonoidHom.liftOfSurjective]
  have he : act h=q cubic := by rw [←hh,hq]
  have ho : Odd (orderOf (act h)) := by
    rw [he]
    exact (show Odd 3 from by decide).of_dvd_nat
      ((orderOf_map_dvd q cubic).trans (orderOf_dvd_of_pow_eq_one (by decide +kernel : cubic^3=1)))
  have hn : act h≠1 := by
    intro hn
    have hx : h∈π.ker := hk.symm ▸ hn
    have he : cubic=1 := hh.symm.trans hx
    exact (by decide +kernel : cubic≠1) he
  by_contra hn1
  exact odd_aut_card_four_fixed_point_free hc (act h) ho hn v hn1 hv
end Theory.GroupAction
