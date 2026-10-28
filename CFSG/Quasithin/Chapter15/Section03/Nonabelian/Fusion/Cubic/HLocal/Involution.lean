module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal.Geometry
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal.OuterModel

/-!
# The cubic witness for the supplied source involution

An inner automorphism preserves the natural summand in the recognized
coordinates. The literal quotient action of a swapping element therefore
has an outer actor image. For a square-one source element this image is an
outer involution, so the exact model theorem constructs a cubic subgroup
in its centralizer. No outer-action premise is added to the source inputs.

Source: Aschbacher–Smith 15.3.58(3) and the proof of 15.3.61(1), p.1150.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal
variable {G : Type*} [Group G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- The same actor recognition transported through SL₃(2) ≃ PSL₃(2). -/
noncomputable def linearActor (d : Recognition Z ZS) :
    ActorQuotient Z ≃* MulAut Matrix.PSL3Two.SL :=
  d.actor.trans (MulAut.congr Matrix.PSL3Two.equiv.symm)

/-- A genuine swap of the natural and dual summands has noninner actor image. -/
lemma swapped_not_inner (d : Recognition Z ZS) (t : centralizerH Z)
    (hs : Swaps Z ZS d t) :
    linearActor Z ZS d (QuotientGroup.mk' (pCore 2 (centralizerH Z)) t) ∉
      MulAut.innerSubgroup Matrix.PSL3Two.SL := by
  rintro ⟨g, hg⟩
  have he : d.actor (QuotientGroup.mk' (pCore 2 (centralizerH Z)) t) =
      MulAut.conj (Matrix.PSL3Two.equiv g) := by
    apply (MulAut.congr Matrix.PSL3Two.equiv.symm).injective
    change linearActor Z ZS d _ = _
    rw [← hg, MulAut.congr_conj, MulEquiv.symm_apply_apply]
  let v : BinaryLinearThree.Vector := fun _ => 1
  have hact := d.inner_action t g he (d.coordinates.symm (Multiplicative.ofAdd (v, 0)))
  have hzero : BinaryLinearThree.W g v = 0 := by
    simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using
      (congrArg Prod.fst hact).symm.trans (hs.1 v)
  have hv := congrArg (BinaryLinearThree.W g⁻¹) hzero
  have hinv : BinaryLinearThree.W g⁻¹ (BinaryLinearThree.W g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  rw [hinv, map_zero] at hv
  exact (by decide : (1 : ZMod 2) ≠ 0) (congrFun hv 0)

/-- The source involution centralizes a cubic in the actual actor quotient. -/
lemma source_actor_cubic (d : Recognition Z ZS)
    (t : centralizerH Z) (ht : (t : G) ^ 2 = 1) (hs : Swaps Z ZS d t) :
    ∃ D : Subgroup (ActorQuotient Z), Nat.card D = 3 ∧
      D ≤ centralizer ({QuotientGroup.mk' (pCore 2 (centralizerH Z)) t} :
        Set (ActorQuotient Z)) := by
  let q := QuotientGroup.mk' (pCore 2 (centralizerH Z))
  let e := linearActor Z ZS d
  have htH : t ^ 2 = 1 := Subtype.ext ht
  have hsq : e (q t) ^ 2 = 1 := by rw [← map_pow, ← map_pow, htH, map_one, map_one]
  obtain ⟨D, hD, hDC⟩ := OuterModel.outer_cubic (e (q t)) hsq
    (swapped_not_inner Z ZS d t hs)
  refine ⟨D.map e.symm.toMonoidHom, ?_, ?_⟩
  · rw [card_map_of_injective e.symm.injective, hD]
  · rintro _ ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using
      mem_centralizer_singleton_iff.mp (hDC hx)
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal
