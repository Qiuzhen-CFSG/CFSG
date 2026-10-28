module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.RetainedBlock.Invariance

/-!
# Fixed vectors of the two retained rotations

The distinguished rotation has no fixed vector on its displacement space.
For the other factor, faithfulness on the two-dimensional reflection half
forces its rotation-fixed space to vanish. Commutation with the distinguished
rotation carries this conclusion to the translated half. Directness of the
two halves then gives zero fixed space on the full four-dimensional block.

Source: Aschbacher--Smith G.9.2, printed p.353, the orthogonal alternative.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.RetainedBlock
open DihedralDegree DihedralGroup
universe v
variable {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

theorem fixed_zero_on_half_sum
    (f t : Module.End (ZMod 2) W) (U : Submodule (ZMod 2) W)
    (ht : Function.Injective t) (hc : Commute f t)
    (hU : U ≤ U.comap f) (hd : Disjoint U (U.map t))
    (hfix : ∀ w ∈ U, f w = w → w = 0)
    (w : W) (hw : w ∈ U ⊔ U.map t) (hf : f w = w) : w = 0 := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hw
  obtain ⟨z, hz, rfl⟩ := hv
  have hc' : f (t z) = t (f z) := congrArg (fun a : Module.End (ZMod 2) W => a z) hc.eq
  rw [map_add, hc'] at hf
  have he : f u - u = t (z - f z) := by
    rw [map_sub, sub_eq_sub_iff_add_eq_add]
    simpa only [add_comm u (t z)] using hf
  have hmem : f u - u ∈ U ⊓ U.map t :=
    ⟨U.sub_mem (hU hu) hu, ⟨z - f z, U.sub_mem hz (hU hz), he.symm⟩⟩
  rw [hd.eq_bot, Submodule.mem_bot] at hmem
  have hu0 := hfix u hu (sub_eq_zero.mp hmem)
  have hz0 : z = 0 := by
    have hh : t (z - f z) = t 0 := by rw [← he, hmem, map_zero]
    exact hfix z hz (sub_eq_zero.mp (ht hh)).symm
  simp [hu0, hz0]

theorem plane_rotation_fixed_zero [FiniteDimensional (ZMod 2) W]
    (split : DihedralSplittingTheorem.{v}) {q : ℕ}
    (hq : q.Prime) (ho : Odd q) (τ : Representation (ZMod 2) (DihedralGroup q) W)
    (hf : Function.Injective τ) (hd : Module.finrank (ZMod 2) W = 2)
    (w : W) (hw : τ (r 1) w = w) : w = 0 := by
  obtain ⟨hC, _, hU⟩ := split_dimensions τ split hq ho hf
  have hdim : Module.finrank (ZMod 2) (rotationFixed τ) = 0 := by omega
  have hbot : rotationFixed τ = ⊥ := Submodule.finrank_eq_zero.mp hdim
  have hh := (mem_rotationFixed τ w).mpr hw
  rwa [hbot, Submodule.mem_bot] at hh

variable {ι : Type} [Fintype ι] [DecidableEq ι] {p : ι → ℕ}
  (σ : Representation (ZMod 2) (∀ i, DihedralGroup (p i)) W) (i : ι)
  [FiniteDimensional (ZMod 2) W]

omit [Fintype ι] in
theorem distinguished_rotation_fixed_zero
    (split : DihedralSplittingTheorem.{v})
    (hp : (p i).Prime) (ho : Odd (p i)) (hf : Function.Injective σ)
    (w : rotationMoved (factorRep σ i)) (hw : σ (Pi.mulSingle i (r 1)) w = (w : W)) :
    (w : W) = 0 := by
  have hs := split W (p i) hp ho (factorRep σ i) (factorRep_injective σ hf i)
  have hh : (w : W) ∈ rotationFixed (factorRep σ i) ⊓ rotationMoved (factorRep σ i) :=
    ⟨(mem_rotationFixed (factorRep σ i) w).mpr hw, w.property⟩
  rwa [hs.1.inf_eq_bot, Submodule.mem_bot] at hh

theorem second_rotation_fixed_zero
    (split : DihedralSplittingTheorem.{v})
    (hp : ∀ j, (p j).Prime) (ho : ∀ j, Odd (p j)) (hf : Function.Injective σ)
    {exceptional : Prop} (s : PreparedSplit σ i exceptional)
    (hM : Module.finrank (ZMod 2) (rotationMoved (factorRep σ i)) = 4)
    (j : s.actions.J) (w : rotationMoved (factorRep σ i))
    (hw : σ (Pi.mulSingle j.val (r 1)) w = (w : W)) : (w : W) = 0 := by
  let U := reflectionHalf (factorRep σ i)
  let υ := Representation.subrepresentation (σ.comp (subproductHom s.actions.J)) U
    s.actions.half_stable
  let f := σ (Pi.mulSingle j.val (r 1))
  let t := σ (Pi.mulSingle i (r 1))
  have hs := split W (p i) (hp i) (ho i) (factorRep σ i) (factorRep_injective σ hf i)
  have hdim := (split_dimensions (factorRep σ i) split (hp i) (ho i)
    (factorRep_injective σ hf i)).2.1
  have hUdim : Module.finrank (ZMod 2) U = 2 := by dsimp [U]; omega
  have hji : j.val ≠ i := fun he => s.actions.excluded
    ((congrArg (fun k : ι => k ∈ s.actions.J) he).mp j.property)
  have hc : Commute f t := (Pi.mulSingle_commute hji (r 1) (r 1)).map σ
  have hU : U ≤ U.comap f := by
    have hh := s.actions.half_stable (Pi.mulSingle j (r 1))
    simpa only [MonoidHom.comp_apply, subproductHom_single] using hh
  have hfix : ∀ u ∈ U, f u = u → u = 0 := by
    intro u hu he
    have hh := plane_rotation_fixed_zero split (hp j) (ho j) (factorRep υ j)
      (factorRep_injective υ s.actions.half_faithful j) hUdim ⟨u, hu⟩
    have hh' : factorRep υ j (r 1) ⟨u, hu⟩ = ⟨u, hu⟩ := by
      apply Subtype.ext
      change σ (subproductHom s.actions.J (Pi.mulSingle j (r 1))) u = u
      rwa [subproductHom_single]
    exact congrArg Subtype.val (hh hh')
  have hsum : U ⊔ U.map t = rotationMoved (factorRep σ i) := hs.2.2
  exact fixed_zero_on_half_sum f t U (σ.apply_bijective _).injective hc hU
    hs.2.1 hfix w (by rw [hsum]; exact w.property) hw

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.RetainedBlock
