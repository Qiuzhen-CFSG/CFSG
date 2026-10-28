module

public import Stellmacher.Recognition.SuzukiThreeCoordinateData
public import Stellmacher.Recognition.SuzukiThreeHermitianRootCoordinates
public import Theory.SpecificGroups.UnitaryThree.SwapRigidity
import Mathlib.Tactic.Group

/-!
# Reciprocal coordinates for Suzuki's swapping element

Transport the action through the Hermitian Borel coordinates. Every element
fixing infinity is a root translation followed by a scalar. The local swapping
involution intertwines the scalar torus by its fifth power. The finite
Hermitian rigidity theorem then places the reciprocal permutation in the
transported group, supplying an actual element of the original group with the
full swapping equation. No adjustment of the root or torus isomorphism is needed.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
group over a finite field of odd characteristic*, J. Algebra 2 (1965),
Sections V–VI. The q = 3 rigidity calculation is in `UnitaryThree.SwapRigidity`.
-/

namespace Stellmacher.Recognition

open MulAction

namespace SuzukiThreeBorelCoordinates

variable {G Ω : Type*} [Group G] [MulAction G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    {h : SuzukiThreeHypotheses G Ω a Q} {b : Ω} {hb : b ≠ a}
    (c : SuzukiThreeBorelCoordinates h b hb)

private noncomputable def actionHom : G →* Equiv.Perm UnitaryThree.Point :=
  ((h.pointCoordinates b hb c.rootEquiv).permCongrHom.toMonoidHom).comp
    (MulAction.toPermHom G Ω)

private theorem actionHom_eq (g : G) (s : Equiv.Perm UnitaryThree.Point)
    (hs : ∀ x : Ω, h.pointCoordinates b hb c.rootEquiv (g • x) =
      s (h.pointCoordinates b hb c.rootEquiv x)) : c.actionHom g = s := by
  apply Equiv.ext
  intro x
  change h.pointCoordinates b hb c.rootEquiv
    (g • (h.pointCoordinates b hb c.rootEquiv).symm x) = s x
  rw [hs, Equiv.apply_symm_apply]

private theorem actionHom_root (q : Q) :
    c.actionHom ((q : stabilizer G a) : G) = UnitaryThree.rootPerm (c.rootEquiv q) :=
  c.actionHom_eq _ _ (h.pointCoordinates_root_smul b hb c.rootEquiv q)

private theorem actionHom_torus (k : stabilizer (stabilizer G a) b) :
    c.actionHom ((k : stabilizer G a) : G) = UnitaryThree.torusPerm (c.torusEquiv k) :=
  c.actionHom_eq _ _ (c.torus_smul k)

private theorem torusPerm_pow (r : FiniteField.Nineˣ) (n : ℕ) :
    UnitaryThree.torusPerm (r ^ n) = UnitaryThree.torusPerm r ^ n := by
  let f : FiniteField.Nineˣ →* Equiv.Perm UnitaryThree.Point := {
    toFun := UnitaryThree.torusPerm
    map_one' := by
      apply Equiv.ext
      intro p
      cases p with
      | none => rfl
      | some q => exact congrArg some (UnitaryThree.scale_one q)
    map_mul' := by
      intro r s
      apply Equiv.ext
      intro p
      cases p with
      | none => rfl
      | some q => exact congrArg some (UnitaryThree.scale_mul r s q) }
  exact map_pow f r n

include c in
/-- Any Hermitian Borel coordinates extend to full coordinates once the local
swapping involution is available. -/
public theorem nonempty_coordinates
    (hlocal : SuzukiThreeLocalStructure G Ω a b Q) :
    Nonempty (SuzukiThreeCoordinates h b hb) := by
  let F := c.actionHom
  have htrans (v : UnitaryThree.Root) : UnitaryThree.rootPerm v ∈ F.range := by
    refine ⟨((c.rootEquiv.symm v : stabilizer G a) : G), ?_⟩
    simpa only [MulEquiv.apply_symm_apply] using c.actionHom_root (c.rootEquiv.symm v)
  have htorus (r : FiniteField.Nineˣ) : UnitaryThree.torusPerm r ∈ F.range := by
    refine ⟨((c.torusEquiv.symm r : stabilizer G a) : G), ?_⟩
    simpa only [MulEquiv.apply_symm_apply] using c.actionHom_torus (c.torusEquiv.symm r)
  have haff (s : Equiv.Perm UnitaryThree.Point) (hs : s ∈ F.range)
      (hsnone : s none = none) : ∃ (v : UnitaryThree.Root) (n : Fin 8),
      s = UnitaryThree.rootPerm v *
        UnitaryThree.torusPerm UnitaryThree.SwapRigidity.scalar ^ n.val := by
    obtain ⟨g, rfl⟩ := hs
    have hga : g • a = a := by
      apply (h.pointCoordinates b hb c.rootEquiv).injective
      have he := congrArg (fun p => F g p) (h.pointCoordinates_base b hb c.rootEquiv)
      change h.pointCoordinates b hb c.rootEquiv
        (g • (h.pointCoordinates b hb c.rootEquiv).symm
          (h.pointCoordinates b hb c.rootEquiv a)) = F g none at he
      rw [Equiv.symm_apply_apply, hsnone] at he
      simpa only [h.pointCoordinates_base] using he
    let g' : stabilizer G a := ⟨g, hga⟩
    obtain ⟨q, hq, _⟩ :=
      (Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp (h.root_complement b hb)) g'
    let k : stabilizer (stabilizer G a) b := ⟨q.val⁻¹ * g', hq⟩
    have hg : g = ((q : stabilizer G a) : G) * ((k : stabilizer G a) : G) := by
      change g = _ * (_⁻¹ * g)
      group
    obtain ⟨n, hn⟩ := UnitaryThree.SwapRigidity.scalar_powers (c.torusEquiv k)
    refine ⟨c.rootEquiv q, n, ?_⟩
    change c.actionHom g = _
    rw [hg, map_mul, c.actionHom_root, c.actionHom_torus, hn, torusPerm_pow]
  obtain ⟨t, ht, hta, _, htK⟩ := hlocal.swap_exists
  let k := c.torusEquiv.symm UnitaryThree.SwapRigidity.scalar
  have hk : F ((k : stabilizer G a) : G) =
      UnitaryThree.torusPerm UnitaryThree.SwapRigidity.scalar := by
    simpa only [k, MulEquiv.apply_symm_apply] using c.actionHom_torus k
  have hsq : F t ^ 2 = 1 := by rw [← map_pow, ht, map_one]
  have hn : F t none = some 1 := by
    rw [← h.pointCoordinates_base b hb c.rootEquiv]
    change h.pointCoordinates b hb c.rootEquiv
      (t • (h.pointCoordinates b hb c.rootEquiv).symm
        (h.pointCoordinates b hb c.rootEquiv a)) = some 1
    rw [Equiv.symm_apply_apply, hta, h.pointCoordinates_other]
  have hc : (F t)⁻¹ * UnitaryThree.torusPerm UnitaryThree.SwapRigidity.scalar * F t =
      UnitaryThree.torusPerm UnitaryThree.SwapRigidity.scalar ^ 5 := by
    rw [← hk, ← map_inv, ← map_mul, ← map_mul, htK, map_pow]
  obtain ⟨w, hw⟩ := UnitaryThree.SwapRigidity.swap_mem F.range htrans
    (htorus _) haff (F t) ⟨t, rfl⟩ hsq hn hc
  refine ⟨{ c with swap := w, swap_smul := ?_ }⟩
  intro x
  have he := congrArg (fun s : Equiv.Perm UnitaryThree.Point =>
    s (h.pointCoordinates b hb c.rootEquiv x)) hw
  change h.pointCoordinates b hb c.rootEquiv
    (w • (h.pointCoordinates b hb c.rootEquiv).symm
      (h.pointCoordinates b hb c.rootEquiv x)) = _ at he
  simpa only [Equiv.symm_apply_apply] using he

end SuzukiThreeBorelCoordinates

namespace SuzukiThreeHypotheses

/-- Suzuki's degree-28 action has full Hermitian coordinates, including the
reciprocal formula for a swapping element. -/
public theorem nonempty_coordinates
    {G Ω : Type*} [Group G] [MulAction G Ω] [FaithfulSMul G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q) (b : Ω) (hb : b ≠ a)
    (hlocal : SuzukiThreeLocalStructure G Ω a b Q) :
    Nonempty (SuzukiThreeCoordinates h b hb) := by
  obtain ⟨c⟩ := h.nonempty_borelCoordinates b hb hlocal
  exact c.nonempty_coordinates hlocal

end SuzukiThreeHypotheses
end Stellmacher.Recognition
