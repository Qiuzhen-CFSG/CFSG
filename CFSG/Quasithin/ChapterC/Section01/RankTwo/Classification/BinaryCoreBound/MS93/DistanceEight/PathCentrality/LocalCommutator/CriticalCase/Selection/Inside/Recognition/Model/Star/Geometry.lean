module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition.Model.Star.Relations
public import Theory.SpecificGroups.PSL3Two.InvolutionConjugacy
/-!
# The escaping-pair relation in the literal source action

One actor isomorphism carries the coordinate point stabilizer to the marked
source stabilizer. Maximality and the index-two core show that an actor outside
this stabilizer moves every seed vector outside the core. Conjugate the source
involution to the coordinate swap. Pulling back the two selected point vectors
places their nonzero differences in the same source displacement subgroup of
order at most two. The two differences coincide, giving the pair relation used
by `Relations`. Vectors in the core are already fixed by `Core`.

All translates use inverse images under actors, exactly the right-conjugate
convention of MS93 (1.6), printed pp.845–847. No whole-module displacement bound
or splitting of a central extension is assumed.
-/

@[expose] public section
open Subgroup Matrix
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
open Escape.Initial.Natural.Splitting
namespace Star
set_option backward.isDefEq.respectTransparency false

private def pointMover : Fin 7 → SL := ![
  ⟨!![1,0,0;0,1,0;0,0,1], by decide⟩,
  ⟨!![0,1,0;1,0,0;0,0,1], by decide⟩,
  ⟨!![1,1,0;1,0,0;0,0,1], by decide⟩,
  ⟨!![0,1,0;0,0,1;1,0,0], by decide⟩,
  ⟨!![1,1,0;0,0,1;1,0,0], by decide⟩,
  ⟨!![0,1,0;1,0,1;1,0,0], by decide⟩,
  ⟨!![1,1,0;1,0,1;1,0,0], by decide⟩]

private theorem point_reachable (v : Fin 3 → ZMod 2) (hv : v ≠ 0) :
    ∃ n : SL, n • (![1,0,0] : Fin 3 → ZMod 2) = v := by
  have h : ∀ v : Fin 3 → ZMod 2, v ≠ 0 →
      ∃ i : Fin 7, (pointMover i).val.mulVec ![1,0,0] = v := by decide +kernel
  obtain ⟨i, hi⟩ := h v hv
  exact ⟨pointMover i, hi⟩

private theorem mem_parabolic_iff (k : SL) : k ∈ PSL3Two.pointParabolicSL ↔
    k • (![1,0,0] : Fin 3 → ZMod 2) = ![1,0,0] := by
  rw [PSL3Two.mem_pointParabolicSL_iff]
  constructor
  · rintro ⟨h1,h2⟩
    have h00 : k.val 0 0 ≠ 0 := by
      intro hz
      have hd := k.property
      simp only [det_fin_three, hz, h1, h2, zero_mul, mul_zero, add_zero, sub_zero] at hd
      exact zero_ne_one hd
    have hbinary : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    have h0 := hbinary _ h00
    change k.val.mulVec ![1,0,0] = ![1,0,0]
    ext i
    fin_cases i <;>
      simp [mulVec, dotProduct, Fin.sum_univ_three, h0, h1, h2]
  · intro hk
    change k.val.mulVec ![1,0,0] = ![1,0,0] at hk
    constructor
    · simpa [mulVec, dotProduct, Fin.sum_univ_three]
        using congrFun hk 1
    · simpa [mulVec, dotProduct, Fin.sum_univ_three]
        using congrFun hk 2

/-- A single actual actor isomorphism aligns the source point stabilizer with the coordinate one. -/
theorem exists_point_marking (marking : SL ≃* SL) (point : Fin 3 → ZMod 2)
    (hne : point ≠ 0) : ∃ e : SL ≃* SL, ∀ k : SL,
      k ∈ PSL3Two.pointParabolicSL ↔ e k ∈ markedPointStabilizer marking point := by
  obtain ⟨n, hn⟩ := point_reachable point hne
  let e := (MulAut.conj n).trans marking.symm
  refine ⟨e, ?_⟩
  intro k
  rw [mem_parabolic_iff]
  change k • (![1,0,0] : Fin 3 → ZMod 2) = ![1,0,0] ↔
    marking (e k) • point = point
  simp only [e, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulAut.conj_apply]
  rw [← hn]
  simp only [mul_smul, inv_smul_smul, smul_left_cancel_iff]

private theorem swap_square : swap ^ 2 = 1 := by decide
private theorem swap_ne_one : swap ≠ 1 := by decide
private theorem first_escape : first⁻¹ * swap * first ∉ PSL3Two.pointParabolicSL := by
  rw [PSL3Two.mem_pointParabolicSL_iff]; decide
private theorem second_escape : second⁻¹ * swap * second ∉ PSL3Two.pointParabolicSL := by
  rw [PSL3Two.mem_pointParabolicSL_iff]; decide

variable {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]

omit [IsElementaryAbelian 2 E] in
/-- Every vector outside the common core detects an actor outside the point stabilizer. -/
theorem outside_moves_seed (ρ : SL →* MulAut E) (d : EscapingConfiguration ρ)
    (hline : (actionOrbitCore ρ d.seed).relIndex d.seed = 2)
    (e : SL ≃* SL) (he : ∀ k, k ∈ PSL3Two.pointParabolicSL ↔
      e k ∈ markedPointStabilizer d.marking d.point)
    (k : SL) (hk : k ∉ PSL3Two.pointParabolicSL)
    (w : E) (hw : w ∈ d.seed) (hwc : w ∉ actionOrbitCore ρ d.seed) :
    ρ (e k) w ≠ w := by
  let H := (MulAction.stabilizer (MulAut E) d.seed).comap (ρ.comp e.toMonoidHom)
  have hPH : PSL3Two.pointParabolicSL ≤ H := by
    intro x hx
    change d.seed.map (ρ (e x)).toMonoidHom = d.seed
    exact d.invariant _ ((he x).mp hx)
  have hntop : H ≠ ⊤ := by
    intro htop
    have hcore : actionOrbitCore ρ d.seed = d.seed := by
      apply le_antisymm (actionOrbitCore_le ρ d.seed)
      apply le_iInf
      intro g
      obtain ⟨x, hx⟩ := e.surjective g⁻¹
      have hh : x ∈ H := htop ▸ mem_top _
      change d.seed.map (ρ (e x)).toMonoidHom = d.seed at hh
      rw [hx] at hh
      exact hh.ge
    rw [hcore, relIndex_self] at hline
    contradiction
  have hH : PSL3Two.pointParabolicSL = H := eq_of_le_of_not_lt hPH
    (fun h => hntop (PSL3Two.isCoatom_pointParabolicSL.2 _ h))
  intro hfix
  apply hk
  rw [hH]
  change d.seed.map (ρ (e k)).toMonoidHom = d.seed
  have hfixed (u : E) (hu : u ∈ d.seed) : ρ (e k) u = u := by
    by_cases huc : u ∈ actionOrbitCore ρ d.seed
    · exact orbitCore_fixed_of_index_two ρ d hline _ _ huc
    · have hprod : u * w ∈ actionOrbitCore ρ d.seed :=
        ((actionOrbitCore ρ d.seed).subgroupOf d.seed).mul_mem_iff_of_index_two hline |>.mpr
          (show (⟨u,hu⟩ : d.seed) ∈ (actionOrbitCore ρ d.seed).subgroupOf d.seed ↔
            (⟨w,hw⟩ : d.seed) ∈ (actionOrbitCore ρ d.seed).subgroupOf d.seed from
            iff_of_false huc hwc)
      have hh := orbitCore_fixed_of_index_two ρ d hline (e k) _ hprod
      rw [map_mul, hfix] at hh
      exact mul_right_cancel hh
  apply le_antisymm
  · rintro _ ⟨u,hu,rfl⟩
    change ρ (e k) u ∈ d.seed
    rw [hfixed u hu]
    exact hu
  · intro u hu
    exact ⟨u, hu, hfixed u hu⟩

private theorem conjugate_involution (t : SL) (ht : t ≠ 1) (ht2 : t ^ 2 = 1)
    (e : SL ≃* SL) : ∃ n : SL, n * t * n⁻¹ = e swap := by
  have htwo : orderOf t = 2 := orderOf_eq_prime ht2 ht
  have hswap : orderOf (e swap) = 2 := by
    rw [e.orderOf_eq]
    exact orderOf_eq_prime swap_square swap_ne_one
  obtain ⟨a, ha⟩ := PSL3Two.involutions_conjugate (PSL3Two.equiv t)
    (PSL3Two.equiv (e swap)) ((PSL3Two.equiv.orderOf_eq _).trans htwo)
    ((PSL3Two.equiv.orderOf_eq _).trans hswap)
  refine ⟨PSL3Two.equiv.symm a, PSL3Two.equiv.injective ?_⟩
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply, MulAut.conj_apply] using ha

private theorem mem_rightConjugate_iff (K : Subgroup SL) (t g : SL) :
    t ∈ NormalizerTransfer.rightConjugate K g ↔ g * t * g⁻¹ ∈ K := by
  constructor
  · rintro ⟨k,hk,rfl⟩
    change g * (g⁻¹ * k * (g⁻¹)⁻¹) * g⁻¹ ∈ K
    rw [show g * (g⁻¹ * k * (g⁻¹)⁻¹) * g⁻¹ = k by group]
    exact hk
  · intro h
    refine ⟨g * t * g⁻¹, h, ?_⟩
    change g⁻¹ * (g * t * g⁻¹) * (g⁻¹)⁻¹ = t
    group

private theorem small_nonzero_eq {F : Type*} [Group F] [Finite F]
    {D : Subgroup F} (hD : Nat.card D ≤ 2)
    {x y : F} (hx : x ∈ D) (hy : y ∈ D) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have hcard : Nat.card D = 2 := by
    have := (Subgroup.one_lt_card_iff_ne_bot D).mpr
      (fun h => hx1 (by simpa only [h, mem_bot] using hx))
    omega
  obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : D)).mp hcard
  exact congrArg Subtype.val ((hz (⟨x,hx⟩ : D) (fun h => hx1 (congrArg Subtype.val h))).trans
    (hz (⟨y,hy⟩ : D) (fun h => hy1 (congrArg Subtype.val h))).symm)

/-- The literal source escaping bound gives the pair relation in the normalized marking. -/
theorem pair_relation (ρ : SL →* MulAut E) (d : EscapingConfiguration ρ)
    (hline : (actionOrbitCore ρ d.seed).relIndex d.seed = 2)
    (e : SL ≃* SL) (he : ∀ k, k ∈ PSL3Two.pointParabolicSL ↔
      e k ∈ markedPointStabilizer d.marking d.point)
    (w : E) (hw : w ∈ d.seed) :
    ρ (e swap) (ρ (e first) w * ρ (e second) w) = ρ (e first) w * ρ (e second) w := by
  by_cases hwc : w ∈ actionOrbitCore ρ d.seed
  · simp only [orbitCore_fixed_of_index_two ρ d hline _ w hwc, map_mul]
  let σ := ρ.comp e.toMonoidHom
  obtain ⟨n, hn⟩ := conjugate_involution d.involution d.involution_ne_one d.involution_sq e
  let pull (r : SL) := ρ (n⁻¹ * e r) w
  let D := actionDisplacement ρ (zpowers d.involution)
    (actionEscapingSpan ρ (markedPointStabilizer d.marking d.point) d.involution d.seed)
  have htransport (r : SL) : ρ n (actionDifference ρ d.involution (pull r)) =
      actionDifference σ swap (σ r w) := by
    change ρ n ((pull r)⁻¹ * ρ d.involution (pull r)) =
      (ρ (e r) w)⁻¹ * ρ (e swap) (ρ (e r) w)
    rw [map_mul, map_inv]
    have hnx : ρ n (pull r) = ρ (e r) w := by
      change ρ n (ρ (n⁻¹ * e r) w) = _
      rw [← MulAut.mul_apply, ← ρ.map_mul, mul_inv_cancel_left]
    rw [hnx]
    congr 1
    change ρ n (ρ d.involution (ρ (n⁻¹ * e r) w)) = _
    simp only [← MulAut.mul_apply, ← ρ.map_mul]
    apply congrArg (fun a : SL => ρ a w)
    rw [← hn]
    group
  have hmem (r : SL) (hr : r⁻¹ * swap * r ∉ PSL3Two.pointParabolicSL) :
      actionDifference ρ d.involution (pull r) ∈ D ∧
        actionDifference ρ d.involution (pull r) ≠ 1 := by
    let g := (e r)⁻¹ * n
    have htest : g * d.involution * g⁻¹ = e (r⁻¹ * swap * r) := by
      rw [e.map_mul, e.map_mul, e.map_inv, ← hn]
      dsimp only [g]
      group
    have hescape : d.involution ∉ NormalizerTransfer.rightConjugate
        (markedPointStabilizer d.marking d.point) g := by
      rw [mem_rightConjugate_iff, htest]
      exact fun h => hr ((he _).mpr h)
    have hpull : pull r ∈ actionConjugate ρ d.seed g := by
      refine ⟨w,hw,?_⟩
      change ρ g⁻¹ w = ρ (n⁻¹ * e r) w
      simp only [g, _root_.mul_inv_rev, inv_inv]
    constructor
    · change (pull r)⁻¹ * ρ d.involution (pull r) ∈ actionDisplacement ρ
        (zpowers d.involution) (actionEscapingSpan ρ
          (markedPointStabilizer d.marking d.point) d.involution d.seed)
      apply Subgroup.subset_closure
      refine ⟨d.involution, mem_zpowers _, pull r, ?_, rfl⟩
      exact (show actionConjugate ρ d.seed g ≤ actionEscapingSpan ρ
        (markedPointStabilizer d.marking d.point) d.involution d.seed from
        le_iSup_of_le g (le_iSup_of_le hescape le_rfl)) hpull
    · intro hz
      have hd : actionDifference σ swap (σ r w) = 1 := by
        rw [← htransport, hz, map_one]
      have hf : σ swap (σ r w) = σ r w := (inv_mul_eq_one.mp hd).symm
      have hh := congrArg (σ r⁻¹) hf
      have hfix : ρ (e (r⁻¹ * swap * r)) w = w := by
        change σ (r⁻¹ * swap * r) w = w
        simpa only [← MulAut.mul_apply, ← σ.map_mul, inv_mul_cancel, map_one,
          MulAut.one_apply, ← mul_assoc] using hh
      exact outside_moves_seed ρ d hline e he _ hr w hw hwc hfix
  obtain ⟨ha,ha1⟩ := hmem first first_escape
  obtain ⟨hb,hb1⟩ := hmem second second_escape
  have heq := congrArg (ρ n) (small_nonzero_eq (D := D) d.small ha hb ha1 hb1)
  rw [htransport, htransport] at heq
  have hsquare : actionDifference σ swap (σ second w) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) _
  have hz : actionDifference σ swap (σ first w * σ second w) = 1 := by
    rw [map_mul, heq, ← pow_two, hsquare]
  exact (inv_mul_eq_one.mp hz).symm

end Star
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
