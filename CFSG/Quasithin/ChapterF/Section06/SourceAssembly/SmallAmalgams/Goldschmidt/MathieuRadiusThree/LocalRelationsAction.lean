module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalRelationsLabels
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ArcSetup
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Syntheme.LargeKernel
public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals
/-!
# The literal radius-two action in the radius-three branch

Three-arc regularity supplies a mixed binary flip and the full three-branch
projection. A label four steps along the canonical track is an even
transposition lift. The finite wreath calculation therefore turns any odd
six-point image into an actual single-pair flip. Parity is unchanged under
vertex transport or a different branch frame.

The source order-eight label calculation excludes a single-pair flip: its
centralizer in that label group contains six elements and hence all eight.
This identifies the literal action image with the even wreath subgroup S₄.
The extra order-eight premise is discharged by the track-commutator assembly.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(6.12.1)--(6.12.4), printed pp.403--404.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup SimpleGraph Theory.GroupAction.CubicTree
open Subgroup.CosetGeometry
open Theory.SpecificGroups.SymmetricSix.SynthemeCalculation
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}
namespace BranchFrame
variable {a : RankTwo.Vertex F} (f : BranchFrame F a) (h : LargeTreeSource F s)
private theorem perm_three_ext (σ τ : Equiv.Perm (Fin 3))
    (h0 : σ 0 = τ 0) (h1 : σ 1 = τ 1) : σ = τ := by
  revert σ τ
  decide +kernel

include h in
theorem branchAction_surjective : Function.Surjective f.branchAction := by
  intro σ
  let p : BasedWalk (RankTwo.graph F) 2 (f.e 0).val :=
    ⟨⟨a, (show (RankTwo.graph F).Adj a (f.e 0).val from (f.e 0).property).symm⟩, ⟨⟨(f.e 1).val, (f.e 1).property⟩, PUnit.unit⟩⟩
  let q : BasedWalk (RankTwo.graph F) 2 (f.e (σ 0)).val :=
    ⟨⟨a, (show (RankTwo.graph F).Adj a (f.e (σ 0)).val from (f.e (σ 0)).property).symm⟩,
      ⟨⟨(f.e (σ 1)).val, (f.e (σ 1)).property⟩, PUnit.unit⟩⟩
  have hp : p.Nonbacktracking := by
    refine ⟨?_, trivial⟩
    intro hh
    have := f.e.injective (Subtype.ext hh)
    exact (by decide : (1 : Fin 3) ≠ 0) this
  have hq : q.Nonbacktracking := by
    refine ⟨?_, trivial⟩
    intro hh
    have := σ.injective (f.e.injective (Subtype.ext hh))
    exact (by decide : (1 : Fin 3) ≠ 0) this
  have ht : (f.e 0).val.type = (f.e (σ 0)).val.type := by
    have h0 := (f.e 0).property.1
    have h1 := (f.e (σ 0)).property.1
    cases ha : a.type <;> cases h0' : (f.e 0).val.type <;>
      cases h1' : (f.e (σ 0)).val.type <;> simp_all
  obtain ⟨g, hg⟩ := CubicTreeAction.congruent_arcs h.action.toCubicTreeAction s h.regular
    (by have := h.five_le; omega : 2 ≤ s) p q hp hq ht
  have hc : g • (f.e 0).val = (f.e (σ 0)).val ∧ g • a = a ∧
      g • (f.e 1).val = (f.e (σ 1)).val := by
    simpa [p, q, BasedWalk.vertices] using hg
  refine ⟨⟨g, hc.2.1⟩, perm_three_ext _ _ ?_ ?_⟩
  · apply f.e.injective
    apply Subtype.ext
    rw [f.branchAction_eval]
    exact hc.1
  · apply f.e.injective
    apply Subtype.ext
    rw [f.branchAction_eval]
    exact hc.2.2

theorem blockProjection_surjective : Function.Surjective
    (quotientHom.comp (f.blockAction h.action.toCubicTreeAction).range.subtype) := by
  intro σ
  obtain ⟨g, hg⟩ := f.branchAction_surjective h σ
  exact ⟨⟨f.blockAction h.action.toCubicTreeAction g, ⟨g, rfl⟩⟩, hg⟩

theorem exists_mixed_flip : ∃ g : RankTwo.stabilizer F a,
    (f.blockAction h.action.toCubicTreeAction g).right = 1 ∧
    (f.blockAction h.action.toCubicTreeAction g).left.toAdd 0 = 0 ∧
    (f.blockAction h.action.toCubicTreeAction g).left.toAdd 1 = 1 := by
  let p : BasedWalk (RankTwo.graph F) 3 (f.c 0) :=
    ⟨⟨(f.e 0).val, (f.c_adj 0).symm⟩,
      ⟨⟨a, (show (RankTwo.graph F).Adj a (f.e 0).val from (f.e 0).property).symm⟩,
        ⟨⟨(f.e 1).val, (f.e 1).property⟩, PUnit.unit⟩⟩⟩
  have hp : p.Nonbacktracking := by
    refine ⟨(f.c_ne_center 0).symm, ?_, trivial⟩
    intro hh
    have := f.e.injective (Subtype.ext hh)
    exact (by decide : (1 : Fin 3) ≠ 0) this
  obtain ⟨g, hg, hgc⟩ := h.regular 3 (f.c 0) p
    (by have := h.five_le; omega) hp (f.c 1) (f.d 1)
      ⟨f.c_adj 1, f.c_ne_center 1⟩ ⟨f.d_adj 1, f.d_ne_center 1⟩
  have h0 : g • (f.c 0) = f.c 0 := hg _ (by simp [p, BasedWalk.vertices])
  have he0 : g • (f.e 0).val = (f.e 0).val := hg _ (by simp [p, BasedWalk.vertices])
  have ha : g • a = a := hg _ (by simp [p, BasedWalk.vertices])
  have he1 : g • (f.e 1).val = (f.e 1).val := hg _ (by simp [p, BasedWalk.vertices])
  let k : RankTwo.stabilizer F a := ⟨g, ha⟩
  have hk : f.branchAction k = 1 := by
    apply perm_three_ext
    · apply f.e.injective
      apply Subtype.ext
      rw [f.branchAction_eval]
      exact he0
    · apply f.e.injective
      apply Subtype.ext
      rw [f.branchAction_eval]
      exact he1
  have hs0 : f.sphereAction h.action.toCubicTreeAction k (0,0) = (0,0) := by
    apply f.point_injective h.action.toCubicTreeAction
    rw [f.sphereAction_eval]
    exact h0
  have hs1 : f.sphereAction h.action.toCubicTreeAction k (1,0) = (1,1) := by
    apply f.point_injective h.action.toCubicTreeAction
    rw [f.sphereAction_eval]
    exact hgc
  refine ⟨k, hk, ?_, ?_⟩
  · have hh := congrArg Prod.snd hs0
    rw [← f.blockAction_coordinates] at hh
    simpa [coordinateHom, f.blockAction_right, hk] using hh
  · have hh := congrArg Prod.snd hs1
    rw [← f.blockAction_coordinates] at hh
    simpa [coordinateHom, f.blockAction_right, hk] using hh

local instance : DecidableEq Model := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right)
    ⟨fun h => SemidirectProduct.ext h.1 h.2,
      fun h => ⟨congrArg SemidirectProduct.left h, congrArg SemidirectProduct.right h⟩⟩

private theorem involution_fixed_point_even_swap (m : Model) (hsq : m^2 = 1)
    (hne : m.right ≠ 1) (hfix : ∃ x, coordinateHom m x = x) :
    m.right.IsSwap ∧ (modelHom m).sign = 1 := by
  revert m
  simp only [Equiv.Perm.IsSwap]
  decide +kernel

theorem exists_label_even_swap (d : CanonicalLabelSetup F s) (hr : d.radius = 3)
    (ha : a.type = d.side) :
    ∃ g : RankTwo.stabilizer F a,
      g.val ∈ d.labelBall a 4 ∧ (f.branchAction g).IsSwap ∧
      (modelHom (f.blockAction h.action.toCubicTreeAction g)).sign = 1 := by
  obtain ⟨g, hga⟩ := (RankTwo.same_orbit_iff F (d.track.vertex d.center) a).mpr
    (d.center_type.trans ha.symm)
  let b := d.track.vertex (d.center + 2*2)
  let z₀ := d.label b
  let z := (MulAut.conj g) z₀
  have hfixed (i : ℤ) (hi : d.center ≤ i ∧ i ≤ d.center + 8) :
      z • (g • d.track.vertex i) = g • d.track.vertex i := by
    have hh : z₀ • d.track.vertex i = d.track.vertex i :=
      (d.shifted_fixed_iff 2 i).mpr (by rw [hr]; omega)
    simpa only [z, MulAut.conj_apply, mul_smul, inv_smul_smul] using
      congrArg (g • ·) hh
  have hzmem : z ∈ RankTwo.stabilizer F a := by
    rw [show a = g • d.track.vertex d.center from hga.symm]
    exact hfixed d.center (by omega)
  let k : RankTwo.stabilizer F a := ⟨z, hzmem⟩
  have hsq : (f.blockAction h.action.toCubicTreeAction k)^2 = 1 := by
    have hzsq : z₀ ^ 2 = 1 := by
      simpa only [z₀, d.order_two b (d.shifted_type 2)] using pow_orderOf_eq_one z₀
    have hk : k^2 = 1 := by
      apply Subtype.ext
      change z^2 = 1
      change ((MulAut.conj g) z₀)^2 = 1
      rw [← map_pow, hzsq, map_one]
    rw [← map_pow, hk, map_one]
  have hne : (f.blockAction h.action.toCubicTreeAction k).right ≠ 1 := by
    intro he
    have hadj : (RankTwo.graph F).Adj a (g • d.track.vertex (d.center-1)) := by
      rw [← hga]
      apply (translationGraphIso F g).toHom.map_adj
      convert (d.track.adjacent (d.center-1)).symm using 1; congr 1; omega
    obtain ⟨i, hi⟩ := f.e.surjective ⟨_, hadj⟩
    have hi' : (f.e i).val = g • d.track.vertex (d.center-1) := congrArg Subtype.val hi
    have hh := f.branchAction_eval k i
    change f.branchAction k = 1 at he
    rw [he] at hh
    simp only [Equiv.Perm.one_apply] at hh
    rw [hi'] at hh
    have hfix : z₀ • d.track.vertex (d.center-1) = d.track.vertex (d.center-1) := by
      apply (MulAction.toPerm g).injective
      change g • (z₀ • d.track.vertex (d.center-1)) = g • d.track.vertex (d.center-1)
      simpa only [k, z, MulAut.conj_apply, mul_smul, inv_smul_smul] using hh.symm
    have hf := (d.shifted_fixed_iff 2 (d.center-1)).mp hfix
    rw [hr] at hf
    omega
  have hfix : ∃ x, coordinateHom (f.blockAction h.action.toCubicTreeAction k) x = x := by
    have hd : (RankTwo.graph F).dist a (g • d.track.vertex (d.center+2)) = 2 := by
      rw [← hga, RankTwo.dist_smul]
      apply (DistanceTwoGeometry.dist_eq_two_iff h.action.tree).mpr
      refine ⟨?_, d.track.vertex (d.center+1), d.track.adjacent d.center, ?_⟩
      · intro he
        have hh := d.track.injective he
        omega
      · convert d.track.adjacent (d.center+1) using 1; congr 1; omega
    obtain ⟨x, hx⟩ := (f.sphereEquiv h.action.toCubicTreeAction).surjective ⟨_, hd⟩
    have hx' : f.point x = g • d.track.vertex (d.center+2) := congrArg Subtype.val hx
    refine ⟨x, ?_⟩
    rw [f.blockAction_coordinates]
    apply f.point_injective h.action.toCubicTreeAction
    rw [f.sphereAction_eval, hx']
    exact hfixed _ (by omega)
  have hkball : k.val ∈ d.labelBall a 4 := by
    change (MulAut.conj g) (d.label b) ∈ d.labelBall a 4
    rw [show (MulAut.conj g) (d.label b) = d.label (g • b) from
      (d.conjugate g b (d.shifted_type 2)).symm]
    apply d.label_mem_labelBall (w := g • b) (show (g • b).type = d.side from d.shifted_type 2)
    rw [← hga, RankTwo.dist_smul]
    have hd := SimpleGraph.dist_le (d.track.arc d.center 4).toWalk
    simpa only [BasedWalk.length_toWalk, Track.arc_endpoint, b, Nat.cast_ofNat,
      show (2 : ℤ)*2 = 4 from rfl] using hd
  exact ⟨k, hkball, involution_fixed_point_even_swap _ hsq hne hfix⟩

theorem exists_even_swap (d : CanonicalLabelSetup F s) (hr : d.radius = 3)
    (ha : a.type = d.side) :
    ∃ g : RankTwo.stabilizer F a,
      (f.branchAction g).IsSwap ∧
      (modelHom (f.blockAction h.action.toCubicTreeAction g)).sign = 1 := by
  obtain ⟨g, _, ht, he⟩ := f.exists_label_even_swap h d hr ha
  exact ⟨g, ht, he⟩

theorem blockAction_kernel_card_ge :
    4 ≤ Nat.card ((f.blockAction h.action.toCubicTreeAction).range ⊓ core : Subgroup Model) := by
  obtain ⟨g, hg, h0, h1⟩ := f.exists_mixed_flip h
  exact large_kernel_of_mixed_flip _ (f.blockProjection_surjective h)
    (f.blockAction h.action.toCubicTreeAction g) ⟨⟨g, rfl⟩, hg⟩ h0 h1

theorem blockAction_kernel_dichotomy :
    (f.blockAction h.action.toCubicTreeAction).range ⊓ core = evenKernel ∨
    (f.blockAction h.action.toCubicTreeAction).range ⊓ core = core :=
  large_kernel_dichotomy _ (f.blockProjection_surjective h) (f.blockAction_kernel_card_ge h)

theorem exists_singleFlip_of_not_even (d : CanonicalLabelSetup F s)
    (hr : d.radius = 3) (ha : a.type = d.side)
    (hne : ¬ (f.blockAction h.action.toCubicTreeAction).range ≤ evenModel)
    (i : Fin 3) : ∃ g : RankTwo.stabilizer F a,
      f.blockAction h.action.toCubicTreeAction g = singleFlip i := by
  let H := (f.blockAction h.action.toCubicTreeAction).range
  have hparity : ((Equiv.Perm.sign.comp modelHom).comp H.subtype) ≠ 1 := by
    intro he
    apply hne
    intro x hx
    have hh := DFunLike.congr_fun he (⟨x,hx⟩ : H)
    exact hh
  obtain ⟨g, hg, h0, h1⟩ := f.exists_mixed_flip h
  obtain ⟨t, ht, hte⟩ := f.exists_even_swap h d hr ha
  exact singleFlips_mem_of_nontrivial_parity_of_mixed_flip H
    (f.blockProjection_surjective h) (f.blockAction h.action.toCubicTreeAction g)
    ⟨⟨g, rfl⟩, hg⟩ h0 h1 hparity
    ⟨f.blockAction h.action.toCubicTreeAction t, ⟨t,rfl⟩⟩ ht hte i

/-- The extracted model element flips the prescribed literal forward pair. -/
theorem singleFlip_smul_point (g : RankTwo.stabilizer F a) (i : Fin 3)
    (hg : f.blockAction h.action.toCubicTreeAction g = singleFlip i)
    (j : Fin 3) (b : ZMod 2) :
    g.val • f.point (j,b) = f.point (j, b + if j = i then 1 else 0) := by
  rw [← f.sphereAction_eval h.action.toCubicTreeAction g (j,b),
    ← f.blockAction_coordinates, hg]
  rfl

theorem blockAction_eq_evenModel_of_even
    (heven : (f.blockAction h.action.toCubicTreeAction).range ≤ evenModel) :
    (f.blockAction h.action.toCubicTreeAction).range = evenModel := by
  let H := (f.blockAction h.action.toCubicTreeAction).range
  let φ := quotientHom.comp H.subtype
  have hkcard : Nat.card φ.ker = Nat.card (H ⊓ core : Subgroup Model) := by
    apply Nat.card_congr
    exact {
      toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
      invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  have hcount := φ.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (f.blockProjection_surjective h),
    card_top, hkcard] at hcount
  have hthree : Nat.card Three = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  rw [hthree] at hcount
  apply eq_of_le_of_card_ge heven
  rw [evenModel_card]
  have hh := f.blockAction_kernel_card_ge h
  change 4 ≤ Nat.card (H ⊓ core : Subgroup Model) at hh
  change 24 ≤ Nat.card H
  change Nat.card (H ⊓ core : Subgroup Model) * 6 = Nat.card H at hcount
  omega

/-- Once the source contradiction excludes odd six-point actions, the actual
radius-two image is the tetrahedral group. -/
theorem blockAction_symmetricFour_of_even
    (heven : (f.blockAction h.action.toCubicTreeAction).range ≤ evenModel) :
    Nonempty ((f.blockAction h.action.toCubicTreeAction).range ≃* Equiv.Perm (Fin 4)) :=
  ⟨(MulEquiv.subgroupCongr (f.blockAction_eq_evenModel_of_even h heven)).trans
    (evenModelEquiv.trans
      Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals.edgeEquiv.symm)⟩

/-- Parity of the literal radius-two action is independent of the frame and
of the choice of a vertex in the same orbit. -/
theorem blockAction_even_iff_of_same_type {b : RankTwo.Vertex F}
    (fb : BranchFrame F b) (htype : a.type = b.type) :
    (f.blockAction h.action.toCubicTreeAction).range ≤ evenModel ↔
      (fb.blockAction h.action.toCubicTreeAction).range ≤ evenModel := by
  suffices hforward : ∀ {a b : RankTwo.Vertex F} (f : BranchFrame F a)
      (fb : BranchFrame F b), a.type = b.type →
      (fb.blockAction h.action.toCubicTreeAction).range ≤ evenModel →
      (f.blockAction h.action.toCubicTreeAction).range ≤ evenModel from
    ⟨hforward fb f htype.symm, hforward f fb htype⟩
  intro a b f fb hab hb
  obtain ⟨g, hg⟩ := (RankTwo.same_orbit_iff F a b).mpr hab
  let e : sphereSet a ≃ sphereSet b := {
    toFun := fun x => ⟨g • x.val, by
      have he := RankTwo.dist_smul F g a x.val
      rw [hg] at he
      exact he.trans x.property⟩
    invFun := fun x => ⟨g⁻¹ • x.val, by
      have he := RankTwo.dist_smul F g⁻¹ b x.val
      have hga : g⁻¹ • b = a := by rw [← hg, inv_smul_smul]
      rw [hga] at he
      exact he.trans x.property⟩
    left_inv := fun x => Subtype.ext (inv_smul_smul g x.val)
    right_inv := fun x => Subtype.ext (smul_inv_smul g x.val) }
  let q := (f.sphereEquiv h.action.toCubicTreeAction).trans
    (e.trans (fb.sphereEquiv h.action.toCubicTreeAction).symm)
  have hq (x : Fin 3 × ZMod 2) : fb.point (q x) = g • f.point x := by
    change ((fb.sphereEquiv h.action.toCubicTreeAction)
      ((fb.sphereEquiv h.action.toCubicTreeAction).symm
        (e ((f.sphereEquiv h.action.toCubicTreeAction) x)))).val = _
    rw [Equiv.apply_symm_apply]
    rfl
  rintro m ⟨k, rfl⟩
  let k' : RankTwo.stabilizer F b := ⟨g * k.val * g⁻¹, by
    change (g * k.val * g⁻¹) • b = b
    rw [← hg]
    simp only [mul_smul, inv_smul_smul]
    rw [show k.val • a = a from k.property]⟩
  have heq : (f.sphereAction h.action.toCubicTreeAction k).sign =
      (fb.sphereAction h.action.toCubicTreeAction k').sign := by
    apply Equiv.Perm.sign_eq_sign_of_equiv _ _ q
    intro x
    apply fb.point_injective h.action.toCubicTreeAction
    rw [hq, f.sphereAction_eval, fb.sphereAction_eval, hq]
    change g • (k.val • f.point x) = (g*k.val*g⁻¹) • (g • f.point x)
    simp only [mul_smul, inv_smul_smul]
  have hmodel (m : Model) : (modelHom m).sign = (coordinateHom m).sign :=
    Equiv.Perm.sign_permCongr letterEquiv (coordinateHom m)
  have htarget : (modelHom (fb.blockAction h.action.toCubicTreeAction k')).sign = 1 :=
    hb ⟨k',rfl⟩
  change (modelHom (f.blockAction h.action.toCubicTreeAction k)).sign = 1
  rw [hmodel, f.blockAction_coordinates, heq]
  simpa only [hmodel, fb.blockAction_coordinates] using htarget

/-- In the order-eight label group a single pair flip would fix six elements.
Its centralizer is a subgroup, so divisibility forces it to fix all eight,
contradicting the distinct labels on the flipped pair. -/
theorem blockAction_even_of_labelBall_card_eight
    (d : CanonicalLabelSetup F s) (hr : d.radius = 3) (ha : a.type = d.side)
    (hcard : Nat.card (d.labelBall a 2) = 8) :
    (f.blockAction h.action.toCubicTreeAction).range ≤ evenModel := by
  classical
  by_contra hne
  obtain ⟨g, hg⟩ := f.exists_singleFlip_of_not_even h d hr ha hne 2
  let A := d.labelBall a 2
  let : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let C := (centralizer ({g.val} : Set G)).subgroupOf A
  let v : Option (Fin 2 × ZMod 2) → RankTwo.Vertex F :=
    fun x => x.elim a (fun x => f.point (x.1.castSucc, x.2))
  have hvtype (x : Option (Fin 2 × ZMod 2)) : (v x).type = d.side := by
    cases x with
    | none => exact ha
    | some x =>
      have he := (RankTwo.even_dist_iff F h.action.generated a
        (f.point (x.1.castSucc,x.2))).mp
        (by rw [f.point_dist h.action.toCubicTreeAction]; decide)
      exact he.symm.trans ha
  have hvdist (x : Option (Fin 2 × ZMod 2)) : (RankTwo.graph F).dist a (v x) ≤ 2 := by
    cases x with
    | none => exact (by simp [v])
    | some x => exact le_of_eq (f.point_dist h.action.toCubicTreeAction _)
  have hvinj : Function.Injective v := by
    intro x y he
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y => exact ((f.point_ne_center _) he.symm).elim
    | some x =>
      cases y with
      | none => exact ((f.point_ne_center _) he).elim
      | some y =>
        have hh := f.point_injective h.action.toCubicTreeAction he
        apply congrArg some
        apply Prod.ext
        · exact Fin.castSucc_injective 2 (congrArg Prod.fst hh)
        · exact congrArg (fun x : Fin 3 × ZMod 2 => x.2) hh
  have hvfix (x : Option (Fin 2 × ZMod 2)) : g.val • v x = v x := by
    cases x with
    | none => exact g.property
    | some x =>
      have hn : x.1.castSucc ≠ (2 : Fin 3) := by
        intro he
        have hh := congrArg Fin.val he
        have hi := x.1.isLt
        change (x.1 : ℕ) = 2 at hh
        omega
      simpa only [v, Option.elim_some, hn, ↓reduceIte, add_zero] using
        f.singleFlip_smul_point h g 2 hg x.1.castSucc x.2
  have hlC (x : Option (Fin 2 × ZMod 2)) :
      (⟨d.label (v x), d.label_mem_labelBall (hvtype x) (hvdist x)⟩ : A) ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    have hh := d.conjugate g.val (v x) (hvtype x)
    rw [hvfix x] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  let l : Option (Fin 2 × ZMod 2) → C := fun x =>
    ⟨⟨d.label (v x), d.label_mem_labelBall (hvtype x) (hvdist x)⟩, hlC x⟩
  have hlinj : Function.Injective l := by
    intro x y he
    apply hvinj
    by_contra hvne
    have hdist : (RankTwo.graph F).dist (v x) (v y) ≤ s := by
      have ht := h.action.tree.connected.dist_triangle (u := v x) (v := a) (w := v y)
      rw [SimpleGraph.dist_comm (u := v x) (v := a)] at ht
      have hx := hvdist x
      have hy := hvdist y
      have hs := h.five_le
      omega
    exact d.label_ne_of_short_dist h (hvtype x) (hvtype y) hvne hdist
      (congrArg (fun k : C => k.val.val) he)
  have hlne (x : Option (Fin 2 × ZMod 2)) : l x ≠ 1 := by
    intro he
    have hh := d.order_two (v x) (hvtype x)
    have he' : d.label (v x) = 1 := congrArg (fun k : C => k.val.val) he
    rw [he', orderOf_one] at hh
    omega
  let u : Option (Option (Fin 2 × ZMod 2)) → C := fun x => x.elim 1 l
  have hu : Function.Injective u := by
    intro x y he
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y => exact (hlne y he.symm).elim
    | some x =>
      cases y with
      | none => exact (hlne x he).elim
      | some y => exact congrArg some (hlinj he)
  have hcge : 6 ≤ Nat.card C := by
    have hc := Nat.card_le_card_of_injective u hu
    have he : Nat.card (Option (Option (Fin 2 × ZMod 2))) = 6 := by
      rw [Nat.card_eq_fintype_card]
      simp
    exact he ▸ hc
  have hcdiv : Nat.card C ∣ 8 := hcard ▸ C.card_subgroup_dvd_card
  have hcle : Nat.card C ≤ 8 := Nat.le_of_dvd (by decide) hcdiv
  have hceq : Nat.card C = 8 := by
    interval_cases hn : Nat.card C <;> norm_num at *
  have hctop : C = ⊤ := C.eq_top_of_card_eq (hceq.trans hcard.symm)
  have hc : d.label (f.c 2) * g.val = g.val * d.label (f.c 2) := by
    apply mem_centralizer_singleton_iff.mp
    have hh : (⟨d.label (f.c 2), d.label_mem_labelBall
        ((f.c_type h.action.toCubicTreeAction 2).trans ha)
        (le_of_eq (f.c_dist h.action.toCubicTreeAction 2))⟩ : A) ∈ C := by
      rw [hctop]
      trivial
    exact hh
  have hswap : g.val • f.c 2 = f.d 2 := by
    simpa [point] using f.singleFlip_smul_point h g 2 hg 2 0
  have he : d.label (f.c 2) = d.label (f.d 2) := by
    have hh := d.conjugate g.val (f.c 2) ((f.c_type h.action.toCubicTreeAction 2).trans ha)
    rw [hswap, ← hc, mul_inv_cancel_right] at hh
    exact hh.symm
  apply d.label_ne_of_short_dist h
    ((f.c_type h.action.toCubicTreeAction 2).trans ha)
    ((f.d_type h.action.toCubicTreeAction 2).trans ha) (f.c_ne_d 2) ?_ he
  have ht := h.action.tree.connected.dist_triangle (u := f.c 2) (v := a) (w := f.d 2)
  rw [SimpleGraph.dist_comm (u := f.c 2) (v := a), f.c_dist h.action.toCubicTreeAction,
    f.d_dist h.action.toCubicTreeAction] at ht
  have hs := h.five_le
  omega

/-- The source order-eight label calculation completes the radius-two action
image in (6.12.2), with the original stabilizer and quotient conventions. -/
theorem blockAction_symmetricFour_of_labelBall_card_eight
    (d : CanonicalLabelSetup F s) (hr : d.radius = 3) (ha : a.type = d.side)
    (hcard : Nat.card (d.labelBall a 2) = 8) :
    Nonempty ((f.blockAction h.action.toCubicTreeAction).range ≃* Equiv.Perm (Fin 4)) :=
  f.blockAction_symmetricFour_of_even h
    (f.blockAction_even_of_labelBall_card_eight h d hr ha hcard)

end BranchFrame
end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
