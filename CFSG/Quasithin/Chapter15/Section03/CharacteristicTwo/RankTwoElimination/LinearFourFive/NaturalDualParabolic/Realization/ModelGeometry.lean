module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ProjectedAction.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Repeated.PlaneGeometry
public import Theory.GroupTheory.PResidual.NormalizedGenerators
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Basic

/-!
# Fixed spaces for the binary natural-plus-dual plane model

For a rank-two plane in the binary four-dimensional natural module, the cubic
closure of its full parabolic has zero fixed space on the natural-plus-dual
module.  At a nonzero point of the plane, the two-residual of the intersection
with the point stabilizer has zero fixed covector space.  Coordinates identify
the plane with the first summand of `F₂² ⊕ F₂²`; order-three Levi elements and
 their conjugates by the plane radical give the two calculations while retaining
the full unipotent radical.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.24,
printed pp.1129–1130 (PDF pp.1146–1147).
-/

@[expose] public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers.Pure
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.ComponentIntersection
open Theory.LinearAlgebra

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ModelGeometry

abbrev F := ZMod 2
abbrev Vec := Fin 2 → F
abbrev Pair := Vec × Vec
abbrev Lin := BinaryLinear.GL Pair
abbrev P : Submodule F Pair := (⊤ : Submodule F Vec).prod (⊥ : Submodule F Vec)
private def cubic : BinaryLinear.GL Vec where
  toFun v := ![v 1, v 0 + v 1]
  invFun v := ![v 0 + v 1, v 0]
  left_inv := by decide
  right_inv := by decide
  map_add' := by decide
  map_smul' := by decide
private theorem cubic_order : orderOf cubic = 3 := by
  apply (orderOf_eq_prime_iff (p := 3)).mpr
  constructor
  · ext v i; exact (by decide : ∀ v : Vec, ∀ i : Fin 2, cubic (cubic (cubic v)) i = v i) v i
  · intro he
    have hh := LinearEquiv.congr_fun he (![1, 0] : Vec)
    have hh' := congrFun hh 0
    norm_num [cubic] at hh'
private theorem cubic_fixed {v : Vec} (h : cubic v = v) : v = 0 :=
  (by decide : ∀ v : Vec, cubic v = v → v = 0) v h
private def diagonal : Lin := (1 : BinaryLinear.GL Vec).prodCongr cubic
private theorem diagonal_order : orderOf diagonal = 3 := by
  apply (orderOf_eq_prime_iff (p := 3)).mpr
  constructor
  · apply LinearEquiv.ext; intro v; apply Prod.ext
    · rfl
    · have hc : cubic ^ 3 = 1 := by rw [← cubic_order]; exact pow_orderOf_eq_one cubic
      exact LinearEquiv.congr_fun hc v.2
  · intro he
    have he' : cubic = 1 := by
      ext v i
      have hh := congrArg Prod.snd (LinearEquiv.congr_fun he (0, v))
      exact congrFun hh i
    have hb : orderOf (1 : BinaryLinear.GL Vec) = 3 := he' ▸ cubic_order
    simp at hb
private def q : Pair →ₗ[F] F := (LinearMap.proj 0).comp (LinearMap.snd F Vec Vec)
private def trans (w : Vec) : Lin := BinaryLinear.transvection (w, 0) q (by simp [q])
private theorem trans_mem_radical (w : Vec) : trans w ∈ BinaryLinear.radical P := by
  apply BinaryLinear.transvection_mem
  · exact ⟨by simp, rfl⟩
  · intro v hv
    have hv2 : v.2 = 0 := by simpa using hv.2
    simp [q, hv2]
private theorem trans_mem_parabolic (w : Vec) : trans w ∈ BinaryLinear.parabolic P :=
  (BinaryLinear.radical_le_parabolic P) (trans_mem_radical w)
private theorem diagonal_mem_parabolic : diagonal ∈ BinaryLinear.parabolic P := by
  intro v
  simp only [P, Submodule.mem_prod, Submodule.mem_top, Submodule.mem_bot]
  constructor
  · intro hv
    exact ⟨trivial, cubic.map_eq_zero_iff.mp hv.2⟩
  · intro hv
    exact ⟨trivial, by simpa [diagonal] using (cubic.map_eq_zero_iff.mpr hv.2)⟩
private theorem conj_mem_parabolic (w : Vec) :
    trans w * diagonal * (trans w)⁻¹ ∈ BinaryLinear.parabolic P := by
  exact (BinaryLinear.parabolic P).mul_mem
    ((BinaryLinear.parabolic P).mul_mem (trans_mem_parabolic w) diagonal_mem_parabolic)
    ((BinaryLinear.parabolic P).inv_mem (trans_mem_parabolic w))
private theorem trans_fixes_x (w : Vec) {x : Pair} (hx : x.2 = 0) : trans w x = x := by
  obtain ⟨a,b⟩ := x
  simp_all [trans, q, BinaryLinear.transvection]
private theorem diagonal_fixes_x {x : Pair} (hx : x.2 = 0) : diagonal x = x := by
  obtain ⟨a,b⟩ := x
  simp_all [diagonal]
private theorem conj_fixes_x (w : Vec) {x : Pair} (hx : x.2 = 0) :
    (trans w * diagonal * (trans w)⁻¹) x = x := by
  rw [show (trans w)⁻¹ = trans w by rfl]
  simp only [LinearEquiv.mul_apply]
  rw [trans_fixes_x w hx]
  rw [diagonal_fixes_x hx]
  exact trans_fixes_x w hx
private theorem conj_order (w : Vec) : orderOf (trans w * diagonal * (trans w)⁻¹) = 3 := by
  rw [show trans w * diagonal * (trans w)⁻¹ = (MulAut.conj (trans w)) diagonal by rfl,
    (MulAut.conj (trans w)).orderOf_eq, diagonal_order]

private theorem residual_mem_general {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} {g : G} (hg : g ∈ H) (ho : orderOf g = 3) :
    g ∈ Stellmacher.twoResidualAmbient H := by
  rw [twoResidualAmbient_eq_map_pResidual]
  refine ⟨⟨g, hg⟩, ?_, rfl⟩
  change ⟨g, hg⟩ ∈ pResidual 2 H
  apply Subgroup.mem_pResidual_of_orderOf_coprime
  have horder0 : orderOf (⟨g, hg⟩ : H) = orderOf g := by
    symm
    exact Subgroup.orderOf_coe (H := H) (⟨g, hg⟩ : H)
  have horder : orderOf (⟨g, hg⟩ : H) = 3 := horder0.trans ho
  rw [horder]
  decide

abbrev Space4 := BinaryLinear.OuterCyclic.Space 4
private instance finite_space4 : Finite (BinaryLinear.GL Space4) := by
  apply Finite.of_injective (fun g : BinaryLinear.GL Space4 => (g : Space4 → Space4))
    DFunLike.coe_injective

private def planeEquiv : FourParabolicRadical.plane ≃ₗ[ZMod 2] Vec where
  toFun v := v.val.1
  invFun v := ⟨(v, 0), by simp [FourParabolicRadical.plane]⟩
  left_inv v := by
    apply Subtype.ext
    change (v.val.1, 0) = v.val
    exact Prod.ext rfl (show v.val.2 = 0 from v.property).symm
  right_inv v := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private theorem plane_coordinates (W : Submodule (ZMod 2) Space4)
    (hW : Module.finrank (ZMod 2) W = 2) :
    ∃ e : Pair ≃ₗ[ZMod 2] Space4, ∀ v : Pair, e v ∈ W ↔ v.2 = 0 := by
  let f := FourParabolicRadical.spaceEquiv
  let W₀ := FourParabolicRadical.plane.map f.toLinearMap
  have hd : Module.finrank (ZMod 2) W₀ = Module.finrank (ZMod 2) W := by
    rw [f.finrank_map_eq]
    have hp : Module.finrank (ZMod 2) FourParabolicRadical.plane = 2 := by
      rw [planeEquiv.finrank_eq]
      simp [Vec]
    rw [hp, hW]
  obtain ⟨g, hg⟩ := FourParabolicAction.exists_linearEquiv_map_eq W₀ W hd
  refine ⟨f.trans g, ?_⟩
  intro v
  change g (f v) ∈ W ↔ v.2 = 0
  rw [← hg]
  constructor
  · rintro ⟨w, ⟨u, hu, he₁⟩, he₂⟩
    change f u = w at he₁
    change g w = g (f v) at he₂
    have he : u = v := f.injective (he₁.trans (g.injective he₂))
    exact he ▸ hu
  · intro hv
    exact ⟨f v, ⟨v, hv, rfl⟩, rfl⟩

private theorem coord_parabolic
    (W : Submodule (ZMod 2) Space4) (e : Pair ≃ₗ[ZMod 2] Space4)
    (he : ∀ v : Pair, e v ∈ W ↔ v.2 = 0) (a b : BinaryLinear.GL Vec) :
    BinaryLinear.SmallParabolicLevi.linearGroupCongr e (a.prodCongr b) ∈ BinaryLinear.parabolic W := by
  intro x
  obtain ⟨v, rfl⟩ := e.surjective x
  rw [BinaryLinear.SmallParabolicLevi.linearGroupCongr_apply, e.symm_apply_apply, he, he]
  exact b.map_eq_zero_iff

private theorem coord_parabolic_general
    (W : Submodule (ZMod 2) Space4) (e : Pair ≃ₗ[ZMod 2] Space4)
    (he : ∀ v : Pair, e v ∈ W ↔ v.2 = 0) {g : Lin}
    (hg : g ∈ BinaryLinear.parabolic P) :
    BinaryLinear.SmallParabolicLevi.linearGroupCongr e g ∈ BinaryLinear.parabolic W := by
  intro y
  obtain ⟨v, rfl⟩ := e.surjective y
  rw [BinaryLinear.SmallParabolicLevi.linearGroupCongr_apply, e.symm_apply_apply, he]
  have h1 := hg v
  have h2 : v ∈ P ↔ e v ∈ W := by simpa [P] using (he v).symm
  simpa using h1.trans h2

private theorem dual_cubic_fixed {qv : Module.Dual F Vec}
    (h : cubic.symm.dualMap qv = qv) : qv = 0 := by
  apply LinearMap.ext
  intro v
  have hv : v = v 0 • (Pi.single 0 1) + v 1 • (Pi.single 1 1) := by
    ext i
    fin_cases i <;> simp
  rw [hv, map_add, map_smul, map_smul]
  have h0 := LinearMap.congr_fun h (Pi.single 0 1)
  have h1 := LinearMap.congr_fun h (Pi.single 1 1)
  have h0' : qv (Pi.single 1 1) = 0 := by
    have hh : qv ![1,1] = qv (Pi.single 0 1) := by simpa [cubic, LinearEquiv.dualMap_apply] using h0
    have hv0 : (![1,1] : Vec) = Pi.single 0 1 + Pi.single 1 1 := by ext i; fin_cases i <;> simp
    rw [hv0] at hh
    have hh' : qv (Pi.single 0 1) + qv (Pi.single 1 1) = qv (Pi.single 0 1) + 0 := by simpa using hh
    exact add_left_cancel hh'
  have h1' : qv (Pi.single 0 1) = qv (Pi.single 1 1) := by
    have hv1 : (![1,0] : Vec) = Pi.single 0 1 := by ext i; fin_cases i <;> simp
    simpa [cubic, LinearEquiv.dualMap_apply, hv1] using h1
  rw [h0'] at h1'
  simp [h0', h1']

private theorem std_fixed_explicit
    (f : Module.Dual F Pair)
    (hdiag : diagonal.symm.dualMap f = f)
    (htrans : ∀ w : Vec,
      (trans w * diagonal * (trans w)⁻¹).symm.dualMap f = f) : f = 0 := by
  have hg := hdiag
  have he0 := htrans (![1,0] : Vec)
  have he1 := htrans (![0,1] : Vec)
  have hg0 := LinearMap.congr_fun hg (0, (![1,0] : Vec))
  have hg1 := LinearMap.congr_fun hg (0, (![0,1] : Vec))
  simp only [LinearEquiv.dualMap_apply] at hg0 hg1
  have hdiag0 : (diagonal.symm) (0, (![1,0] : Vec)) = (0, (![1,1] : Vec)) := by decide
  have hdiag1 : (diagonal.symm) (0, (![0,1] : Vec)) = (0, (![1,0] : Vec)) := by decide
  rw [hdiag0] at hg0
  rw [hdiag1] at hg1
  have hsum : ((0 : Vec), (![1,1] : Vec)) = ((0 : Vec), (![1,0] : Vec)) + ((0 : Vec), (![0,1] : Vec)) := by
    apply Prod.ext
    · rfl
    · ext i
      fin_cases i <;> decide
  have hg0' := hg0
  change f ((0 : Vec), (![1,1] : Vec)) = f ((0 : Vec), (![1,0] : Vec)) at hg0'
  have hsumf : f ((0 : Vec), (![1,1] : Vec)) =
      f (((0 : Vec), (![1,0] : Vec)) + ((0 : Vec), (![0,1] : Vec))) := by
    exact congrArg (fun z : Vec × Vec => f z) hsum
  rw [hsumf, map_add] at hg0'
  have hb1 : f (0, (![0,1] : Vec)) = 0 := by
    have hh : f (0, (![1,0] : Vec)) + f (0, (![0,1] : Vec)) =
        f (0, (![1,0] : Vec)) + 0 := by simpa using hg0'
    exact add_left_cancel hh
  have hb0 : f (0, (![1,0] : Vec)) = 0 := by
    rw [hb1] at hg1
    exact hg1
  have hn0 : f ((![1,0] : Vec), 0) = 0 := by
    have he := LinearMap.congr_fun (htrans (![1,0] : Vec)) (0, (![0,1] : Vec))
    simp only [LinearEquiv.dualMap_apply] at he
    have hv : ((trans (![1,0]) * diagonal * (trans (![1,0]) : Lin)⁻¹).symm)
        (0, (![0,1] : Vec)) = ((![1,0] : Vec), (![1,0] : Vec)) := by decide
    rw [hv] at he
    have he' : f ((![1,0] : Vec), (![1,0] : Vec)) = 0 := by simpa [hb1] using he
    have hv : ((![1,0] : Vec), (![1,0] : Vec)) = ((![1,0] : Vec), 0) + (0, (![1,0] : Vec)) := by
      ext i <;> fin_cases i <;> decide
    have hh := he'
    rw [hv, map_add, hb0] at hh
    simpa using hh
  have hn1 : f ((![0,1] : Vec), 0) = 0 := by
    have he := LinearMap.congr_fun (htrans (![0,1] : Vec)) (0, (![0,1] : Vec))
    simp only [LinearEquiv.dualMap_apply] at he
    have hv : ((trans (![0,1]) * diagonal * (trans (![0,1]) : Lin)⁻¹).symm)
        (0, (![0,1] : Vec)) = ((![0,1] : Vec), (![1,0] : Vec)) := by decide
    rw [hv] at he
    have he' : f ((![0,1] : Vec), (![1,0] : Vec)) = 0 := by simpa [hb1] using he
    have hv : ((![0,1] : Vec), (![1,0] : Vec)) = ((![0,1] : Vec), 0) + (0, (![1,0] : Vec)) := by
      ext i <;> fin_cases i <;> decide
    have hh := he'
    rw [hv, map_add, hb0] at hh
    simpa using hh
  apply LinearMap.ext
  rintro ⟨u,v⟩
  have hu : u = u 0 • (![1,0] : Vec) + u 1 • (![0,1] : Vec) := by
    ext i; fin_cases i <;> simp
  have hv : v = v 0 • (![1,0] : Vec) + v 1 • (![0,1] : Vec) := by
    ext i; fin_cases i <;> simp
  have hz : (u,v) =
      (u 0) • ((![1,0] : Vec), 0) + (u 1) • ((![0,1] : Vec), 0) +
      (v 0) • (0, (![1,0] : Vec)) + (v 1) • (0, (![0,1] : Vec)) := by
    rw [hu, hv]
    apply Prod.ext
    · ext i
      fin_cases i <;> simp
    · ext i
      fin_cases i <;> simp
  rw [hz]
  rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
  simp [hn0, hn1, hb0, hb1]
private theorem transported_fixed (W : Submodule (ZMod 2) Space4)
    (hW : Module.finrank (ZMod 2) W = 2) (x : Space4) (hxW : x ∈ W)
    (hx0 : x ≠ 0) (f : Module.Dual F Space4)
    (hf : ∀ g ∈ Stellmacher.twoResidualAmbient
      (CFSG.Quasithin.Chapter15.Section03.theta (BinaryLinear.parabolic W) ⊓
        pointStabilizer x), g.symm.dualMap f = f) : f = 0 := by
  obtain ⟨e, he⟩ := plane_coordinates W hW
  let x' : Pair := e.symm x
  have hx' : x'.2 = 0 := by
    exact (he x').mp (by simpa [x'] using hxW)
  have hx'0 : x' ≠ 0 := by
    intro h
    apply hx0
    have hx_eq : e x' = x := by simp [x']
    rw [← hx_eq]
    simpa using congrArg e h
  let phi := BinaryLinear.SmallParabolicLevi.linearGroupCongr e
  let f' : Module.Dual F Pair := e.dualMap f
  have image_point {g : Lin} (hg : g x' = x') : phi g ∈ pointStabilizer x := by
    change phi g x = x
    have hx_eq : x = e x' := by simp [x']
    rw [hx_eq, BinaryLinear.SmallParabolicLevi.linearGroupCongr_apply,
      e.symm_apply_apply, hg]
  have hdiagP : phi diagonal ∈ BinaryNaturalDual.VectorStabilizers.Pure.pointStabilizer x :=
      image_point (diagonal_fixes_x hx')
  have hdiagK : phi diagonal ∈ CFSG.Quasithin.Chapter15.Section03.theta
      (BinaryLinear.parabolic W) := by
    apply Subgroup.subset_closure
    constructor
    · exact coord_parabolic W e he 1 cubic
    · exact (phi.orderOf_eq diagonal).trans diagonal_order
  let H : Subgroup (BinaryLinear.GL Space4) :=
    CFSG.Quasithin.Chapter15.Section03.theta (BinaryLinear.parabolic W) ⊓
      pointStabilizer x
  have hdiagD : phi diagonal ∈ Stellmacher.twoResidualAmbient H :=
    residual_mem_general ⟨hdiagK, hdiagP⟩ ((phi.orderOf_eq diagonal).trans diagonal_order)
  have hdiag : diagonal.symm.dualMap f' = f' := by
    apply LinearMap.ext
    intro z
    have hh := LinearMap.congr_fun (hf (phi diagonal) hdiagD) (e z)
    change f ((phi diagonal).symm (e z)) = f (e z) at hh
    change f (e (diagonal.symm z)) = f (e z)
    have hinv : (phi diagonal).symm (e z) = e (diagonal.symm z) := by
      apply (phi diagonal).injective
      rw [(phi diagonal).apply_symm_apply,
        BinaryLinear.SmallParabolicLevi.linearGroupCongr_apply,
        e.symm_apply_apply, diagonal.apply_symm_apply]
    rw [hinv] at hh
    exact hh
  have htrans : ∀ w : Vec,
      (trans w * diagonal * (trans w)⁻¹).symm.dualMap f' = f' := by
    intro w
    let c : Lin := trans w * diagonal * (trans w)⁻¹
    have hcP : c ∈ BinaryLinear.parabolic P := conj_mem_parabolic w
    have hcW : phi c ∈ BinaryLinear.parabolic W := by
      exact coord_parabolic_general W e he hcP
    have hcK : phi c ∈ CFSG.Quasithin.Chapter15.Section03.theta
        (BinaryLinear.parabolic W) := by
      apply Subgroup.subset_closure
      exact ⟨hcW, (phi.orderOf_eq c).trans (conj_order w)⟩
    have hcPnt : phi c ∈ pointStabilizer x := image_point (conj_fixes_x w hx')
    have hcD : phi c ∈ Stellmacher.twoResidualAmbient H :=
      residual_mem_general ⟨hcK, hcPnt⟩ ((phi.orderOf_eq c).trans (conj_order w))
    apply LinearMap.ext
    intro z
    have hh := LinearMap.congr_fun (hf (phi c) hcD) (e z)
    change f ((phi c).symm (e z)) = f (e z) at hh
    change f (e (c.symm z)) = f (e z)
    have hinv : (phi c).symm (e z) = e (c.symm z) := by
      apply (phi c).injective
      rw [(phi c).apply_symm_apply,
        BinaryLinear.SmallParabolicLevi.linearGroupCongr_apply,
        e.symm_apply_apply, c.apply_symm_apply]
    rw [hinv] at hh
    exact hh
  apply e.dualMap.injective
  simpa [f'] using (std_fixed_explicit f' hdiag htrans)

private def diagonalBoth : Lin := cubic.prodCongr cubic

private theorem diagonalBoth_order : orderOf diagonalBoth = 3 := by
  apply (orderOf_eq_prime_iff (p := 3)).mpr
  constructor
  · apply LinearEquiv.ext
    intro v
    have hc : cubic ^ 3 = 1 := by rw [← cubic_order]; exact pow_orderOf_eq_one cubic
    apply Prod.ext
    · change cubic (cubic (cubic v.1)) = v.1
      exact LinearEquiv.congr_fun hc v.1
    · change cubic (cubic (cubic v.2)) = v.2
      exact LinearEquiv.congr_fun hc v.2
  · intro he
    have he' : cubic = 1 := by
      ext v i
      have hh := congrArg Prod.fst (LinearEquiv.congr_fun he (v, 0))
      exact congrFun hh i
    have hc := cubic_order
    rw [he', orderOf_one] at hc
    omega

private theorem dual_diagonalBoth_fixed {q : Module.Dual F Pair}
    (hq : diagonalBoth.symm.dualMap q = q) : q = 0 := by
  let q₁ : Module.Dual F Vec :=
    { toFun := fun u => q (u, 0)
      map_add' := by intro u v; change q ((u, 0) + (v, 0)) = _; rw [q.map_add]
      map_smul' := by intro a u; change q (a • (u, 0)) = _; rw [q.map_smul]; simp }
  let q₂ : Module.Dual F Vec :=
    { toFun := fun v => q (0, v)
      map_add' := by intro u v; change q ((0, u) + (0, v)) = _; rw [q.map_add]
      map_smul' := by intro a u; change q (a • (0, u)) = _; rw [q.map_smul]; simp }
  have hq₁ : cubic.symm.dualMap q₁ = q₁ := by
    apply LinearMap.ext
    intro u
    have hh := LinearMap.congr_fun hq (u, 0)
    simp only [LinearEquiv.dualMap_apply] at hh ⊢
    simpa [diagonalBoth, q₁] using hh
  have hq₂ : cubic.symm.dualMap q₂ = q₂ := by
    apply LinearMap.ext
    intro v
    have hh := LinearMap.congr_fun hq (0, v)
    simp only [LinearEquiv.dualMap_apply] at hh ⊢
    simpa [diagonalBoth, q₂] using hh
  have hz₁ : ∀ u : Vec, q (u, 0) = 0 := by
    intro u
    have := LinearMap.congr_fun (dual_cubic_fixed hq₁) u
    simpa [q₁] using this
  have hz₂ : ∀ v : Vec, q (0, v) = 0 := by
    intro v
    have := LinearMap.congr_fun (dual_cubic_fixed hq₂) v
    simpa [q₂] using this
  apply LinearMap.ext
  rintro ⟨u, v⟩
  have hp : (u, v) = (u, 0) + (0, v) := by ext <;> simp
  calc
    q (u, v) = q (u, 0) + q (0, v) := by rw [hp, map_add]
    _ = 0 + 0 := by rw [hz₁, hz₂]
    _ = 0 := add_zero _

private theorem theta_dual_fixed_eq_zero (W : Submodule (ZMod 2) Space4)
    (hW : Module.finrank (ZMod 2) W = 2) (f : Module.Dual F Space4)
    (hf : ∀ g ∈ CFSG.Quasithin.Chapter15.Section03.theta
      (BinaryLinear.parabolic W), g.symm.dualMap f = f) : f = 0 := by
  obtain ⟨e, he⟩ := plane_coordinates W hW
  let phi := BinaryLinear.SmallParabolicLevi.linearGroupCongr e
  let f' : Module.Dual F Pair := e.dualMap f
  have hgK : phi diagonalBoth ∈ CFSG.Quasithin.Chapter15.Section03.theta
      (BinaryLinear.parabolic W) := by
    apply Subgroup.subset_closure
    exact ⟨coord_parabolic W e he cubic cubic,
      (phi.orderOf_eq diagonalBoth).trans diagonalBoth_order⟩
  have hq : diagonalBoth.symm.dualMap f' = f' := by
    apply LinearMap.ext
    intro z
    have hh := LinearMap.congr_fun (hf (phi diagonalBoth) hgK) (e z)
    change f ((phi diagonalBoth).symm (e z)) = f (e z) at hh
    change f (e (diagonalBoth.symm z)) = f (e z)
    have hinv : (phi diagonalBoth).symm (e z) = e (diagonalBoth.symm z) := by
      apply (phi diagonalBoth).injective
      rw [(phi diagonalBoth).apply_symm_apply,
        BinaryLinear.SmallParabolicLevi.linearGroupCongr_apply,
        e.symm_apply_apply, diagonalBoth.apply_symm_apply]
    rw [hinv] at hh
    exact hh
  apply e.dualMap.injective
  simpa [f'] using (dual_diagonalBoth_fixed hq)

theorem theta_naturalDual_fixed_eq_zero (W : Submodule (ZMod 2) Space4)
    (hW : Module.finrank (ZMod 2) W = 2) (z : Space4 × Module.Dual (ZMod 2) Space4)
    (hz : ∀ g ∈ CFSG.Quasithin.Chapter15.Section03.theta
      (BinaryLinear.parabolic W), BinaryLinear.NaturalDualFlag.action g z = z) : z = 0 := by
  obtain ⟨v, f⟩ := z
  have hv :=
    CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Repeated.plane_theta_fixed_eq_zero
      W hW v (by
        intro g hg
        simpa only [BinaryLinear.NaturalDualFlag.action_fst] using congrArg Prod.fst (hz g hg))
  have hf : ∀ g ∈ CFSG.Quasithin.Chapter15.Section03.theta
      (BinaryLinear.parabolic W), g.symm.dualMap f = f := by
    intro g hg
    apply LinearMap.ext
    intro y
    have hh := congrArg (fun w => w.2 y) (hz g hg)
    simpa only [BinaryLinear.NaturalDualFlag.action_snd, LinearEquiv.dualMap_apply] using hh
  exact Prod.ext hv (theta_dual_fixed_eq_zero W hW f hf)

theorem theta_point_residual_dual_fixed_eq_zero (W : Submodule (ZMod 2) Space4)
    (hW : Module.finrank (ZMod 2) W = 2) (x : Space4) (hxW : x ∈ W)
    (hx0 : x ≠ 0) (f : Module.Dual F Space4)
    (hf : ∀ g ∈ Stellmacher.twoResidualAmbient
      (CFSG.Quasithin.Chapter15.Section03.theta (BinaryLinear.parabolic W) ⊓
        pointStabilizer x), g.symm.dualMap f = f) : f = 0 :=
  transported_fixed W hW x hxW hx0 f hf


end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ModelGeometry
