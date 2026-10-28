module
public import Theory.GroupTheory.SpecificGroups.QuaternionEightAut
public import Theory.GroupTheory.QuaternionDiagonalMembership
public import Theory.GroupTheory.QuaternionCentralProductCommutator
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.Tactic.Group

/-!
# A cubic-invariant quaternion diagonal moved by a commuting factor swap

Let `B` and `C` be commuting quaternion factors with intersection of order two.
Suppose `g` has cube one, preserves each factor, and acts nontrivially on `B`.
Let `s` be an involution swapping the factors and inverting `g` modulo their
join, while a second swap `t` commutes with `g` modulo the join. There is an
actual diagonal elementary eight normalized by the join, `g`, and `s`, but
not by `t`. The result retains its factor isomorphism for later centralizer
calculations. No involution hypothesis is imposed on `t`.

Identify the second factor with the first by conjugation by `s`. On the first
factor, conjugation by `g` is a nontrivial cubic automorphism, and conjugation
by `s*t` and `t*s` invert it modulo central differences. The shared-factor
commutator calculation translates the two ambient modulo-join relations into
these statements on the actual factor. A kernel-checked quaternion calculation
selects an involution `f` inverting the cubic action whose diagonal is moved by
the second swap. Compose `f` with the factor identification to define the
diagonal. Its exact membership criterion proves normalization by `g` and `s`
and turns the selected noncentral difference into failure of normalization by
`t`. The generic diagonal theorems supply its order and normalization by the
full product.

This is the invariant-eight selection and exceptional-diagonal exclusion in
Stellmacher (9.1), Journal of Algebra 190 (1997), p.48. The source application
supplies `s²=1` from membership in the elementary abelian subgroup `Z_a`; that
hypothesis is essential to the reusable statement.
-/

namespace Subgroup
private theorem exists_inverting_involution_moved_of_equiv
    {G : Type*} [Group G] (model : G ≃* QuaternionGroup 2)
    (a b c : MulAut G) (ha : a^3=1) (hane : a ≠ 1)
    (hb : ∀ x, (b (a x))⁻¹ * a (a (b x)) ∈ Subgroup.center G)
    (hc : ∀ x, (c (a x))⁻¹ * a (a (c x)) ∈ Subgroup.center G) :
    ∃ f : MulAut G, f^2=1 ∧ (∀ x, f (a x) = a (a (f x))) ∧
      ∃ x, (f (c (f x)))⁻¹ * b x ∉ Subgroup.center G := by
  let E := MulAut.congr model
  have hcent (x : G) (hx : x ∈ Subgroup.center G) :
      model x ∈ Subgroup.center (QuaternionGroup 2) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := model.surjective y
    simpa using congrArg model (Subgroup.mem_center_iff.mp hx z)
  have ha' : (E a)^3=1 := by rw [← map_pow, ha, map_one]
  have hane' : E a ≠ 1 := by
    intro h; apply hane; apply E.injective
    simpa only [map_one] using h
  have hb' : ∀ x, (E b (E a x))⁻¹ * E a (E a (E b x)) ∈
      Subgroup.center (QuaternionGroup 2) := by
    intro x
    obtain ⟨y, rfl⟩ := model.surjective x
    simpa [E, MulAut.congr_apply] using hcent _ (hb y)
  have hc' : ∀ x, (E c (E a x))⁻¹ * E a (E a (E c x)) ∈
      Subgroup.center (QuaternionGroup 2) := by
    intro x
    obtain ⟨y, rfl⟩ := model.surjective x
    simpa [E, MulAut.congr_apply] using hcent _ (hc y)
  obtain ⟨f', hf'2, hfa, x', hfx⟩ :=
    QuaternionGroup.exists_inverting_involution_moved (E a) (E b) (E c) ha' hane' hb' hc'
  let f := E.symm f'
  have hEf : E f = f' := E.apply_symm_apply f'
  refine ⟨f, ?_, ?_, model.symm x', ?_⟩
  · apply E.injective
    rw [map_pow, hEf, hf'2, map_one]
  · intro x
    apply model.injective
    have hh := hfa (model x)
    rw [← hEf] at hh
    simpa [E, MulAut.congr_apply] using hh
  · intro hx
    apply hfx
    have hh := hcent _ hx
    rw [← hEf]
    simpa [E, MulAut.congr_apply] using hh
private def factorAction {G : Type*} [Group G] (B : Subgroup G)
    (u : G) (hu : u ∈ normalizer (B : Set G)) : MulAut B :=
  B.normalizerMonoidHom ⟨u, hu⟩

private theorem anti_action_of_modulo
    {G : Type*} [Group G] (B C : Subgroup G) (model : B ≃* QuaternionGroup 2)
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (g u : G) (hg : g ∈ normalizer (B : Set G))
    (hu : u ∈ normalizer (B : Set G))
    (hmod : u*g*u⁻¹*g ∈ B⊔C) :
    ∀ x : B, ((factorAction B u hu) ((factorAction B g hg) x))⁻¹ *
      (factorAction B g hg)⁻¹ ((factorAction B u hu) x) ∈ center B := by
  intro x
  let a := factorAction B g hg
  let b := factorAction B u hu
  let y : B := a⁻¹ (b x)
  have hy : (y : G) = g⁻¹ * (u * (x : G) * u⁻¹) * g := by
    change ((B.normalizerMonoidHom ⟨g, hg⟩)⁻¹ (b x) : G) = _
    rw [← map_inv]
    change g⁻¹ * (u * (x : G) * u⁻¹) * (g⁻¹)⁻¹ = _
    rw [inv_inv]
  have hd := factor_central_difference_of_mem_sup B C model hinter hcomm
    (u*g*u⁻¹*g) hmod y y.property
  have hdeq : (y : G)⁻¹ * ((u*g*u⁻¹*g) * (y : G) * (u*g*u⁻¹*g)⁻¹) =
      (y : G)⁻¹ * (b (a x) : G) := by
    rw [hy]
    change _ = _ * (u * (g * (x : G) * g⁻¹) * u⁻¹)
    group
  rw [hdeq] at hd
  have hd' := (B ⊓ C).inv_mem hd
  have hd'' : (b (a x) : G)⁻¹ * y ∈ B ⊓ C := by simpa only [mul_inv_rev, inv_inv] using hd'
  rw [mem_center_iff]
  intro z
  apply Subtype.ext
  exact hcomm z z.property _ hd''.2
private theorem normalizes_diagonal_of_generators
    {G : Type*} [Group G] [Finite G] (B C : Subgroup G) (θ : B ≃* C)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b) (u : G)
    (hI : ∀ z ∈ B⊓C, u*z*u⁻¹ ∈ B⊓C)
    (hD : ∀ z : B, u*((z:G)*(θ z:G))*u⁻¹ ∈ quaternionDiagonal B C θ hcomm) :
    u ∈ normalizer (quaternionDiagonal B C θ hcomm : Set G) := by
  have hmap : (quaternionDiagonal B C θ hcomm).map (MulAut.conj u).toMonoidHom ≤
      quaternionDiagonal B C θ hcomm := by
    change ((quaternionDiagonalHom B C θ hcomm).range ⊔ (B⊓C)).map _ ≤ _
    rw [map_sup]
    apply sup_le
    · intro x hx
      obtain ⟨y,hy,rfl⟩ := hx
      obtain ⟨z,rfl⟩ := hy
      exact hD z
    · intro x hx
      obtain ⟨z,hz,rfl⟩ := hx
      exact (show B⊓C ≤ quaternionDiagonal B C θ hcomm from le_sup_right) (hI z hz)
  apply mem_normalizer_fintype
  intro x hx
  exact hmap ⟨x,hx,rfl⟩

/-- Select an actual elementary-eight diagonal invariant under the cubic actor
and the inverting involutory swap, but moved by the commuting swap. -/
public theorem exists_quaternion_diagonal_of_swapped_cubic_actions
    {G : Type*} [Group G] [Finite G]
    (B C : Subgroup G) (model : B ≃* QuaternionGroup 2)
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (g s t : G) (hg3 : g^3=1) (hs2 : s^2=1)
    (hgB : g ∈ normalizer (B : Set G)) (hgC : g ∈ normalizer (C : Set G))
    (hgne : ∃ b : B, g*(b:G)*g⁻¹ ≠ b)
    (hsB : B.conjBy s = C) (htB : B.conjBy t = C) (htC : C.conjBy t = B)
    (hsg : s*g*s⁻¹*g ∈ B⊔C) (htg : t*g*t⁻¹*g⁻¹ ∈ B⊔C) :
    ∃ θ : B ≃* C, ∃ U : Subgroup G,
      U = quaternionDiagonal B C θ hcomm ∧ IsElementaryAbelian 2 U ∧ Nat.card U=8 ∧
      B⊓C ≤ U ∧ U ≤ B⊔C ∧ B⊔C ≤ normalizer (U : Set G) ∧
      g ∈ normalizer (U : Set G) ∧ s ∈ normalizer (U : Set G) ∧
      t ∉ normalizer (U : Set G) := by
  let V := B⊔C
  have hsC : C.conjBy s = B := by
    rw [← hsB, conjBy_conjBy, ← pow_two, hs2, conjBy_one]
  have hgV : g ∈ normalizer (V : Set G) :=
    normalizer_inf_normalizer_le_normalizer_sup B C ⟨hgB,hgC⟩
  have hsV : s ∈ normalizer (V : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change (B⊔C).map (MulAut.conj s).toMonoidHom = B⊔C
    rw [map_sup, show B.map (MulAut.conj s).toMonoidHom = C from hsB,
      show C.map (MulAut.conj s).toMonoidHom = B from hsC, sup_comm]
  have htV : t ∈ normalizer (V : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change (B⊔C).map (MulAut.conj t).toMonoidHom = B⊔C
    rw [map_sup, show B.map (MulAut.conj t).toMonoidHom = C from htB,
      show C.map (MulAut.conj t).toMonoidHom = B from htC, sup_comm]
  have hstB : s*t ∈ normalizer (B : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change B.conjBy (s*t) = B
    rw [conjBy_mul, htB, hsC]
  have htsB : t*s ∈ normalizer (B : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change B.conjBy (t*s) = B
    rw [conjBy_mul, hsB, htC]
  have hstg : (s*t)*g*(s*t)⁻¹*g ∈ V := by
    have hh := V.mul_mem ((mem_normalizer_iff.mp hsV _).mp htg) hsg
    convert hh using 1; group
  have htgInv : t*g⁻¹*t⁻¹*g ∈ V := by
    have hh := (mem_normalizer_iff.mp ((normalizer (V : Set G)).inv_mem hgV) _).mp
      (V.inv_mem htg)
    convert hh using 1; group
  have htsg : (t*s)*g*(t*s)⁻¹*g ∈ V := by
    have hh := V.mul_mem ((mem_normalizer_iff.mp htV _).mp hsg) htgInv
    convert hh using 1; group
  let a := factorAction B g hgB
  let b := factorAction B (s*t) hstB
  let c := factorAction B (t*s) htsB
  have ha : a^3=1 := by
    change (B.normalizerMonoidHom ⟨g,hgB⟩)^3=1
    rw [← map_pow]
    have hh : (⟨g,hgB⟩ : normalizer (B : Set G))^3=1 := Subtype.ext hg3
    rw [hh, map_one]
  have hane : a ≠ 1 := by
    intro hh
    obtain ⟨x,hx⟩ := hgne
    have hval := congrArg Subtype.val (DFunLike.congr_fun hh x)
    exact hx hval
  have ha2 : a^2=a⁻¹ := eq_inv_of_mul_eq_one_left (by simpa [pow_succ] using ha)
  have hb : ∀ x, (b (a x))⁻¹ * a (a (b x)) ∈ center B := by
    intro x
    have hh := anti_action_of_modulo B C model hinter hcomm g (s*t) hgB hstB hstg x
    change (b (a x))⁻¹ * a⁻¹ (b x) ∈ center B at hh
    simpa only [← ha2, pow_two, MulAut.mul_apply] using hh
  have hc : ∀ x, (c (a x))⁻¹ * a (a (c x)) ∈ center B := by
    intro x
    have hh := anti_action_of_modulo B C model hinter hcomm g (t*s) hgB htsB htsg x
    change (c (a x))⁻¹ * a⁻¹ (c x) ∈ center B at hh
    simpa only [← ha2, pow_two, MulAut.mul_apply] using hh
  obtain ⟨f,hf2,hfa,x,hfx⟩ := exists_inverting_involution_moved_of_equiv model a b c ha hane hb hc
  let φ : B ≃* C := (B.equivMapOfInjective (MulAut.conj s).toMonoidHom
    (MulAut.conj s).injective).trans (MulEquiv.subgroupCongr hsB)
  have hφ (z : B) : (φ z : G) = s*(z:G)*s⁻¹ := rfl
  let θ : B ≃* C := f.trans φ
  let U := quaternionDiagonal B C θ hcomm
  obtain ⟨hUelem,hUcard,hIU,hUV⟩ := quaternion_diagonal_elementary_eight B C model θ hinter hcomm
  have hsI (z : G) (hz : z ∈ B⊓C) : s*z*s⁻¹ ∈ B⊓C := by
    constructor
    · rw [← hsC]
      exact ⟨z,hz.2,rfl⟩
    · rw [← hsB]
      exact ⟨z,hz.1,rfl⟩
  have hgI (z : G) (hz : z ∈ B⊓C) : g*z*g⁻¹ ∈ B⊓C :=
    ⟨(mem_normalizer_iff.mp hgB z).mp hz.1, (mem_normalizer_iff.mp hgC z).mp hz.2⟩
  have hainv (z : B) : (a⁻¹ z : G) = g⁻¹*(z:G)*g := by
    change ((B.normalizerMonoidHom ⟨g,hgB⟩)⁻¹ z : G) = _
    rw [← map_inv]
    change g⁻¹*(z:G)*(g⁻¹)⁻¹ = _
    rw [inv_inv]
  have hsinv : s⁻¹=s := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hs2)
  have hsfφ (z : B) : s*(φ z:G)*s⁻¹=(z:G) := by
    rw [hφ]
    calc
      s*(s*(z:G)*s⁻¹)*s⁻¹ = (s*s)*(z:G)*(s*s)⁻¹ := by group
      _ = (z:G) := by rw [← pow_two, hs2]; simp
  have hCg (z : B) : (φ (a⁻¹ z):G)⁻¹ * (g*(φ z:G)*g⁻¹) ∈ B⊓C := by
    have hh := factor_central_difference_of_mem_sup B C model hinter hcomm
      (s*g*s⁻¹*g) hsg (a⁻¹ z) (a⁻¹ z).property
    have hhS := hsI _ hh
    convert hhS using 1
    rw [hφ, hφ, hainv]
    group
    simp only [zpow_neg_one, hsinv,
      show s ^ (-2 : ℤ) = 1 by simp [zpow_neg, hs2], mul_one]
  refine ⟨θ,U,rfl,hUelem,hUcard,hIU,hUV,?_,?_,?_,?_⟩
  · exact sup_le_normalizer_quaternionDiagonal B C model θ hinter hcomm
  · apply normalizes_diagonal_of_generators B C θ hcomm g hgI
    intro z
    let az : B := a z
    let gz : C := C.normalizerMonoidHom ⟨g,hgC⟩ (θ z)
    have hprod : g*((z:G)*(θ z:G))*g⁻¹ = (az:G)*(gz:G) := by
      change _ = (g*(z:G)*g⁻¹)*(g*(θ z:G)*g⁻¹)
      group
    rw [hprod]
    apply (mem_quaternionDiagonal_mul_iff B C model θ hinter hcomm az gz).mpr
    change (φ (f (a z)):G)⁻¹ * (g*(φ (f z):G)*g⁻¹) ∈ B⊓C
    have hfa' : f (a z) = a⁻¹ (f z) := by
      simpa only [← ha2, pow_two, MulAut.mul_apply] using hfa z
    rw [hfa']
    exact hCg (f z)
  · apply normalizes_diagonal_of_generators B C θ hcomm s hsI
    intro z
    have hfpoint : f (f z)=z := by simpa [pow_two] using DFunLike.congr_fun hf2 z
    have hprod : s*((z:G)*(θ z:G))*s⁻¹ = (f z:G)*(θ (f z):G) := by
      change s*((z:G)*(φ (f z):G))*s⁻¹ = (f z:G)*(φ (f (f z)):G)
      rw [hfpoint]
      calc
        s*((z:G)*(φ (f z):G))*s⁻¹ = (s*(z:G)*s⁻¹)*(s*(φ (f z):G)*s⁻¹) := by group
        _ = (φ z:G)*(f z:G) := by rw [← hφ, hsfφ]
        _ = (f z:G)*(φ z:G) := (hcomm (f z) (f z).property (φ z) (φ z).property).symm
    rw [hprod]
    exact (show (quaternionDiagonalHom B C θ hcomm).range ≤ U from le_sup_left) ⟨f z,rfl⟩
  · intro htU
    have htbφ (z : B) : t*(z:G)*t⁻¹=(φ (b z):G) := by
      rw [hφ]
      change t*(z:G)*t⁻¹ = s*((s*t)*(z:G)*(s*t)⁻¹)*s⁻¹
      group
      simp only [show s ^ (-2 : ℤ)=1 by simp [zpow_neg,hs2], mul_one]
      rw [← pow_two, hs2, one_mul]
    have htc (z : B) : t*(φ z:G)*t⁻¹=(c z:G) := by
      rw [hφ]
      change t*(s*(z:G)*s⁻¹)*t⁻¹=(t*s)*(z:G)*(t*s)⁻¹
      group
    have hxU : (x:G)*(θ x:G) ∈ U :=
      (show (quaternionDiagonalHom B C θ hcomm).range ≤ U from le_sup_left) ⟨x,rfl⟩
    have hxT := (mem_normalizer_iff.mp htU _).mp hxU
    have hprod : t*((x:G)*(θ x:G))*t⁻¹=(c (f x):G)*(φ (b x):G) := by
      change t*((x:G)*(φ (f x):G))*t⁻¹ = _
      calc
        t*((x:G)*(φ (f x):G))*t⁻¹ = (t*(x:G)*t⁻¹)*(t*(φ (f x):G)*t⁻¹) := by group
        _ = (φ (b x):G)*(c (f x):G) := by rw [htbφ,htc]
        _ = (c (f x):G)*(φ (b x):G) :=
          (hcomm (c (f x)) (c (f x)).property (φ (b x)) (φ (b x)).property).symm
    rw [hprod] at hxT
    have hI := (mem_quaternionDiagonal_mul_iff B C model θ hinter hcomm
      (c (f x)) (φ (b x))).mp hxT
    let δ : B := (f (c (f x)))⁻¹*b x
    have hφδ : (φ δ:G) ∈ B⊓C := by
      change (φ (f (c (f x))):G)⁻¹*(φ (b x):G) ∈ B⊓C at hI
      simpa only [δ, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using hI
    have hδ : (δ:G) ∈ B⊓C := by
      have hh := hsI _ hφδ
      rwa [hsfφ] at hh
    apply hfx
    rw [mem_center_iff]
    intro z
    apply Subtype.ext
    exact hcomm z z.property δ hδ.2
end Subgroup
