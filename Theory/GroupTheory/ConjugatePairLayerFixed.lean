module

public import Theory.GroupTheory.ConjugatePairQuotientLayer
import Mathlib.Tactic.Group

/-!
# Common fixed factors in the literal conjugate-pair layer

Disjoint conjugate factors have no globally central elements. If the first
factor centralizes one generator and the second centralizes its conjugate,
then their product's fixed group is precisely the corresponding factor.
The same holds for a single element of the opposite generator whenever that
element generates the whole group with the first generator.

Applied to [Q,G] modulo (U∩Uᵍ)V, this gives the common fixed spaces used
after Aschbacher--Smith (12.7.18), printed pp.845--846. The original quotient
map and conjugator are retained; no vanishing fixed-space premise is supplied.
-/

public section
open scoped Pointwise
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

private theorem center_of_pair_fixed (U W : Subgroup G) (hgen : U ⊔ W = ⊤)
    {z : G} (hU : z ∈ centralizer (U : Set G)) (hW : z ∈ centralizer (W : Set G)) :
    z ∈ center G := by
  have h : U ⊔ W ≤ centralizer ({z} : Set G) := by
    apply sup_le
    · intro u hu
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hU u hu)
    · intro w hw
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hW w hw)
  rw [hgen] at h
  apply mem_center_iff.mpr
  intro x
  exact mem_centralizer_singleton_iff.mp (h (mem_top x))

/-- Conjugate disjoint factors have no nonidentity central elements. -/
theorem disjoint_conjugate_factors_inf_center (A B : Subgroup G) (g : G)
    (hdis : Disjoint A B) (hconj : A.map (MulAut.conj g).toMonoidHom = B) :
    A ⊓ center G = ⊥ ∧ B ⊓ center G = ⊥ := by
  have hA : A ⊓ center G = ⊥ := by
    apply bot_unique
    intro a ha
    have hc : g * a * g⁻¹ = a := by
      rw [(mem_center_iff.mp ha.2) g, mul_inv_cancel_right]
    have hb : a ∈ B := by
      rw [← hconj]
      exact ⟨a, ha.1, hc⟩
    exact disjoint_iff_inf_le.mp hdis ⟨ha.1, hb⟩
  refine ⟨hA, ?_⟩
  apply bot_unique
  intro b hb
  obtain ⟨a, ha, he⟩ := hconj.symm ▸ hb.1
  have hba : b = a := by
    have hc : g⁻¹ * b * g = b := by
      rw [(mem_center_iff.mp hb.2) g⁻¹, inv_mul_cancel_right]
    have hi := congrArg (fun z : G => g⁻¹ * z * g) he
    change g⁻¹ * (g * a * g⁻¹) * g = g⁻¹ * b * g at hi
    have ha' : a = b := by simpa only [mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one, hc] using hi
    exact ha'.symm
  exact disjoint_iff_inf_le.mp hdis ⟨hba.symm ▸ ha, hb.1⟩

/-- Common fixed spaces from actual conjugate factors and actual generation. -/
theorem conjugate_factors_fixed_groups (A B U W : Subgroup G) (g : G)
    (hgen : U ⊔ W = ⊤) (hdis : Disjoint A B)
    (hAB : B ≤ centralizer (A : Set G))
    (hAU : A ≤ centralizer (U : Set G)) (hBW : B ≤ centralizer (W : Set G))
    (hconj : A.map (MulAut.conj g).toMonoidHom = B) :
    (A ⊔ B) ⊓ centralizer (U : Set G) = A ∧
      ∀ x ∈ W, U ⊔ zpowers x = ⊤ →
        (A ⊔ B) ⊓ centralizer ({x} : Set G) = B := by
  have hc := disjoint_conjugate_factors_inf_center A B g hdis hconj
  have hprod : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
    coe_mul_of_right_le_normalizer_left A B (hAB.trans (centralizer_le_normalizer _))
  constructor
  · apply le_antisymm ?_ (le_inf le_sup_left hAU)
    rintro p ⟨hp, hpf⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod ▸ hp
    have hbU : b ∈ centralizer (U : Set G) := by
      have hh := (centralizer (U : Set G)).mul_mem
        ((centralizer (U : Set G)).inv_mem (hAU ha)) hpf
      simpa only [inv_mul_cancel_left] using hh
    have hb1 : b = 1 := by
      have hm : b ∈ B ⊓ center G := ⟨hb, center_of_pair_fixed U W hgen hbU (hBW hb)⟩
      rwa [hc.2] at hm
    change a * b ∈ A
    rw [hb1, mul_one]
    exact ha
  · intro x hx hUx
    have hBx : B ≤ centralizer ({x} : Set G) :=
      hBW.trans (centralizer_le (Set.singleton_subset_iff.mpr hx))
    apply le_antisymm ?_ (le_inf le_sup_right hBx)
    rintro p ⟨hp, hpf⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod ▸ hp
    have haX : a ∈ centralizer ({x} : Set G) := by
      have hh := (centralizer ({x} : Set G)).mul_mem hpf
        ((centralizer ({x} : Set G)).inv_mem (hBx hb))
      simpa only [mul_inv_cancel_right] using hh
    have haX' : a ∈ centralizer (zpowers x : Set G) := by
      have hxC : x ∈ centralizer ({a} : Set G) :=
        mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp haX).symm
      have hxp : zpowers x ≤ centralizer ({a} : Set G) := zpowers_le.mpr hxC
      exact mem_centralizer_iff.mpr fun y hy => mem_centralizer_singleton_iff.mp (hxp hy)
    have ha1 : a = 1 := by
      have hm : a ∈ A ⊓ center G :=
        ⟨ha, center_of_pair_fixed U (zpowers x) hUx (hAU ha) haX'⟩
      rwa [hc.1] at hm
    change a * b ∈ B
    rw [ha1, one_mul]
    exact hb

/-- The common fixed groups on the exact quotient of the original commutator
layer, with its original conjugator and its element-generation condition. -/
theorem conjugate_pair_commutator_quotient_fixed (q : G →* H)
    (hq : Function.Surjective q) (U Q V : Subgroup G) (g : G)
    [Q.Normal] [V.Normal]
    (hgen : U ⊔ U.map (MulAut.conj g).toMonoidHom = ⊤)
    (hQU : Q ≤ normalizer (U : Set G)) (hVQ : V ≤ Q)
    (hV : ⁅V, (⊤ : Subgroup G)⁆ = V)
    (hker : q.ker = (U ⊓ U.map (MulAut.conj g).toMonoidHom) ⊔ V)
    (hUU : ⁅U,U⁆ ≤ V) (hsq : ∀ u ∈ U, u ^ 2 ∈ V) :
    let P := ⁅Q, (⊤ : Subgroup G)⁆
    let A := (P ⊓ U).map q
    let B := (P ⊓ U.map (MulAut.conj g).toMonoidHom).map q
    A ⊔ B = P.map q ∧ Disjoint A B ∧ IsElementaryAbelian 2 (P.map q) ∧
      P.map q ⊓ centralizer (U.map q : Set H) = A ∧
      ∀ x ∈ U.map (MulAut.conj g).toMonoidHom,
        U.map q ⊔ zpowers (q x) = ⊤ →
        P.map q ⊓ centralizer ({q x} : Set H) = B := by
  dsimp only
  let c := (MulAut.conj g).toMonoidHom
  let W := U.map c
  let P := ⁅Q, (⊤ : Subgroup G)⁆
  let A := (P ⊓ U).map q
  let B := (P ⊓ W).map q
  have hQg : Q.map c = Q := Normal.map_conj_eq Q g
  have hVg : V.map c = V := Normal.map_conj_eq V g
  have hPg : P.map c = P := Normal.map_conj_eq P g
  have hQW : Q ≤ normalizer (W : Set G) := by
    have hh := (map_mono (f := c) hQU).trans (U.le_normalizer_map c)
    rwa [hQg] at hh
  have hWW : ⁅W,W⁆ ≤ V := by
    have hh := map_mono (f := c) hUU
    rwa [map_commutator, hVg] at hh
  have hsqW : ∀ w ∈ W, w ^ 2 ∈ V := by
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_pow]
    exact hVg ▸ mem_map_of_mem c (hsq u hu)
  obtain ⟨hsplit, hdis, helem, hAU, hBW⟩ :=
    normalized_pair_commutator_quotient q U W Q V hgen hQU hQW hVQ hV hker
      hUU hWW hsq hsqW
  have hAB : B ≤ centralizer (A : Set H) := by
    let : IsElementaryAbelian 2 (P.map q) := helem
    exact (map_mono inf_le_left).trans
      ((P.map q).le_centralizer.trans (centralizer_le (map_mono inf_le_left)))
  have hgen' : U.map q ⊔ W.map q = ⊤ := by
    rw [← map_sup, hgen, map_top_of_surjective q hq]
  have hconj : A.map (MulAut.conj (q g)).toMonoidHom = B := by
    rw [map_map, show (MulAut.conj (q g)).toMonoidHom.comp q = q.comp c from by
      ext y; change q g * q y * (q g)⁻¹ = q (g * y * g⁻¹)
      simp only [map_mul, map_inv], ← map_map,
      map_inf _ _ c (MulAut.conj g).injective, hPg]
  have hfixed := conjugate_factors_fixed_groups A B (U.map q) (W.map q)
    (q g) hgen' hdis hAB hAU hBW hconj
  refine ⟨hsplit, hdis, helem, ?_, ?_⟩
  · rw [← hsplit]
    exact hfixed.1
  · intro x hx hgx
    rw [← hsplit]
    exact hfixed.2 (q x) (mem_map_of_mem q hx) hgx

end Subgroup
