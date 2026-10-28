module
public import Theory.GroupTheory.InvolutionAbelianSpan
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow centralizers from a weakly closed abelian subgroup

A Sylow conjugation of an overgroup of C_T(w) carries the weakly closed
subgroup X into T, hence normalizes X. If its orbit of w is already a
T-orbit, a correction in T makes the conjugator centralize w. Comparing
orders then proves that the literal C_T(w) is Sylow in C_G(w).
An invariant codimension-one subgroup of Ω₁(X) supplies this orbit condition.

Source application: Aschbacher--Smith 14.3.22, printed p.999. This avoids
rechoosing the original T and preserves its parabolic-core marking.
-/

public section
open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A weakly closed subgroup and a single normalizer orbit in T promote the
literal centralizer in T to a Sylow subgroup of the full centralizer. -/
theorem centralizer_sylow_of_weakly_closed_orbit
    (T : Sylow p G) (X : Subgroup G) (w : G)
    (hXT : X ≤ (T : Subgroup G)) (hXw : X ≤ centralizer ({w} : Set G))
    (hweak : ∀ g : G, X.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      g ∈ normalizer (X : Set G))
    (horbit : ∀ g ∈ normalizer (X : Set G), ∃ r ∈ (T : Subgroup G),
      g*w*g⁻¹ = r*w*r⁻¹) :
    ∃ S : Sylow p (centralizer ({w} : Set G)),
      (S : Subgroup _).map (centralizer ({w} : Set G)).subtype =
        (T : Subgroup G) ⊓ centralizer ({w} : Set G) := by
  let C := centralizer ({w} : Set G)
  let P := (T : Subgroup G) ⊓ C
  have hPC : P ≤ C := inf_le_right
  have hP : IsPGroup p (P.subgroupOf C) := T.isPGroup'.to_inf_left.comap_subtype
  obtain ⟨S,hPS⟩ := hP.exists_le_sylow
  let Y := (S : Subgroup C).map C.subtype
  have hPY : P ≤ Y := by
    rw [← map_subgroupOf_eq_of_le hPC]
    exact map_mono hPS
  obtain ⟨A,hA⟩ := (S.isPGroup'.map C.subtype).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G A T
  have hYT : Y.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) := by
    rw [←hg]
    exact map_mono hA
  have hgN : g ∈ normalizer (X : Set G) :=
    hweak g ((map_mono ((le_inf hXT hXw).trans hPY)).trans hYT)
  obtain ⟨r,hr,hgr⟩ := horbit g hgN
  let c := r⁻¹*g
  have hc : c ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      c*w*c⁻¹ = r⁻¹*(g*w*g⁻¹)*r := by dsimp [c]; group
      _ = r⁻¹*(r*w*r⁻¹)*r := by rw [hgr]
      _ = w := by group
  have hcY : Y.map (MulAut.conj c).toMonoidHom ≤ P := by
    rintro _ ⟨y,hy,rfl⟩
    have hyC : y ∈ C := map_subtype_le _ hy
    have hgY := hYT (mem_map_of_mem (MulAut.conj g).toMonoidHom hy)
    have hrY := (T : Subgroup G).mul_mem
      ((T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem hr) hgY) hr
    constructor
    · change c*y*c⁻¹ ∈ (T : Subgroup G)
      convert hrY using 1
      dsimp [c]
      group
    · exact C.mul_mem (C.mul_mem hc hyC) (C.inv_mem hc)
  have hcard : Nat.card S ≤ Nat.card (P.subgroupOf C) := by
    have hh := card_le_of_le hcY
    rw [card_map_of_injective (MulAut.conj c).injective,
      card_map_of_injective C.subtype_injective] at hh
    rwa [Nat.card_congr (subgroupOfEquivOfLe hPC).toEquiv]
  have heq : P.subgroupOf C = (S : Subgroup C) := eq_of_le_of_card_ge hPS hcard
  exact ⟨S, heq ▸ map_subgroupOf_eq_of_le hPC⟩

end Sylow

namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
open scoped IsMulCommutative
/-- An invariant codimension-one omega subgroup and its full coset orbit
supply the normalizer-orbit premise of Sylow promotion. -/
theorem normalizer_orbit_of_omega_coset
    (T : Subgroup G) (X V : Subgroup G) [IsMulCommutative X] (w : G)
    (hVX : V ≤ X) (hwX : w ∈ X) (hw : orderOf w = 2) (hwV : w ∉ V)
    (hNV : normalizer (X : Set G) ≤ normalizer (V : Set G))
    (homega : omegaOneAmbient X = V ⊔ zpowers w)
    (horbit : ∀ v ∈ V, ∃ r ∈ T, r*w*r⁻¹=v*w) :
    ∀ g ∈ normalizer (X : Set G), ∃ r ∈ T, g*w*g⁻¹=r*w*r⁻¹ := by
  classical
  intro g hg
  have htX : g*w*g⁻¹ ∈ X := (mem_normalizer_iff.mp hg w).mp hwX
  have ht2 : (g*w*g⁻¹)^2=1 := by
    rw [← MulAut.conj_apply g w, ← map_pow,
      show w^2=1 from hw ▸ pow_orderOf_eq_one w, map_one]
  have ht : g*w*g⁻¹ ∈ V ⊔ zpowers w := homega ▸
    (omegaOneAmbient_le_iff X (omegaOneAmbient X)).mp le_rfl _ htX ht2
  have hWV : zpowers w ≤ normalizer (V : Set G) := by
    apply zpowers_le.mpr
    apply centralizer_le_normalizer
    intro v hv
    exact congrArg Subtype.val (mul_comm' (⟨v,hVX hv⟩ : X) ⟨w,hwX⟩)
  change g*w*g⁻¹ ∈ (↑(V ⊔ zpowers w) : Set G) at ht
  rw [coe_mul_of_right_le_normalizer_left _ _ hWV] at ht
  obtain ⟨v,hv,y,hy,he⟩ := ht
  have hy' : y=w ∨ y=1 := by
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hy)
    rw [Finset.mem_range,hw] at hn
    interval_cases n <;> simp_all
  have hgv : g*w*g⁻¹=v*w := by
    rcases hy' with rfl | rfl
    · exact he.symm
    · exfalso
      apply hwV
      apply (mem_normalizer_iff.mp (hNV hg) w).mpr
      have hvt : v = g*w*g⁻¹ := by simpa only [mul_one] using he
      exact hvt ▸ hv
  obtain ⟨r,hr,hrw⟩ := horbit v hv
  exact ⟨r,hr,hgv.trans hrw.symm⟩
end Theory.GroupTheory
