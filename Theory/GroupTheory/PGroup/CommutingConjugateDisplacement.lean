module
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.PGroup
public import Theory.GroupTheory.PCoreImage
/-!
# Nontrivial prime-power displacement between commuting conjugates

If a p-element in Y agrees with its conjugate in a subgroup commuting with
Y, its cyclic subgroup is normal in Y. Thus a trivial p-core forces the
p-element to move. Its displacement is again a p-element, since the two
cyclic subgroups commute.

This is the quotient algebra in Aschbacher, *Pushing-up in finite groups*,
Math. Z. 177 (1981), 10.3, p.78, used for Aschbacher--Smith C.2.4.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] {p : ℕ}

theorem p_displacement_of_commuting_conjugate
    (Y : Subgroup G) (s y : G) (hy : y ∈ Y) (hy1 : y ≠ 1)
    (hp : IsPGroup p (zpowers y)) (hcore : Y.pCoreIn p = ⊥)
    (hc : Y ≤ centralizer (Y.map (MulAut.conj s).toMonoidHom : Set G)) :
    IsPGroup p (zpowers (y⁻¹ * (s * y * s⁻¹))) ∧ y⁻¹ * (s * y * s⁻¹) ≠ 1 := by
  let A := zpowers y
  let B := A.map (MulAut.conj s).toMonoidHom
  have hAY : A ≤ Y := zpowers_le.mpr hy
  have hBY : B ≤ Y.map (MulAut.conj s).toMonoidHom := map_mono hAY
  have hAB : A ≤ centralizer (B : Set G) := hAY.trans (hc.trans (centralizer_le hBY))
  have hj : IsPGroup p (A ⊔ B : Subgroup G) := hp.to_sup_of_normal_right' (hp.map _)
    (hAB.trans (Subgroup.centralizer_le_normalizer _))
  have hw : y⁻¹ * (s * y * s⁻¹) ∈ A ⊔ B :=
    mul_mem (mem_sup_left (A.inv_mem (mem_zpowers y)))
      (mem_sup_right (mem_map_of_mem _ (mem_zpowers y)))
  refine ⟨hj.to_le (zpowers_le.mpr hw), ?_⟩
  intro he
  have hye : s * y * s⁻¹ = y := by
    have hh := congrArg (fun z => y * z) he
    simpa only [← mul_assoc,mul_inv_cancel,one_mul,mul_one] using hh
  have hyconj : y ∈ Y.map (MulAut.conj s).toMonoidHom :=
    hye ▸ (mem_map_of_mem (MulAut.conj s).toMonoidHom hy)
  have hYA : Y ≤ centralizer (A : Set G) := by
    change Y ≤ centralizer (zpowers y : Set G)
    rw [zpowers_eq_closure, centralizer_closure]
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hc ha y hyconj).symm
  have hle : A ≤ Y.pCoreIn p := le_pCoreIn_of_normalizes hp hAY
    (hYA.trans (Subgroup.centralizer_le_normalizer _))
  exact hy1 (mem_bot.mp (hcore ▸ hle (mem_zpowers y)))

variable [Finite G] [Fact p.Prime]

/-- The nontrivial displacement lifts through an actual normal p-subgroup. -/
theorem p_displacement_modulo_normal
    (R Y : Subgroup G) [R.Normal] (hpR : IsPGroup p R)
    (hcore : Y.pCoreIn p = R)
    (s y : G) (hy : y ∈ Y) (hyR : y ∉ R)
    (hp : IsPGroup p (zpowers y))
    (hc : ⁅Y,Y.map (MulAut.conj s).toMonoidHom⁆ ≤ R) :
    IsPGroup p (zpowers (y⁻¹ * (s * y * s⁻¹))) ∧ y⁻¹ * (s * y * s⁻¹) ∉ R := by
  let q := QuotientGroup.mk' R
  have hk : IsPGroup p q.ker := by rw [QuotientGroup.ker_mk']; exact hpR
  have hqY : (Y.map q).pCoreIn p = ⊥ := by
    rw [← map_pCoreIn_of_ker_isPGroup q hk, hcore, QuotientGroup.map_mk'_self]
  have he : (Y.map (MulAut.conj s).toMonoidHom).map q =
      (Y.map q).map (MulAut.conj (q s)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
  have hqc : Y.map q ≤ centralizer ((Y.map q).map (MulAut.conj (q s)).toMonoidHom : Set (G ⧸ R)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← he, ← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hc
  have hyp : IsPGroup p (zpowers (q y)) := by
    rw [← MonoidHom.map_zpowers]
    exact hp.map q
  have hyn : q y ≠ 1 := fun hh => hyR ((QuotientGroup.eq_one_iff y).mp hh)
  have hd := p_displacement_of_commuting_conjugate (Y.map q) (q s) (q y)
    (mem_map_of_mem q hy) hyn hyp hqY hqc
  let w := y⁻¹ * (s * y * s⁻¹)
  have hew : q w = (q y)⁻¹ * (q s * q y * (q s)⁻¹) := by simp [w]
  refine ⟨?_,fun hw => hd.2 (hew.symm.trans ((QuotientGroup.eq_one_iff w).mpr hw))⟩
  have hwp : IsPGroup p (zpowers (q w)) := hew ▸ hd.1
  exact (hwp.comap_of_ker_isPGroup q hk).to_le
    (zpowers_le.mpr (show q w ∈ zpowers (q w) from mem_zpowers _))
end Theory.GroupTheory
