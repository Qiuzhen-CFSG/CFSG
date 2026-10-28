module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Residual

/-!
# The 11.0.4 residual step for the Hall actor in 11.4.2

For an odd subgroup of N_G(L) whose prime support divides q−1, the proved
prime-residual equalities place O³(Y) in L. The Sp₄ and G₂ cubic residuals
also place Ω₁(O₃(Y)) there. Only the earlier SL₃ cubic-containment clause
remains explicit, restricted to the actual actor Y. This includes all
three original natural markings and assumes no Hall or diagonal marking.

The terminal chosen-flag application uses this containment. The earlier
SL₃ clause retains its source producer qt-d-1222-natural-local-geometry
and final discharge by qt-d-1222-shadow-components. Construction and
placement of Y remain with this comparison owner.
Source: Aschbacher--Smith, 11.0.4 and 11.4.2, printed pp.760,777.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
open LocalGeometry CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- The genuine prime-residual clauses of 11.0.4 place the extracted Hall
actor in L. Only the remaining SL3 cubic clause is explicit; the Sp4 and G2
cubic clauses and every larger prime are discharged here. -/
theorem oddCartanPart_le_of_source
    (S : D.NonbinaryNaturalInput) (c : Coordinates D S.field)
    (Y : Subgroup G) (hYM : Y ≤ normalizer (L : Set G))
    (ho : Odd (Nat.card Y))
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y → p ∣ 2 ^ S.field.degree - 1)
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      ∀ y ∈ Y, orderOf y = 3 → y ∈ L) : oddCartanPart Y ≤ L := by
  let M := normalizer (L : Set G)
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hdiv (p : ℕ) (hd : p ∣ Nat.card Y) (hp : p.Prime) :
      p ∣ (2 ^ S.field.degree) ^ 2 - 1 :=
    (hsupport p hp hd).trans (Nat.sub_dvd_pow_sub_pow (2 ^ S.field.degree) 1 2)
  have hres (p : ℕ) (hp : p.Prime) (hlarge : 3 < p) (hd : p ∣ Nat.card Y) :
      L = (primeToResidual p M).map M.subtype := by
    cases c with
    | sl3 m => exact Preliminary.sl3_prime_residual D S m hp hlarge (hsupport p hp hd)
    | sp4 m => exact Preliminary.sp4_prime_residual D S m hp (hdiv p hd hp)
    | g2 m => exact Preliminary.g2_prime_residual D S m hp (hdiv p hd hp)
  apply oddCartanPart_le_of_primeToResidual Y M L hYM ho
  · intro p hp hlarge hd y hy
    change (y : G) ∈ L
    rw [hres p hp hlarge hd]
    exact mem_map_of_mem M.subtype hy
  · intro y hy hy3
    cases c with
    | sl3 m =>
      exact hcubic ⟨S.field.Carrier, inferInstance, inferInstance, S.field.card_eq,
        ⟨m.groupEquiv⟩⟩ y hy hy3
    | sp4 m =>
      rw [Preliminary.sp4_cubic_residual D S m]
      apply mem_map_of_mem M.subtype (x := ⟨y,hYM hy⟩)
      apply mem_primeToResidual_of_pow (n := 1)
      apply Subtype.ext
      simpa [hy3] using pow_orderOf_eq_one y
    | g2 m =>
      rw [Preliminary.g2_cubic_residual D S m]
      apply mem_map_of_mem M.subtype (x := ⟨y,hYM hy⟩)
      apply mem_primeToResidual_of_pow (n := 1)
      apply Subtype.ext
      simpa [hy3] using pow_orderOf_eq_one y

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
