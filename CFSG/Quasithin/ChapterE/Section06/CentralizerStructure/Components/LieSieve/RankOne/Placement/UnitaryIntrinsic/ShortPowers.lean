module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PPerfectHom

/-!
# Excluding short subgroups by squared radical commutators

Suppose a normal two-subgroup R of B contains every b whose commutators
with R have square one. For a subnormal short subgroup X of a finite
power of B, [R^k,X] lies in the image of the intrinsic core commutator
U(X) = [O₂(X),X]. This uses relative subnormality and two-perfection.
The elementary-abelian clause of C.1.7 therefore puts each coordinate
of X in R. Two-perfection then makes X trivial, contradicting the
nonzero module clause. The same square test makes O₂(B) self-centralizing.

This criterion applies to the concrete unitary root–torus action; it
uses the complete short-group definition and assumes no rank bound or
block exclusion. Isomorphism transport retains relative subnormality.

Source: Aschbacher–Smith, C.1.7 and E.6.7–8, printed pp.123 and 246–248.
-/

public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.UnitaryIntrinsic

/-- The radical square test excludes every short subnormal subgroup of a finite power. -/
theorem noShort_power_of_square_test {B : Type*} [Group B] [Finite B]
    (R : Subgroup B) [R.Normal] (hp : IsPGroup 2 R)
    (htest : ∀ b : B, (∀ r ∈ R, ⁅r, b⁆ ^ 2 = 1) → b ∈ R)
    (k : ℕ) (X : Subgroup (Fin k → B)) (hs : X.IsSubnormal) :
    ¬ CFSG.Quasithin.ChapterC.IsShort X := by
  intro hx
  let P : Subgroup (Fin k → B) := pi Set.univ (fun _ => R)
  let : P.Normal := ⟨by
    intro x hx y i _
    exact (inferInstance : R.Normal).conj_mem _ (hx i (Set.mem_univ i)) _⟩
  have hpP : IsPGroup 2 P := by
    obtain ⟨n, hn⟩ := hp.exists_card_dvd_pow
    intro x
    refine ⟨n, Subtype.ext (funext fun i => ?_)⟩
    exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp
      ((_root_.orderOf_dvd_natCard (⟨x.val i, x.property i (Set.mem_univ i)⟩ : R)).trans hn))
  have hc : ⁅P, X⁆ ≤ (CFSG.Quasithin.ChapterC.blockU X).map X.subtype :=
    commutator_le_core_commutator_of_isSubnormal X P hs hx.twoPerfect hpP
      le_normalizer_of_normal
  let _ := hx.elementary
  let _ : IsElementaryAbelian 2 ((CFSG.Quasithin.ChapterC.blockU X).map X.subtype) :=
    IsElementaryAbelian.map_subtype
  have hXP : X ≤ P := by
    intro x hxx i _
    apply htest
    intro r hr
    have hrP : (fun _ : Fin k => r) ∈ P := fun _ _ => hr
    have hcomm := elemPow_eq_one_of_isElementaryAbelian (p := 2) _
      (hc (commutator_mem_commutator hrP hxx))
    exact congrFun hcomm i
  let f : X →* P := inclusion hXP
  have hf := hx.twoPerfect.hom_eq_one_of_isPGroup hpP f
  have hone (x : X) : x = 1 := by
    apply inclusion_injective hXP
    exact (DFunLike.congr_fun hf x).trans (map_one f).symm
  apply hx.blockU_ne_bot
  exact eq_bot_iff.mpr (fun x _ => mem_bot.mpr (hone x))

/-- A normal two-subgroup detecting squared commutators forces characteristic two. -/
theorem characteristicTwo_of_square_test {B : Type*} [Group B]
    (R : Subgroup B) [R.Normal] (hp : IsPGroup 2 R)
    (htest : ∀ b : B, (∀ r ∈ R, ⁅r, b⁆ ^ 2 = 1) → b ∈ R) :
    CFSG.Quasithin.HasCharacteristicTwo B := by
  have hR : R ≤ pCore 2 B := le_sSup ⟨inferInstance, hp⟩
  intro b hb
  apply hR
  apply htest
  intro r hr
  rw [commutatorElement_eq_one_iff_mul_comm.mpr
    (mem_centralizer_iff.mp hb r (hR hr)), one_pow]

/-- Transport the full short-subgroup exclusion through a genuine group equivalence. -/
theorem power_noShort_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B)
    (hB : ∀ k, ∀ X : Subgroup (Fin k → B), X.IsSubnormal →
      ¬ CFSG.Quasithin.ChapterC.IsShort X)
    (k : ℕ) (X : Subgroup (Fin k → A)) (hs : X.IsSubnormal) :
    ¬ CFSG.Quasithin.ChapterC.IsShort X := by
  intro hx
  let E : (Fin k → A) ≃* (Fin k → B) := MulEquiv.piCongrRight (fun _ => e)
  exact hB k (X.map E.toMonoidHom) (hs.map E.surjective)
    (hx.of_mulEquiv (X.equivMapOfInjective E.toMonoidHom E.injective))


end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.UnitaryIntrinsic
end
