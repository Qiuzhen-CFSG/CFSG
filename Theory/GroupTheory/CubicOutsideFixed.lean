module

public import Theory.GroupTheory.CommutatorPreimage
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.NumberTheory.Divisors
public import Mathlib.GroupTheory.Index

/-!
# Outside centralizers from a cubic fixed preimage

If a fixed preimage is V∩D of index3 in V, an element outside V in D
cannot commute with a V-element outside D. Otherwise its commutator
preimage contains V∩D and that additional element, hence all of V,
contradicting the specified cubic fixed-preimage criterion.
Source: Aschbacher, Sporadic Groups (1994),45.8(2),printed p246.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem cubic_outside_fixed_of_preimage (V D W:Subgroup G) (y:G) (hy:y∈V)
    (hV:Nat.card V=81) (hcap:Nat.card (V⊓D:Subgroup G)=27)
    (hVW:V≤normalizer (W:Set G)) (hcomm:⁅D,D⁆≤W)
    (hpre:∀d∈D,y*d*y⁻¹*d⁻¹∈W→d∈V) :
    ∀d∈D,d∉V→V⊓centralizer ({d}:Set G)≤D := by
  intro d hd hdV v hv
  by_contra hvD
  let E:=commutatorPreimage V (zpowers d) W
  have hEV:E≤V:=commutatorPreimage_le _ _ _
  have hAE:V⊓D≤E:=le_commutatorPreimage inf_le_left
    ((commutator_mono inf_le_right (zpowers_le.mpr hd)).trans hcomm)
  have hvE:v∈E:=by
    have hz:zpowers v≤centralizer (zpowers d:Set G):=by
      rw [le_centralizer_iff,zpowers_le]
      rw [Subgroup.zpowers_eq_closure,centralizer_closure,mem_centralizer_singleton_iff]
      exact (mem_centralizer_singleton_iff.mp hv.2).symm
    exact (le_commutatorPreimage (zpowers_le.mpr hv.1)
      (by rw [commutator_eq_bot_iff_le_centralizer.mpr hz];exact bot_le)) (mem_zpowers v)
  have hecard:Nat.card E=81:=by
    have hdiv:Nat.card E∣81:=hV ▸ card_dvd_of_le hEV
    have hlo:27≤Nat.card E:=hcap ▸ card_le_of_le hAE
    have hne:Nat.card E≠27:=by
      intro he
      have hEq:V⊓D=E:=eq_of_le_of_card_ge hAE (by rw [he,hcap])
      exact hvD ((hEq.ge hvE).2)
    have hh:=Nat.mem_divisors.mpr ⟨hdiv,(by decide:81≠0)⟩
    have hs:Nat.divisors 81={1,3,9,27,81}:=by decide
    simp only [hs,Finset.mem_insert,Finset.mem_singleton] at hh
    omega
  have he:E=V:=eq_of_le_of_card_ge hEV (by rw [hecard,hV])
  have hbound:=commutator_commutatorPreimage_le V (zpowers d) W hVW
  have hyE:y∈E:=he ▸ hy
  have hmem:⁅y,d⁆∈W:=hbound (commutator_mem_commutator hyE (mem_zpowers d))
  exact hdV (hpre d hd hmem)
end Subgroup
