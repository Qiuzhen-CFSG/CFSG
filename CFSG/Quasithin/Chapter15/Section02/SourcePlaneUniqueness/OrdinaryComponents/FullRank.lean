module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.ComponentData
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.PrimeComplement
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.Descent
public import Theory.GroupAction.ComponentRankAction.OuterTwo

/-!
# The full-rank ordinary component and its marked fixed subgroup

The actual wreath quotient makes H a {2,3}-group. Its embedded two-residual
K therefore lies in O^{3′}(I). For a centerless component of three-rank two
with two-group outer quotient, the proved A.3.18 theorem identifies the
component itself with O^{3′}(I). Thus K lies in this component and, because
K centralizes z, in its literal fixed subgroup. The wreath calculation
supplies m₃(K) = 2, so that fixed subgroup also has three-rank at least two.

Faithfulness of Z independently proves that its marked automorphism has
order two. No normality or component-containment callback remains.
Source: Aschbacher--Smith,15.2.24 and the proof of15.2.15,
printed pp.1117--1118, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 Candidates.ComponentStructure ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)
include d

/-- K lies in the literal O^{3′}(I), since the original H is a {2,3}-group. -/
theorem residual_le_escape_primeToResidual (hI : PlaneEscapes Mc ZS I) :
    (pResidual 2 H).map H.subtype ≤ (primeToResidual 3 I).map I.subtype := by
  let K := (pResidual 2 H).map H.subtype
  have hKI : K ≤ I :=
    (le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  let A := K.subgroupOf I
  let e := subgroupOfEquivOfLe hKI
  let f : A →* H := (inclusion (show K ≤ H from map_subtype_le _)).comp e.toMonoidHom
  have hpi : IsPiGroup twoThreePrimes A :=
    (ChosenGeometry.twoThree_of_wreath H d.geometry.quotient.some).of_injective f
      ((inclusion_injective (show K ≤ H from map_subtype_le _)).comp e.injective)
  have hpA : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2 H).of_surjective
    e.symm.toMonoidHom e.symm.surjective
  have ht : primeToResidual 3 A = ⊤ :=
    (twoResidual_eq_primeToResidual_three hpi).symm.trans ((pResidual_eq_top_iff 2 A).mpr hpA)
  have hA : A ≤ primeToResidual 3 I := by
    have hh := map_primeToResidual_le_of_hom 3 A.subtype
    rw [ht, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  exact (map_subgroupOf_eq_of_le hKI).symm.le.trans (map_mono hA)

omit d in
include hsource in
/-- A.3.18 identifies the actual full-rank component with O^{3′}(I). -/
theorem component_eq_cubic_residual (hI : PlaneEscapes Mc ZS I)
    (hcenter : center c.component = ⊥) (hr : 2 ≤ primeRank 3 c.component)
    (ho : IsPGroup 2 (MulAut.Outer c.component)) :
    c.component = primeToResidual 3 I := by
  let e : (c.component ⧸ center c.component) ≃* c.component :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  exact (Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual_of_outer_twoGroup
    c.isComponent (by rw [hcenter]; simp) hr
    ((Chapter3.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin 3 (by decide) (by decide))
    e (by decide) ho).2

/-- The same original K embeds in the fixed subgroup, which has three-rank at least two. -/
theorem fixed_three_rank_of_full_component (hI : PlaneEscapes Mc ZS I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (hcenter : center c.component = ⊥) (hr : 2 ≤ primeRank 3 c.component)
    (ho : IsPGroup 2 (MulAut.Outer c.component))
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹) :
    2 ≤ primeRank 3 a.fixedSubgroup := by
  let K := (pResidual 2 H).map H.subtype
  have hKL : K ≤ c.component.map I.subtype := by
    rw [component_eq_cubic_residual (hsource := hsource) c hI hcenter hr ho]
    exact residual_le_escape_primeToResidual d hI
  let e := c.component.equivMapOfInjective I.subtype I.subtype_injective
  let f : K →* c.component := e.symm.toMonoidHom.comp (inclusion hKL)
  have hf (k : K) : ((f k : I) : G) = k := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨k,hKL k.property⟩)
  have hfix (k : K) : f k ∈ a.fixedSubgroup := by
    rw [MulAut.mem_fixedSubgroup]
    apply Subtype.ext
    apply Subtype.ext
    rw [ha,hf]
    have hkMc : (k : G) ∈ Mc :=
      ((le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_left) k.property
    have hkz : (k : G) * z = z * k := mem_centralizer_singleton_iff.mp
      ((marked_centralizer d hI hz hzne).2.ge hkMc)
    rw [← hkz,mul_inv_cancel_right]
  let g := f.codRestrict a.fixedSubgroup hfix
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact (hf x).symm.trans ((congrArg (fun w : a.fixedSubgroup => ((w.val : I) : G)) h).trans (hf y))
  have hbound := _root_.primeRank_le_of_injective 3 g hg
  rw [PlaneUniquenessPreceding.LinearThree.residual_rank_two d] at hbound
  exact hbound

omit d [Finite G] in
/-- Faithfulness of Z detects the order of its literal component automorphism. -/
theorem marked_component_action_order_two
    (horder : orderOf z = 2) (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹) :
    orderOf a = 2 := by
  have ha2 : a ^ 2 = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change ((a (a x) : I) : G) = (x : G)
    rw [ha,ha]
    have hz2 : z*z=1 := by simpa [pow_two,horder] using pow_orderOf_eq_one z
    calc
      _ = (z*z) * (x : G) * (z*z)⁻¹ := by group
      _ = _ := by rw [hz2]; simp
  have hane : a ≠ 1 := by
    intro he
    have hzc : z ∈ centralizer (c.component.map I.subtype : Set G) := by
      rintro x ⟨l,hl,rfl⟩
      have hh := ha ⟨l,hl⟩
      rw [he] at hh
      change (l : G) = z * (l : G) * z⁻¹ at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    have hh : z ∈ centralInvolutions T ⊓ centralizer (c.component.map I.subtype : Set G) := ⟨hz,hzc⟩
    rw [c.faithful,mem_bot] at hh
    exact hzne hh
  exact ((Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one ha2)).resolve_left
    (by simpa only [orderOf_eq_one_iff] using hane)

end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
