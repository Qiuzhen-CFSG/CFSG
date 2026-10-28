module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.CubicNonsplit
public import Theory.GroupTheory.CyclicKernelPerfectLift
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel

/-!
# Alternating-six sections in the literal Held local groups

A perfect subgroup with simple A₆ two-core quotient retains that quotient
after projection by the ambient two-core. The remaining six-point kernel
is cubic. Its restriction to the perfect image is also a two-group, hence
trivial. The image in S₆ is therefore exactly A₆ by perfection and order.
This contradicts the checked noncommuting lifts in the nonsplit cubic cover.

Source: GLS3 Table 5.3p and Aschbacher–Smith A.3.12, pp.47–48.
-/

public noncomputable section
open Subgroup
open Held.LocalPairs.PairCoverage
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner
namespace Held.TwoLocalCandidates.AlternatingSix

/-- A perfect subgroup cannot split the actual cubic kernel above A₆. -/
private theorem no_perfect_lift (i : Bool) (U : Subgroup (LocalQuotient i)) [Group.IsPerfect U]
    (hi : Function.Injective ((SixPoint.quotientAction i).comp U.subtype))
    (hm : U.map (SixPoint.quotientAction i) = alternatingGroup (Fin 6)) : False := by
  let : IsCyclic (SixPoint.quotientAction i).ker := CubicNonsplit.quotientAction_kernel_isCyclic i
  obtain ⟨x,y,hx,hy,hc,hn⟩ := CubicNonsplit.noncommuting_even_lifts i
  rw [←hm] at hx hy
  exact hn (Theory.GroupTheory.commute_lifts_of_perfect_subgroup (SixPoint.quotientAction i) U hi hx hy hc)

/-- Neither native max3 nor max4 contains a perfect subgroup with simple
alternating-six quotient by its whole two-core. -/
theorem not_perfect_section (i : Bool) (B : Subgroup (localOvergroup i))
    [Group.IsPerfect B] (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := eB.isSimpleGroup
  let q := localQuotientMap i
  let U := B.map q
  let f := q.subgroupMap B
  have hfk : IsPGroup 2 f.ker := by
    rw [show f = q.subgroupMap B from rfl,ker_subgroupMap]
    have hq : IsPGroup 2 q.ker := by
      change IsPGroup 2 (QuotientGroup.mk' (pCore 2 (localOvergroup i))).ker
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup
    exact hq.comap_subtype
  let : Group.IsNilpotent f.ker := hfk.isNilpotent
  let eU : (U ⧸ pCore 2 U) ≃* alternatingGroup (Fin 6) :=
    (Theory.GroupTheory.PerfectCoreTwoExtension.solvableKernelQuotientEquiv f
      (q.subgroupMap_surjective B)).symm.trans eB
  let : Group.IsPerfect U := Group.IsPerfect.map q
  let : IsSimpleGroup (U ⧸ pCore 2 U) := eU.isSimpleGroup
  let g := (SixPoint.quotientAction i).comp U.subtype
  have hk3 : IsPGroup 3 (SixPoint.quotientAction i).ker := isPGroup_iff_card_dvd_pow.mpr
    ⟨1, by simpa only [pow_one] using ThreeCoreBounds.quotientAction_kernel_card_dvd_three i⟩
  have hg3 : IsPGroup 3 g.ker := hk3.comap_subtype
  let : Group.IsNilpotent g.ker := hg3.isNilpotent
  have hg2 : IsPGroup 2 g.ker := Theory.GroupTheory.PerfectCoreTwoExtension.ker_isTwoGroup g
  have hgb : g.ker = ⊥ := disjoint_self.mp (hg2.disjoint_of_coprime hg3 (by decide))
  have hi : Function.Injective g := (MonoidHom.ker_eq_bot_iff g).mp hgb
  let V := U.map (SixPoint.quotientAction i)
  let : Group.IsPerfect V := Group.IsPerfect.map _
  have hVA : V ≤ alternatingGroup (Fin 6) := by
    intro v hv
    rw [Equiv.Perm.mem_alternatingGroup]
    let s := Equiv.Perm.sign.comp V.subtype
    let : Group.IsPerfect s.range := Group.IsPerfect.range s
    exact congrArg Subtype.val (Subsingleton.elim (s.rangeRestrict ⟨v,hv⟩) 1)
  have heq : V = alternatingGroup (Fin 6) := by
    apply eq_of_le_of_card_ge hVA
    have hcard : Nat.card (U ⧸ pCore 2 U) = Nat.card (alternatingGroup (Fin 6)) :=
      Nat.card_congr eU.toEquiv
    have hle : Nat.card (alternatingGroup (Fin 6)) ≤ Nat.card U := by
      rw [←hcard]
      exact Nat.le_of_dvd (Nat.card_pos) (card_quotient_dvd_card _)
    have hV : Nat.card U = Nat.card V := by
      have he := Nat.card_congr (MonoidHom.ofInjective hi).toEquiv
      simpa only [g,MonoidHom.range_comp,range_subtype] using he
    exact hV ▸ hle
  exact no_perfect_lift i U hi heq

end Held.TwoLocalCandidates.AlternatingSix
