module
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupAction.AutomorphismFixedResidualTransport
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# An S₆ overgroup of the original perfect HS fixed subgroup

After the center of E is trivial, its literal central-quotient map is an
isomorphism. The marked product-class action therefore identifies the full
fixed group with C₂ × Aut(A₆). A perfect subgroup has trivial first projection,
and its second projection lies in the natural S₆, which has index two in
Aut(A₆). The canonical S₆ subgroup of that product contains the original
perfect subgroup. Transporting it back retains this literal containment.

Applied to the original fixed component B, this supplies the S₆ overgroup
used by the source nonfull-A₆ action contradiction. Component uniqueness and
an additional equivalence B ≃ A₆ are unnecessary for this local implication.

Source: Aschbacher–Smith 2.5.19–21, printed pp.562 and 566; the intrinsic HS
centralizer is the product class in 16.1.5(10), printed p.1172.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6.HSFixed
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open HSInner
open Sporadic.LeechRelated.HS AlternatingSix.ShadowLocal

private theorem product_perfect_subgroup_in_symmetric
    (B : Subgroup (C2 × AutA6)) [Group.IsPerfect B] :
    ∃ C : Subgroup (C2 × AutA6), B ≤ C ∧ Nonempty (C ≃* Equiv.Perm (Fin 6)) := by
  let f : Equiv.Perm (Fin 6) →* C2 × AutA6 :=
    (1 : Equiv.Perm (Fin 6) →* C2).prod permutationAction
  have hf : Function.Injective f := by
    intro x y h
    exact permutationAction_injective (congrArg Prod.snd h)
  refine ⟨f.range, ?_, ⟨(MonoidHom.ofInjective hf).symm⟩⟩
  let Bfst := B.map (MonoidHom.fst C2 AutA6)
  let Bsnd := B.map (MonoidHom.snd C2 AutA6)
  let : Group.IsPerfect Bfst := Group.IsPerfect.map _
  let : Group.IsPerfect Bsnd := Group.IsPerfect.map _
  have hsn : Bsnd ≤ natural := le_of_isPerfect_of_index_eq_two Bsnd natural
    GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index
  intro x hx
  have hx1 : x.1 = 1 := by
    let y : Bfst := ⟨x.1, mem_map_of_mem (MonoidHom.fst C2 AutA6) hx⟩
    exact congrArg Subtype.val (Subsingleton.elim y (1 : Bfst))
  obtain ⟨p, hp⟩ := hsn (mem_map_of_mem (MonoidHom.snd C2 AutA6) hx)
  exact ⟨p, Prod.ext hx1.symm hp⟩

private theorem fixed_equiv_product {E : Type*} [Group E]
    (hz : center E = ⊥) (e : (E ⧸ center E) ≃* Carrier) (a : MulAut E)
    (hmark : MulAut.congr e (quotientAut (center E) a) = MulAut.conj ClassCoverage.t) :
    Nonempty (a.fixedSubgroup ≃* C2 × AutA6) := by
  let q : E ≃* E ⧸ center E := MulEquiv.ofBijective (QuotientGroup.mk' (center E))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hz]),
      QuotientGroup.mk'_surjective _⟩
  let f := q.trans e
  have heq : ∀ x : E, f (a x) = MulAut.conj ClassCoverage.t (f x) := by
    intro x
    change e (QuotientGroup.mk' (center E) (a x)) =
      MulAut.conj ClassCoverage.t (e (QuotientGroup.mk' (center E) x))
    have hm : MulAut.centralQuotientAction e a = MulAut.conj ClassCoverage.t := hmark
    rw [← hm]
    exact (MulAut.centralQuotientAction_apply e a x).symm
  let j := MulAut.fixedSubgroupEquivOfCompatible f a (MulAut.conj ClassCoverage.t) heq
  obtain ⟨k⟩ := ClassCoverage.product_centralizer_equiv
  exact ⟨j.trans ((MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj ClassCoverage.t)).trans k)⟩

/-- The original perfect fixed subgroup lies in an actual S₆ subgroup of the
same fixed group, with the marked HS quotient action retained. -/
theorem exists_symmetric_six_overgroup {E : Type*} [Group E]
    (hz : center E = ⊥) (e : (E ⧸ center E) ≃* Carrier) (a : MulAut E)
    (hmark : MulAut.congr e (quotientAut (center E) a) = MulAut.conj ClassCoverage.t)
    (B : Subgroup a.fixedSubgroup) [Group.IsPerfect B] :
    ∃ C : Subgroup a.fixedSubgroup, B ≤ C ∧ Nonempty (C ≃* Equiv.Perm (Fin 6)) := by
  obtain ⟨f⟩ := fixed_equiv_product hz e a hmark
  let D := B.map f.toMonoidHom
  let : Group.IsPerfect D := Group.IsPerfect.map _
  obtain ⟨C, hDC, ⟨k⟩⟩ := product_perfect_subgroup_in_symmetric D
  refine ⟨C.map f.symm.toMonoidHom, ?_, ⟨(f.symm.subgroupMap C).symm.trans k⟩⟩
  intro x hx
  exact ⟨f x, hDC (mem_map_of_mem f.toMonoidHom hx), f.symm_apply_apply x⟩
end CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6.HSFixed
