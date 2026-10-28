module
public import Theory.GroupAction.IrreducibleSmallLinear
public import Theory.GroupTheory.CyclicNormalOddQuotient
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Irreducible odd actors in cyclic-normal outer quotients

An ambient homomorphism has trivial image on a noncyclic odd p-subgroup
whose normalizer acts irreducibly on its Frattini quotient, if the target
has a cyclic normal subgroup with cyclic odd-prime subgroups in its quotient.
First kill the cyclic quotient image by the invariant-kernel argument;
the remaining image lies in the cyclic normal subgroup and the same argument
kills it. Applied to the actual conjugation map, this places the actor in
N C_G(N).

Source application: Aschbacher–Smith, proof of 1.3.4, printed p.510.
-/

public section
namespace Subgroup
open Theory.GroupTheory
variable {G H : Type*} [Group G] [Finite G] [Group H]

theorem IsNormalizerFrattiniIrreducible.comp_eq_one_of_cyclicNormalOddQuotient
    {P : Subgroup G} (hirr : IsNormalizerFrattiniIrreducible P)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hP : IsPGroup p P)
    (hnc : ¬ IsCyclic P) (ρ : G →* H) (hH : HasCyclicNormalOddQuotient H) :
    ρ.comp P.subtype = 1 := by
  obtain ⟨N, hN, hc, hq⟩ := hH
  let := hN
  let := hc
  let q := QuotientGroup.mk' N
  let f := (q.comp ρ).comp P.subtype
  have hf : IsCyclic f.range :=
    hq p hp ho f.range (hP.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have hz := hirr.comp_eq_one_of_cyclic_range hnc (q.comp ρ) hf
  let g := ρ.comp P.subtype
  let i : g.range →* N := g.range.subtype.codRestrict N (by
    intro y
    obtain ⟨x, hx⟩ := y.property
    change (y : H) ∈ N
    rw [← hx]
    apply (QuotientGroup.eq_one_iff _).mp
    exact DFunLike.congr_fun hz x)
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : N => (z : H)) h)
  exact hirr.comp_eq_one_of_cyclic_range hnc ρ (isCyclic_of_injective i hi)
/-- A noncyclic irreducible odd actor induces only inner automorphisms on N. -/
theorem IsNormalizerFrattiniIrreducible.le_sup_centralizer_of_outer
    {P : Subgroup G} (hirr : IsNormalizerFrattiniIrreducible P)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hP : IsPGroup p P)
    (hnc : ¬ IsCyclic P) (N : Subgroup G) [N.Normal]
    (hN : HasCyclicNormalOddQuotient (MulAut.Outer N)) :
    P ≤ N ⊔ centralizer (N : Set G) := by
  let f : G →* MulAut.Outer N :=
    (QuotientGroup.mk' (MulAut.innerSubgroup N)).comp MulAut.conjNormal
  have hf := hirr.comp_eq_one_of_cyclicNormalOddQuotient hp ho hP hnc f hN
  rw [← MulAut.conjNormal_comap_innerSubgroup N]
  intro x hx
  change MulAut.conjNormal x ∈ MulAut.innerSubgroup N
  apply (QuotientGroup.eq_one_iff _).mp
  exact DFunLike.congr_fun hf ⟨x, hx⟩

end Subgroup
