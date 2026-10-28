module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Excluding the ordinary displaced-normalizer alternative

An actual prime-order actor normalizing D is conjugated into the normalizer
of the displaced D. Every such element belongs to the prime-to-p residual,
or to the order-three-generated theta when p = 3. If that subgroup equals
the relative component, the crossing centralization forces the actor to
centralize D, contradicting its constructed action.

Source: Aschbacher–Smith 2.5.7, printed p.556.
-/
public section
open Subgroup
open CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection.FieldReduction
variable {G : Type*} [Group G]
theorem ordinary_a318_impossible (L D X : Subgroup G) (g : G) {p : ℕ}
    (hp : p.Prime) (hX : Nat.card X=p)
    (hN : X ≤ normalizer (D:Set G))
    (hm : ¬ X ≤ centralizer (D:Set G))
    (hC : D.conjBy g ≤ centralizer (L:Set G))
    (he : L.subgroupOf (normalizer (D.conjBy g:Set G))=
      if p=3 then theta (normalizer (D.conjBy g:Set G))
      else primeToResidual p (normalizer (D.conjBy g:Set G))) : False := by
  apply hm
  intro a ha
  let f := (MulAut.conj g).toMonoidHom
  have han : f a ∈ normalizer (D.conjBy g:Set G) :=
    D.le_normalizer_map f (mem_map_of_mem f (hN ha))
  let b : normalizer (D.conjBy g:Set G) := ⟨f a,han⟩
  have hap : a^p=1 := orderOf_dvd_iff_pow_eq_one.mp (hX ▸ X.orderOf_dvd_natCard ha)
  have hbp : b^p=1 := Subtype.ext (by change (f a)^p=1;rw [←map_pow,hap,map_one])
  have hbL : b ∈ L.subgroupOf (normalizer (D.conjBy g:Set G)) := by
    rw [he]
    split_ifs with hp3
    · by_cases hb : b=1
      · exact hb ▸ one_mem _
      · apply Subgroup.subset_closure
        change orderOf b=3
        let : Fact p.Prime:=⟨hp⟩
        exact (orderOf_eq_prime hbp hb).trans hp3
    · exact mem_primeToResidual_of_pow (n:=1) (by simpa using hbp)
  have hfa : f a ∈ L := hbL
  rw [mem_centralizer_iff]
  intro d hd
  apply (MulAut.conj g).injective
  change f (d*a)=f (a*d)
  rw [map_mul,map_mul]
  exact (mem_centralizer_iff.mp (hC (mem_map_of_mem f hd)) (f a) hfa).symm

theorem prime_actor_normalizes_derived {X U : Subgroup G} (hN : X≤normalizer (U:Set G)) :
    X≤normalizer ((⁅U,U⁆:Subgroup G):Set G) := by
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (⁅U,U⁆:Subgroup G).map (MulAut.conj x).toMonoidHom=⁅U,U⁆
  have hfix : U.map (MulAut.conj x).toMonoidHom=U := mem_normalizer_iff_map_conj_eq.mp (hN hx)
  rw [map_commutator,hfix]

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection.FieldReduction
