module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.TransitivePair
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.CyclicKernelEndpoints
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.DihedralMarking
/-!
# Dihedral markings for a nonsingleton transitive factor family

The genuine SQTK cover forces a noncyclic starred factor to be normal,
contradicting transitivity and independence. The remaining cyclic source
witnesses have cyclic odd cores, hence are the marked dihedral rows of
D.2.17. Conjugation gives a common prime and support dimension. The final
lemma retains the original moved submodule and its possible fixed complement.

Source: Aschbacher--Smith 14.6.12(2), printed p.1031, and 15.1.2(3), p.1086.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
universe u
variable {G V : Type u} [Group G] [Finite G] [Group.IsSolvable G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G} [K.Normal]
  {U : Submodule (ZMod 2) V} (c : FactorData ρ K U)
  (d : Decomposition c.representation)
  (hcore : pCore 2 G = ⊥) (hq : cubicRatio ρ ≤ 2) (hd : d.FittingFull)
  {H : Type*} [Group H] [Finite H] {C : GroupClass}
  (hH : IsSQTK C H) (f : H →* G) (hf : Function.Surjective f)
  (π : G →* Equiv.Perm d.Index)
  (hp : ∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
    (c.ambientFactor d (π g i)).actor)
  (ht : ∀ i j, ∃ g : G, π g i = j) (hmore : 1 < Nat.card d.Index)
namespace FactorData
include hcore hq hd hH f hf π hp ht hmore

theorem transitive_factor_cyclic_star (i : d.Index)
    (A : Subgroup (d.factor i).Carrier) (hA : A ∈ QhatStar (d.factor i).action) :
    IsCyclic A := by
  classical
  by_contra hncyc
  have hr : 1 < rank A := by
    have hp := hA.1.2.1.rank_pos
    by_contra hn
    have hr : rank A = 1 := by omega
    have hc : Nat.card A = 2 := by rw [hA.1.2.1.card_eq_two_pow_rank,hr]; norm_num
    exact hncyc (isCyclic_of_prime_card hc)
  let F := d.factor i
  let j : F.Carrier →* G := K.subtype.comp F.embedding.groupMap
  let : Group.IsSolvable F.Carrier := Group.isSolvable_of_isSolvable_injective
    (f := j) (K.subtype_injective.comp F.embedding.group_injective)
  obtain ⟨B,r,hB,hrB⟩ := c.factor_cover d hH f hf i
  obtain ⟨s,h,ds,_,_⟩ := SourceReduction.source_noncyclic_global_configurations F.action
    hB r hrB F.faithful hA hr (generalizedFitting_eq_fitting_of_solvable F.Carrier)
    (c.factor_twoCore d hcore i) (hd i) F.generated
  let : IsElementaryAbelian 3 (pCore 3 F.Carrier) := h.elementary
  have hn : ¬ IsCyclic (pCore 3 F.Carrier) := by
    intro hc
    let := hc
    have hh := IsElementaryAbelian.exponent_dvd_p 3 (pCore 3 F.Carrier)
    rw [IsCyclic.exponent_eq_card,h.card_core] at hh
    rcases h.rank_cases with hs | hs <;> rw [hs] at hh <;> norm_num at hh
  let : IsElementaryAbelian 2 A := h.starred.1.2.1.2
  let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr h.starred.1.2.1.1
  obtain ⟨a,ha⟩ := exists_ne (1 : A)
  have ha1 : (a : F.Carrier) ≠ 1 := fun he => ha (Subtype.ext he)
  have ha2 : orderOf (a : F.Carrier) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (a : F.Carrier) a.property) ha1
  have ham : (a : F.Carrier) ∉ centralizer (pCore 3 F.Carrier : Set _) := by
    intro hh
    have hm : (a : F.Carrier) ∈ A ⊓ centralizer (pCore 3 F.Carrier : Set _) := ⟨a.property,hh⟩
    rw [h.actor_faithful] at hm
    exact ha1 hm
  apply c.transitive_actor_not_normal d π hp ht hmore i
  exact c.factor_actor_normal_of_noncyclic_core d (by decide : Odd 3) f hf
    (hH.stronglyQuasithin 3 (by decide) (by decide))
    (c.factor_starred_sylow_iff d hcore hq hd hH f hf) i hn a ha2 ham

theorem transitive_uniform_dihedral
    (hs : ∀ g i, (c.ambientFactor d i).space.map (ρ g) =
      (c.ambientFactor d (π g i)).space) :
    Nat.card d.Index = 2 ∧ ∃ p m, CyclicSource.PrimeDimensionOptions p m ∧
      ∀ i, ∃ l : CyclicSource.LocalGeneration (d.factor i).action,
        CyclicSource.DihedralMarking l p m := by
  have hlocal (i : d.Index) : Nat.card d.Index = 2 ∧
      ∃ p m, CyclicSource.PrimeDimensionOptions p m ∧
        ∃ l : CyclicSource.LocalGeneration (d.factor i).action,
          CyclicSource.DihedralMarking l p m := by
    obtain ⟨l⟩ := c.factor_cyclic_localGeneration d hcore hq hd hH f hf i
      (c.transitive_factor_cyclic_star d hcore hq hd hH f hf π hp ht hmore i)
    let : Fact l.prime.Prime := ⟨l.prime_prime⟩
    obtain ⟨hc,hcyc⟩ := c.transitive_core_bound d π hp ht hmore l.prime_odd f hf
      (hH.stronglyQuasithin l.prime l.prime_prime l.prime_odd)
      i l.involution l.order_two l.involution_not_centralizer_core
    obtain ⟨p,m,hpm,hm⟩ := l.marking_of_endpoints
      (l.cyclic_endpoints (d.factor i).faithful (l.kernel_isCyclic_of_core (hcyc i)))
    exact ⟨hc,p,m,hpm,l,hm⟩
  let i : d.Index := Classical.arbitrary d.Index
  obtain ⟨hc,p,m,hpm,l,hl⟩ := hlocal i
  refine ⟨hc,p,m,hpm,fun j => ?_⟩
  obtain ⟨_,q,n,hqn,k,hk⟩ := hlocal j
  obtain ⟨g,hg⟩ := ht i j
  have hj := hp g i
  rw [hg] at hj
  let e := c.factorCarrierEquivOfConjugate d g hj
  obtain ⟨ei⟩ := hl.dihedral
  obtain ⟨ej⟩ := hk.dihedral
  have hcard : 2 * p = 2 * q := by
    calc
      2*p = Nat.card (d.factor i).Carrier :=
        (Nat.card_congr ei.toEquiv).trans DihedralGroup.nat_card |>.symm
      _ = Nat.card (d.factor j).Carrier := Nat.card_congr e.toEquiv
      _ = 2*q := (Nat.card_congr ej.toEquiv).trans DihedralGroup.nat_card
  have hpq : q = p := by omega
  have hdim := c.transitive_factor_dimensions d π hs ht i j
  rw [hl.dimension,hk.dimension] at hdim
  have hnm : n = m := by omega
  subst q
  subst n
  exact ⟨k,hk⟩
end FactorData
end CFSG.Quasithin.ChapterD.RatioDecomposition

namespace CFSG.Quasithin.ChapterD.RatioDecomposition
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G} {U : Submodule (ZMod 2) V}
  (c : FactorData ρ K U) (d : Decomposition c.representation)
namespace FactorData

theorem two_factor_moved_decomposition (hc : Nat.card d.Index = 2) :
    ∃ i j : d.Index, i ≠ j ∧ (∀ k, k = i ∨ k = j) ∧
      (c.ambientFactor d i).actor ⊔ (c.ambientFactor d j).actor = K ∧
      Disjoint (c.ambientFactor d i).actor (c.ambientFactor d j).actor ∧
      (∀ x ∈ (c.ambientFactor d i).actor, ∀ y ∈ (c.ambientFactor d j).actor, Commute x y) ∧
      (c.ambientFactor d i).space ⊔ (c.ambientFactor d j).space = U ∧
      Disjoint (c.ambientFactor d i).space (c.ambientFactor d j).space := by
  obtain ⟨i,j,hij,hall⟩ := Nat.card_eq_two_iff.mp hc
  have hk (k : d.Index) : k = i ∨ k = j := by
    have hh : k ∈ ({i,j} : Set d.Index) := hall.symm ▸ Set.mem_univ k
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hh
  have hsup : (⨆ k, (c.ambientFactor d k).actor) = K := by
    simp only [ambientFactor,Factor.map_actor,embedding,←Subgroup.map_iSup,
      d.group_generation,←MonoidHom.range_eq_map,Subgroup.range_subtype]
  have hact : (c.ambientFactor d i).actor ⊔ (c.ambientFactor d j).actor = K := by
    apply Eq.trans _ hsup
    apply le_antisymm
    · exact sup_le (le_iSup (fun k => (c.ambientFactor d k).actor) i)
        (le_iSup (fun k => (c.ambientFactor d k).actor) j)
    · exact iSup_le fun k => by rcases hk k with rfl | rfl; exact le_sup_left; exact le_sup_right
  have hspace : (c.ambientFactor d i).space ⊔ (c.ambientFactor d j).space = U := by
    apply Eq.trans _ (c.ambient_spaces_generate d)
    apply le_antisymm
    · exact sup_le (le_iSup (fun k => (c.ambientFactor d k).space) i)
        (le_iSup (fun k => (c.ambientFactor d k).space) j)
    · exact iSup_le fun k => by rcases hk k with rfl | rfl; exact le_sup_left; exact le_sup_right
  refine ⟨i,j,hij,hk,hact,?_,?_,?_⟩
  · simpa only [ambientFactor,Factor.map_actor,embedding] using
      Subgroup.disjoint_map K.subtype_injective (d.actors_independent.pairwiseDisjoint hij)
  · intro x hx y hy
    simp only [ambientFactor,Factor.map_actor,embedding] at hx hy
    obtain ⟨x,hx,rfl⟩ := hx
    obtain ⟨y,hy,rfl⟩ := hy
    exact congrArg K.subtype (d.actors_commute c.faithful hij hx hy).eq
  · exact ⟨hspace,(c.ambient_spaces_independent d).pairwiseDisjoint hij⟩
end FactorData
end CFSG.Quasithin.ChapterD.RatioDecomposition
