module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.Basic
public import Theory.GroupTheory.TightlyEmbedded

/-!
# Intersection control from the component-pair residual theorem

For the nonnormal component configuration of §16.2, A.1.34 supplies an odd
local prime of L/Z(L). Its exceptional alternative has odd ambient centralizer,
whereas z centralizes L₀, so O^{p′}(H) = L₀. Quasisimplicity shows that L and
its conjugates are p′-perfect. If a conjugate component centralizes L and lies
in H, it therefore lies in L₀ = LL^u; perfectness then puts it in L^u.
This proves the intersection assertion without an extra component-lifting
premise from I.3.2.

All inputs here are explicit: the parent constructs the orbit and persistence,
and the earlier A.1.34 owner supplies the two indicated clauses. The remaining
model obligations are to identify the precise local primes in 16.2.9 and to
establish the center-free alternatives in 16.2.8(2). The theorem with a
center-free premise is only the finite-group reduction of that clause.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, A.1.34, printed pp.29–30, and 16.2.8–9, p.1175.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry
universe u
variable {G : Type u} [Group G]

/-- An odd prime occurring in an actual two-local subgroup. -/
def IsOddLocalPrime (p : ℕ) (X : Type*) [Group X] : Prop :=
  p.Prime ∧ Odd p ∧ ∃ M : Subgroup X, IsTwoLocal M ∧ p ∣ Nat.card M

private theorem localPrime_dvd_card {X : Type*} [Group X] {p : ℕ}
    (hp : IsOddLocalPrime p X) : p ∣ Nat.card X := by
  obtain ⟨_, _, M, _, hd⟩ := hp
  exact hd.trans M.card_subgroup_dvd_card

private theorem residual_index_coprime {X : Type*} [Group X] [Finite X]
    (p : ℕ) [Fact p.Prime] : p.Coprime (primeToResidual p X).index := by
  let P : Sylow p X := Classical.choice inferInstance
  have hP : (P : Subgroup X) ≤ primeToResidual p X := by
    intro x hx
    obtain ⟨n, hn⟩ := P.2 ⟨x, hx⟩
    exact mem_primeToResidual_of_pow (congrArg Subtype.val hn)
  exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr P.not_dvd_index).coprime_dvd_right
    (index_dvd_of_le hP)

private theorem quasisimple_residual_eq_top {X : Type*} [Group X] [Finite X]
    [IsQuasisimple X] {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card (X ⧸ center X)) :
    primeToResidual p X = ⊤ := by
  let : Fact p.Prime := ⟨hp⟩
  rcases IsQuasisimple.normal_le_center_or_eq_top (primeToResidual p X) with hc | ht
  · have hcop := (residual_index_coprime p (X := X)).coprime_dvd_right
      (index_dvd_of_le hc)
    rw [index_eq_card] at hcop
    exact ((hp.coprime_iff_not_dvd.mp hcop) hd).elim
  · exact ht

private theorem residual_map_le {X Y : Type*} [Group X] [Group Y]
    (p : ℕ) (f : X →* Y) : (primeToResidual p X).map f ≤ primeToResidual p Y := by
  apply le_sInf
  rintro N ⟨hN, hc⟩
  let := hN
  rw [map_le_iff_le_comap]
  apply primeToResidual_le
  rw [N.index_comap]
  exact hc.coprime_dvd_right (N.relIndex_dvd_index_of_normal f.range)

private theorem residual_contains {A B : Subgroup G} {p : ℕ}
    (hAB : A ≤ B) (hself : primeToResidual p A = ⊤) :
    A ≤ (primeToResidual p B).map B.subtype := by
  intro a ha
  have hm := residual_map_le p (inclusion hAB)
  have hi : inclusion hAB ⟨a, ha⟩ ∈ primeToResidual p B :=
    hm (mem_map_of_mem _ (by rw [hself]; trivial))
  exact mem_map_of_mem B.subtype hi

private theorem conjugate_residual_eq_top {A : Subgroup G} {p : ℕ}
    (hself : primeToResidual p A = ⊤) (g : G) :
    primeToResidual p (conjugate A g) = ⊤ := by
  have hm := map_primeToResidual (p := p) ((MulAut.conj g⁻¹).subgroupMap A)
  rw [hself, map_top_of_surjective _ ((MulAut.conj g⁻¹).subgroupMap A).surjective] at hm
  exact hm.symm

private theorem perfect_le_second {A B D : Subgroup G} [Group.IsPerfect D]
    (hAB : ⁅A, B⁆ = ⊥) (hD : D ≤ A ⊔ B) (hAD : ⁅A, D⁆ = ⊥) : D ≤ B := by
  have hAn : A ≤ normalizer (B : Set G) :=
    (commutator_eq_bot_iff_le_centralizer.mp hAB).trans (centralizer_le_normalizer _)
  have hDn : D ≤ normalizer (B : Set G) := hD.trans (sup_le hAn B.le_normalizer)
  rw [← commutator_eq_self (H := D)]
  apply commutator_le.mpr
  intro x hx y hy
  have hx' : x ∈ (A : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A B
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hAB)).trans
        (centralizer_le_normalizer _))]
    exact hD hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  have hay : ⁅a, y⁆ = 1 :=
    show ⁅a, y⁆ ∈ (⊥ : Subgroup G) from hAD ▸ commutator_mem_commutator ha hy
  have hby : ⁅b, y⁆ ∈ B :=
    commutator_le.mp (le_normalizer_iff_commutator_le_left.mp hDn) b hb y hy
  rw [commutatorElement_mul_left_eq_conj_mul, hay, mul_one]
  exact (hAn ha _).mp hby



/-- The consequences of A.1.34(1) used here, retained as an earlier-source
input. The source's exceptional branch additionally has p = 3, a full
SU₃(8) component, and a non-SQTK-quotient ambient group. Forgetting those
extra conjuncts gives this weaker disjunction; its centralizer remains the
ambient C_G(AB), and the primes are tested in A/Z(A). This definition does
not assert the earlier theorem. -/
def ComponentPairResidualInput [Finite G] (K : GroupClass.{u}) : Prop :=
  IsQuasithin G → ∀ M : Subgroup G, IsKGroup K M →
    ∀ A B : Subgroup G, IsComponentIn A M → IsComponentIn B M →
      A ≠ B → Nonempty (A ≃* B) →
      (∃ p, IsOddLocalPrime p (A ⧸ center A)) ∧
      ∀ p, IsOddLocalPrime p (A ⧸ center A) →
        (primeToResidual p M).map M.subtype = A ⊔ B ∨
        Odd (Nat.card (centralizer ((A ⊔ B : Subgroup G) : Set G)))

variable {T : Sylow 2 G} {z : G} {L : Subgroup G} {u : G}

private theorem even_card_of_involution {A : Subgroup G} {t : G}
    (ht : t ∈ A) (ht2 : orderOf t = 2) : Even (Nat.card A) := by
  apply even_iff_two_dvd.mpr
  have ho : orderOf (⟨t, ht⟩ : A) = 2 := by rwa [← orderOf_coe]
  rw [← ho]
  exact orderOf_dvd_natCard _

private theorem even_card_mono {A B : Subgroup G} (hab : A ≤ B)
    (ha : Even (Nat.card A)) : Even (Nat.card B) :=
  even_iff_two_dvd.mpr ((even_iff_two_dvd.mp ha).trans (card_dvd_of_le hab))

/-- Restriction to the normal local closure puts L among the components of H. -/
theorem component_in_localNormalizer (h : CentralComponentSetup T z L) :
    IsComponentIn L (localComponentNormalizer z L) := by
  have hL := (show IsComponentIn L (involutionCentralizer z) from h.component).restrict
    component_le_closure (closure_le_centralizer h)
  exact hL.of_subnormal (localComponentClosure z L).le_normalizer ((normal_subgroupOf_iff_le_normalizer (localComponentClosure z L).le_normalizer).mpr le_rfl).isSubnormal

/-- The same restriction and normal ascent for the swapped component. -/
theorem swapped_component_in_localNormalizer (h : CentralComponentSetup T z L)
    (o : TwoComponentOrbit T z L u) :
    IsComponentIn (conjugate L u) (localComponentNormalizer z L) := by
  have hL := (o.swapped_component h).restrict
    ((o.closure_eq_pair h).symm ▸ le_sup_right) (closure_le_centralizer h)
  exact hL.of_subnormal (localComponentClosure z L).le_normalizer ((normal_subgroupOf_iff_le_normalizer (localComponentClosure z L).le_normalizer).mpr le_rfl).isSubnormal

private theorem centralizer_closure_even (h : CentralComponentSetup T z L) :
    Even (Nat.card (centralizer (localComponentClosure z L : Set G))) := by
  apply even_card_of_involution (t := z) _ h.involution
  intro x hx
  exact ((closure_le_centralizer h hx) z (Set.mem_singleton z)).symm

/-- A.1.34 supplies an odd local prime of the simple central quotient. -/
theorem exists_residual_prime [Finite G] {K : GroupClass.{u}}
    (c : CounterexampleSetup K T z L) (o : TwoComponentOrbit T z L u)
    (a134 : ComponentPairResidualInput (G := G) K) :
    ∃ p, IsOddLocalPrime p (L ⧸ center L) := by
  exact (a134 c.global.quasithin _ (c.global.properK _ c.localNormalizer_ne_top)
    L (conjugate L u) (component_in_localNormalizer c.localSetup)
    (swapped_component_in_localNormalizer c.localSetup o) o.moved.symm
    ⟨(MulAut.conj u⁻¹).subgroupMap L⟩).1

/-- For every odd local prime of L/Z(L), z excludes the exceptional
odd-centralizer branch of A.1.34, giving O^{p′}(H) = L₀. -/
theorem localNormalizer_residual [Finite G] {K : GroupClass.{u}}
    (c : CounterexampleSetup K T z L) (o : TwoComponentOrbit T z L u)
    (a134 : ComponentPairResidualInput (G := G) K) {p : ℕ}
    (hp : IsOddLocalPrime p (L ⧸ center L)) :
    (primeToResidual p (localComponentNormalizer z L)).map
      (localComponentNormalizer z L).subtype = localComponentClosure z L := by
  have hr := (a134 c.global.quasithin _ (c.global.properK _ c.localNormalizer_ne_top)
    L (conjugate L u) (component_in_localNormalizer c.localSetup)
    (swapped_component_in_localNormalizer c.localSetup o) o.moved.symm
    ⟨(MulAut.conj u⁻¹).subgroupMap L⟩).2 p hp
  rw [← o.closure_eq_pair c.localSetup] at hr
  exact hr.resolve_right (Nat.not_odd_iff_even.mpr (centralizer_closure_even c.localSetup))

/-- Both commuting factors are p′-perfect, and they generate L₀. -/
theorem closure_residual_eq_top [Finite G] (h : CentralComponentSetup T z L)
    (o : TwoComponentOrbit T z L u) {p : ℕ}
    (hp : IsOddLocalPrime p (L ⧸ center L)) :
    primeToResidual p (localComponentClosure z L) = ⊤ := by
  let := (show IsComponentIn L (involutionCentralizer z) from h.component).quasisimple
  have hL := quasisimple_residual_eq_top hp.1 (localPrime_dvd_card hp)
  have hU := conjugate_residual_eq_top hL u
  have h1 := residual_contains (component_le_closure (z := z) (L := L)) hL
  have h2 := residual_contains (show conjugate L u ≤ localComponentClosure z L by
    rw [o.closure_eq_pair h]; exact le_sup_right) hU
  have hc : localComponentClosure z L ≤
      (primeToResidual p (localComponentClosure z L)).map (localComponentClosure z L).subtype := by
    exact (o.closure_eq_pair h).le.trans (sup_le h1 h2)
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := hc x.property
  exact (Subtype.ext he : y = x) ▸ hy


private theorem conjugate_centralizer (t g : G) :
    conjugate (involutionCentralizer t) g =
      involutionCentralizer ((MulAut.conj g⁻¹) t) := by
  let e := MulAut.conj g⁻¹
  ext x
  change x ∈ (involutionCentralizer t).map e.toMonoidHom ↔ _
  rw [mem_map_equiv]
  change e.symm x ∈ involutionCentralizer t ↔ x ∈ involutionCentralizer (e t)
  simp only [involutionCentralizer, mem_centralizer_singleton_iff]
  constructor
  · intro he
    have hm := congrArg e he
    simpa only [map_mul, MulEquiv.apply_symm_apply] using hm
  · intro he
    have hm := congrArg e.symm he
    simpa only [map_mul, MulEquiv.symm_apply_apply] using hm

private theorem conjugate_persistence (persist : ComponentPersistence z L u)
    {t g : G} (ht : t ∈ conjugate (involutionContainer z L u) g)
    (ht2 : orderOf t = 2) : IsCentralizerComponent t (conjugate L g) := by
  obtain ⟨s, hs, he⟩ := ht
  have hs2 : orderOf s = 2 := by
    rw [← orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective, he]
    exact ht2
  have hm := (show IsComponentIn L (involutionCentralizer s) from persist s hs hs2).map
    (MulAut.conj g⁻¹)
  change IsComponentIn (conjugate L g) (conjugate (involutionCentralizer s) g) at hm
  change (MulAut.conj g⁻¹) s = t at he
  rwa [conjugate_centralizer, he] at hm

private theorem mem_localNormalizer_of_conjugate_eq_swapped
    (h : CentralComponentSetup T z L) (o : TwoComponentOrbit T z L u)
    (hn : normalizer (L : Set G) ≤ localComponentNormalizer z L)
    {g : G} (he : conjugate L g = conjugate L u) :
    g ∈ localComponentNormalizer z L := by
  have hgu : g * u⁻¹ ∈ normalizer (L : Set G) := by
    apply (mem_normalizer_iff_conjugate_eq _ _).mpr
    rw [← conjugate_conjugate, he, conjugate_conjugate, mul_inv_cancel, conjugate_one]
  simpa using (localComponentNormalizer z L).mul_mem (hn hgu) (o.swap_mem_localNormalizer h)

/-- 16.2.8(1), using A.1.34 before the intersection argument.
No balance or C-component lifting assertion is needed on this route. -/
theorem even_intersection_mem_localNormalizer [Finite G] {K : GroupClass.{u}}
    (c : CounterexampleSetup K T z L) (o : TwoComponentOrbit T z L u)
    (pair : ComponentPairExhaustion K G)
    (a134 : ComponentPairResidualInput (G := G) K)
    (persist : ComponentPersistence z L u)
    {v : G} (hv : v ∈ conjugate L u) (hv2 : orderOf v = 2)
    (g : G)
    (heven : Even (Nat.card (involutionContainer z L u ⊓
      conjugate (involutionContainer z L u) g : Subgroup G))) :
    g ∈ localComponentNormalizer z L := by
  have hn := (show normalizer (L : Set G) ≤
      normalizer (L : Set G) ⊔ normalizer (conjugate L u : Set G) from le_sup_left).trans
    (normalizers_le_localNormalizer c o pair persist hv hv2)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
  have ht2 : orderOf (t : G) = 2 := by rwa [orderOf_coe]
  have hL : IsComponentIn L (involutionCentralizer (t : G)) :=
    persist t t.property.1 ht2
  have hLg : IsComponentIn (conjugate L g) (involutionCentralizer (t : G)) :=
    conjugate_persistence persist t.property.2 ht2
  by_cases he : conjugate L g = L
  · exact hn ((mem_normalizer_iff_conjugate_eq _ _).mpr he)
  have hc : ⁅L, conjugate L g⁆ = ⊥ := hL.commutator_eq_bot_of_ne hLg (Ne.symm he)
  have hgH : conjugate L g ≤ localComponentNormalizer z L :=
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
      (centralizer_le_normalizer _)).trans hn
  obtain ⟨p, hp⟩ := exists_residual_prime c o a134
  let := hL.quasisimple
  have hself := quasisimple_residual_eq_top hp.1 (localPrime_dvd_card hp)
  have hinc := residual_contains hgH (conjugate_residual_eq_top hself g)
  rw [localNormalizer_residual c o a134 hp, o.closure_eq_pair c.localSetup] at hinc
  let := hLg.quasisimple
  have hle := perfect_le_second (o.commute c.localSetup) hinc hc
  have heU : conjugate L g = conjugate L u :=
    eq_of_le_of_card_ge hle (Nat.card_congr
      (((MulAut.conj u⁻¹).subgroupMap L).symm.trans
        ((MulAut.conj g⁻¹).subgroupMap L)).toEquiv).le
  exact mem_localNormalizer_of_conjugate_eq_swapped c.localSetup o hn heU

/-- 16.2.9(2), with the residual premises now discharged from A.1.34. -/
theorem closure_not_le_conjugate_localNormalizer [Finite G] {K : GroupClass.{u}}
    (c : CounterexampleSetup K T z L) (o : TwoComponentOrbit T z L u)
    (a134 : ComponentPairResidualInput (G := G) K)
    {g : G} (hg : g ∉ localComponentNormalizer z L) :
    ¬ localComponentClosure z L ≤ conjugate (localComponentNormalizer z L) g := by
  obtain ⟨p, hp⟩ := exists_residual_prime c o a134
  exact closure_not_le_conjugate_localNormalizer_of_residual p
    (closure_residual_eq_top c.localSetup o hp) (localNormalizer_residual c o a134 hp) hg

/-- 16.2.8(3), for every nontrivial two-subgroup of the marked container. -/
theorem twoSubgroup_normalizer_le [Finite G] {K : GroupClass.{u}}
    (c : CounterexampleSetup K T z L) (o : TwoComponentOrbit T z L u)
    (pair : ComponentPairExhaustion K G)
    (a134 : ComponentPairResidualInput (G := G) K)
    (persist : ComponentPersistence z L u)
    {v : G} (hv : v ∈ conjugate L u) (hv2 : orderOf v = 2)
    {X : Subgroup G} (hX : IsPGroup 2 X) (hne : X ≠ ⊥)
    (hle : X ≤ involutionContainer z L u) :
    normalizer (X : Set G) ≤ localComponentNormalizer z L :=
  normalizer_le_of_even_intersections
    (even_intersection_mem_localNormalizer c o pair a134 persist hv hv2) hX hne hle


/-- The full normalizer of L₀ permutes its two marked components. -/
theorem localNormalizer_orbit [Finite G] {K : GroupClass.{u}}
    (c : CounterexampleSetup K T z L) (o : TwoComponentOrbit T z L u)
    (pair : ComponentPairExhaustion K G) {g : G}
    (hg : g ∈ localComponentNormalizer z L) :
    conjugate L g = L ∨ conjugate L g = conjugate L u := by
  have hH : conjugate (localComponentNormalizer z L) g = localComponentNormalizer z L :=
    (mem_normalizer_iff_conjugate_eq _ _).mp (Subgroup.le_normalizer hg)
  have hLg := (component_in_localNormalizer c.localSetup).map (MulAut.conj g⁻¹)
  change IsComponentIn (conjugate L g) (conjugate (localComponentNormalizer z L) g) at hLg
  rw [hH] at hLg
  exact pair _ (c.global.properK _ c.localNormalizer_ne_top) L (conjugate L u)
    (component_in_localNormalizer c.localSetup)
    (swapped_component_in_localNormalizer c.localSetup o) o.moved.symm
    ⟨(MulAut.conj u⁻¹).subgroupMap L⟩ (conjugate L g) hLg
    ⟨((MulAut.conj g⁻¹).subgroupMap L).symm⟩

private theorem pair_disjoint_of_center_eq_bot
    (h : CentralComponentSetup T z L) (o : TwoComponentOrbit T z L u)
    (hcenter : center L = ⊥) : L ⊓ conjugate L u = ⊥ := by
  apply eq_bot_iff.mpr
  rintro x ⟨hx, hxU⟩
  have hc : (⟨x, hx⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    exact ((commutator_eq_bot_iff_le_centralizer.mp (o.commute h)) y.property x hxU).symm
  rw [hcenter] at hc
  exact congrArg Subtype.val (show (⟨x, hx⟩ : L) = 1 from hc)

private theorem tight_map_equiv [Finite G] {G' : Type*} [Group G'] [Finite G']
    {A : Subgroup G} (hA : IsTightlyEmbedded A) (e : G ≃* G') :
    IsTightlyEmbedded (A.map e.toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · simpa only [card_map_of_injective (f := e.toMonoidHom) e.injective] using hA.1
  · intro g hg
    have hn : e.symm g ∉ normalizer (A : Set G) := by
      intro hn
      apply hg
      rw [← map_equiv_normalizer_eq A e]
      exact ⟨e.symm g, hn, e.apply_symm_apply g⟩
    have heq : (A.map e.toMonoidHom) ⊓
        (A.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom =
        (A ⊓ A.map (MulAut.conj (e.symm g)).toMonoidHom).map e.toMonoidHom := by
      rw [map_inf _ _ e.toMonoidHom e.injective]
      congr 1
      ext x
      simp only [mem_map_equiv, MulAut.conj_symm_apply, map_mul, map_inv]
    rw [heq, card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact hA.2 _ hn

/-- The center-free case of 16.2.8(2). Identifying which models have trivial
center is separate from this finite-group argument. -/
theorem tightlyEmbedded_of_center_eq_bot [Finite G] {K : GroupClass.{u}}
    (c : CounterexampleSetup K T z L) (o : TwoComponentOrbit T z L u)
    (pair : ComponentPairExhaustion K G)
    (a134 : ComponentPairResidualInput (G := G) K)
    (persist : ComponentPersistence z L u)
    {v : G} (hv : v ∈ conjugate L u) (hv2 : orderOf v = 2)
    (hcenter : center L = ⊥) : IsTightlyEmbedded L := by
  have htight : IsTightlyEmbedded (conjugate L u) := by
    refine ⟨even_card_of_involution hv hv2, ?_⟩
    intro g hg
    apply Nat.not_even_iff_odd.mp
    intro heven
    have heven' : Even (Nat.card (conjugate L u ⊓
        conjugate (conjugate L u) g⁻¹ : Subgroup G)) := by
      simpa only [conjugate, inv_inv] using heven
    have hsub : conjugate L u ≤ involutionContainer z L u := le_sup_right
    have hbig := even_card_mono (inf_le_inf hsub (map_mono hsub)) heven'
    have hgH := even_intersection_mem_localNormalizer c o pair a134 persist hv hv2 g⁻¹ hbig
    have horbit := localNormalizer_orbit c o pair
      ((localComponentNormalizer z L).mul_mem (o.swap_mem_localNormalizer c.localSetup) hgH)
    rw [← conjugate_conjugate] at horbit
    rcases horbit with he | he
    · rw [he, inf_comm, pair_disjoint_of_center_eq_bot c.localSetup o hcenter] at heven'
      simp at heven'
    · have hn := (mem_normalizer_iff_conjugate_eq _ _).mpr he
      exact hg (by simpa only [inv_inv] using
        (normalizer (conjugate L u : Set G)).inv_mem hn)
  have hm := tight_map_equiv htight (MulAut.conj u)
  have he : (conjugate L u).map (MulAut.conj u).toMonoidHom = L := by
    simpa only [conjugate, inv_inv] using conjugate_conjugate L u u⁻¹ |>.trans
      (by simp)
  rwa [he] at hm

end CFSG.Quasithin.Chapter16.CounterexampleGeometry

end
