module

public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
public import Theory.GroupTheory.SylowCentralizerObstruction
public import Theory.GroupTheory.SemidihedralStandardModel
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# The standard-component problem in §16.3

The terminal assertion is that L remains a component in the centralizer of
every involution centralizing L. Its failure, after conjugacy in C_G(L), gives
the involution t in T_C used in Lemmas 16.3.8–12. Relative normality in C_G(z)
is the earlier Theorem 16.2.4, not normality in G.

The standardness criterion below proves the group-theoretic implication of
16.3.2. Even order of L follows from E1; the exclusion in 16.3.1 stays explicit.
Theorem 16.3.7 must still discharge terminality and the exclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.1177–1182. The proof of Theorem 16.3.7 and Lemma 16.3.13 are on p.1182,
beyond the initial page range of the section task.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]
variable {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- The actual contrary involution used to prove 16.3.7, with the
relative normality output required from 16.2.4 kept explicit. -/
structure TerminalCounterexample (T : Sylow 2 G) (z : G) (L : Subgroup G) (t : G) : Prop where
  localSetup : CentralComponentSetup T z L
  normal : (L.subgroupOf (involutionCentralizer z)).Normal
  involution : orderOf t = 2
  mem_commutingSylow : t ∈ commutingSylow T L
  not_component : ¬ IsCentralizerComponent t L

/-- The literal dihedral/semidihedral conclusion of 16.3.8, with the
small cases excluded by the model parameters. This is an output to construct,
not an extra assumption of Theorem 16.3.7. Mathlib's dihedral parameter is
the rotation order, half the group order. -/
structure NonterminalCentralizerShape (T : Sylow 2 G) (z : G)
    (L : Subgroup G) (t : G) : Prop where
  model :
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (commutingSylow T L ≃* DihedralGroup (2 ^ n))) ∨
    (∃ (n : ℕ) (hn : 4 ≤ n),
      Nonempty (commutingSylow T L ≃* Semidihedral.StandardModel n hn))
  centralizer_eq : commutingSylow T L ⊓ involutionCentralizer t = zpowers z ⊔ zpowers t

/-- The chosen central involution centralizes the component. -/
theorem CentralComponentSetup.involution_mem_componentCentralizer
    (h : CentralComponentSetup T z L) : z ∈ centralizer (L : Set G) := by
  intro x hx
  exact mem_centralizer_singleton_iff.mp (h.component.1 hx)

/-- In particular the centralizer has even order, without any model facts. -/
theorem CentralComponentSetup.componentCentralizer_even [Finite G]
    (h : CentralComponentSetup T z L) : Even (Nat.card (centralizer (L : Set G))) := by
  let a : centralizer (L : Set G) := ⟨z, h.involution_mem_componentCentralizer⟩
  apply even_iff_two_dvd.mpr
  have ha : orderOf a = 2 := (orderOf_coe a).symm.trans h.involution
  exact ha ▸ orderOf_dvd_natCard a

/-- Relative normality from 16.2.4 makes T_C a Sylow two-subgroup of C_G(L).
It is represented intrinsically by the actual intersection with T. -/
theorem CentralComponentSetup.exists_commutingSylow_of_normal [Finite G]
    (h : CentralComponentSetup T z L)
    (hn : (L.subgroupOf (involutionCentralizer z)).Normal) :
    ∃ S : Sylow 2 (centralizer (L : Set G)),
      (S : Subgroup (centralizer (L : Set G))) =
        (T : Subgroup G).subgroupOf (centralizer (L : Set G)) := by
  let N := normalizer (L : Set G)
  let C := centralizer (L : Set G)
  have hTN : (T : Subgroup G) ≤ N := h.sylow_le_normalizer_of_normal hn
  have hCN : C ≤ N := centralizer_le_normalizer _
  obtain ⟨S, hS⟩ := (T.subtype hTN).exists_subgroupOf_eq_of_normal (C.subgroupOf N)
  let e := subgroupOfEquivOfLe hCN
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (S : Subgroup _).map e.toMonoidHom = _
  rw [hS]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨⟨x, hCN x.property⟩, x.property⟩, hx, rfl⟩

/-- Condition E1 already forces every component to have even order. Its
odd core is trivial by subnormality; an odd-order group would be its own
odd core. Thus this input to 16.3.2 needs no model classification. -/
theorem HasEvenTypeCentralizers.component_even [Finite G]
    (he : HasEvenTypeCentralizers G) {i : G} (hi : orderOf i = 2)
    (hL : IsCentralizerComponent i L) : Even (Nat.card L) := by
  have hcore := Subgroup.IsSubnormal.pPrimeCore_eq_bot (he.oddCore i hi)
    (L.subgroupOf (involutionCentralizer i)) hL.2.1
  have hmap := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hL.1)
  have hLcore : pPrimeCore 2 L = ⊥ := by
    simpa only [hcore, Subgroup.map_bot] using hmap.symm
  let := hL.quasisimple
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  have : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  by_contra hnot
  have hc : Nat.Coprime 2 (Nat.card (⊤ : Subgroup L)) := by
    simpa only [Nat.card_congr Subgroup.topEquiv.toEquiv] using
      (Nat.coprime_two_left.mpr (Nat.not_even_iff_odd.mp hnot))
  exact top_ne_bot ((pPrimeCore_eq_bot_iff.mp hLcore) ⊤ inferInstance hc)

/-- The genuine conditional implication in 16.3.2. The premises correspond
to terminality, E1/E2, and the second assertion of 16.3.1. -/
theorem CentralComponentSetup.standard_of_terminal_of_exclusion [Finite G]
    (h : CentralComponentSetup T z L) (hterminal : IsTerminalComponent L)
    (hevenType : HasEvenTypeCentralizers G)
    (hexclude : ∀ g : G, ¬ IsComponentIn (L.map (MulAut.conj g).toMonoidHom)
      (centralizer (L : Set G))) : IsStandardComponent L :=
  hterminal.standard_of_no_conjugate_component
    (hevenType.component_even h.involution h.component) h.componentCentralizer_even hexclude

/-- Before Sylow conjugacy, a failure of standardness gives a contrary
involution in the full centralizer. No classification premise is hidden. -/
theorem CentralComponentSetup.exists_nonterminal_involution [Finite G]
    (h : CentralComponentSetup T z L) (hevenType : HasEvenTypeCentralizers G)
    (hexclude : ∀ g : G, ¬ IsComponentIn (L.map (MulAut.conj g).toMonoidHom)
      (centralizer (L : Set G))) (hnot : ¬ IsStandardComponent L) :
    ∃ t : G, t ∈ centralizer (L : Set G) ∧ orderOf t = 2 ∧
      ¬ IsCentralizerComponent t L := by
  by_contra! hn
  apply hnot
  exact h.standard_of_terminal_of_exclusion (fun t ht ht2 => hn t ht ht2) hevenType hexclude

/-- The contrary involution can be chosen in the actual T_C, by conjugacy
inside C_G(L). This is the reduction preceding 16.3.8, and retains the
previous normality and conjugate-exclusion obligations explicitly. -/
theorem CentralComponentSetup.exists_terminalCounterexample [Finite G]
    (h : CentralComponentSetup T z L)
    (hn : (L.subgroupOf (involutionCentralizer z)).Normal)
    (hevenType : HasEvenTypeCentralizers G)
    (hexclude : ∀ g : G, ¬ IsComponentIn (L.map (MulAut.conj g).toMonoidHom)
      (centralizer (L : Set G))) (hnot : ¬ IsStandardComponent L) :
    ∃ t : G, TerminalCounterexample T z L t := by
  obtain ⟨t, htC, ht2, hnotcomp⟩ := h.exists_nonterminal_involution hevenType hexclude hnot
  let C := centralizer (L : Set G)
  let a : C := ⟨t, htC⟩
  have ha : orderOf a = 2 := (orderOf_coe a).symm.trans ht2
  have hp : IsPGroup 2 (zpowers a) := by
    apply IsPGroup.of_card (n := 1)
    simpa only [Nat.card_zpowers, pow_one] using ha
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  obtain ⟨S, hS⟩ := h.exists_commutingSylow_of_normal hn
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C R S
  let e : G ≃* G := MulAut.conj (c : G)
  have hSC : e t ∈ commutingSylow T L := by
    have hm : c * a * c⁻¹ ∈ (S : Subgroup C) := by
      rw [← hc]
      exact mem_map_of_mem (MulAut.conj c).toMonoidHom (hR (mem_zpowers a))
    have hmT : e t ∈ (T : Subgroup G) := by
      rw [hS] at hm
      exact hm
    exact ⟨hmT, (c * a * c⁻¹).property⟩
  refine ⟨e t, ⟨h, hn, (e.orderOf_eq t).trans ht2, hSC, ?_⟩⟩
  intro hcomp
  have he : e.symm.toMonoidHom = (MulAut.conj (c : G)⁻¹).toMonoidHom := by
    ext x
    apply e.injective
    simp [e, MulAut.conj_apply, mul_assoc]
  have hback : L.map e.symm.toMonoidHom = L := by
    rw [he]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (L : Set G)).inv_mem (centralizer_le_normalizer _ c.property))
  have hm := (show IsComponentIn L (involutionCentralizer (e t)) from hcomp).map e.symm
  rw [hback, involutionCentralizer, map_centralizer_equiv,
    Set.image_singleton, e.symm_apply_apply] at hm
  exact hnotcomp hm

/-- The contrary involution is different from the original central one. -/
theorem TerminalCounterexample.ne_original (h : TerminalCounterexample T z L t) : t ≠ z := by
  rintro rfl
  exact h.not_component h.localSetup.component

/-- Every normalized setup arising after 16.2.4 has T inside N_G(L). -/
theorem TerminalCounterexample.sylow_le_normalizer (h : TerminalCounterexample T z L t) :
    (T : Subgroup G) ≤ normalizer (L : Set G) :=
  h.localSetup.sylow_le_normalizer_of_normal h.normal

end CFSG.Quasithin.Chapter16
