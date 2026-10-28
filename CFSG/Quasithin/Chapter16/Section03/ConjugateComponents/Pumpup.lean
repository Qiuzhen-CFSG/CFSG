module

public import CFSG.Quasithin.Chapter16.Section03.Basic
public import Theory.GroupTheory.CComponent.Basic

/-!
# The mutual-normalization obstruction

Lemma 16.3.13(3) uses an involution in C_G(L) ∩ N_G(Lᵍ). Terminality
makes L a component of its local centralizer in N_G(Lᵍ). The normalizer
is proper, so the standing proper-K hypothesis supplies the K-group input.
The involution case of I.3.1 puts L inside a pair of C-components exchanged
by the involution. Each either equals the normal component Lᵍ or commutes
with it. The first case forces L = Lᵍ by equal orders; the second contradicts
standard form.

Only the indicated consequence of I.3.1 is an explicit source premise.
Its output retains actual C-components; forgetting the additional assertion
that their odd-core quotients are quasisimple is harmless for this argument.
This file does not assert I.3.1. Its proof belongs to the Chapter I owner.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma I.3.1(1), p.414, and Lemma 16.3.13(3), p.1182.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.ConjugateComponents
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The ordinary-component, involution specialization of I.3.1(1),
retaining the actual two conjugate factors and their C-component property. -/
def InvolutionPumpup (K : GroupClass.{u}) (G : Type u) [Group G] : Prop :=
  ∀ N : Subgroup G, IsKGroup K N → ∀ i : N, orderOf i = 2 →
    ∀ B : Subgroup N, IsComponentIn B (centralizer ({i} : Set N)) →
      ∃ J : Subgroup N, J.IsCComponent ∧ B ≤ J ⊔ J.map (MulAut.conj i).toMonoidHom

private theorem component_cComponent_dichotomy {H : Type*} [Group H]
    {A B : Subgroup H} (hA : IsComponent H A) (hB : B.IsCComponent) :
    A = B ∨ ⁅A, B⁆ = ⊥ := by
  rcases hA.subnormal_dichotomy B hB.subnormal with hle | hc
  · left
    let := hA.2
    let : IsSimpleGroup (A ⧸ center A) := IsQuasisimple.simple
    have : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
    exact le_antisymm hle (hB.minimal A hle
      ((nontrivial_iff_ne_bot A).mp inferInstance) inferInstance hA.1)
  · exact Or.inr hc

/-- The argument of 16.3.13(3), conditional only on the stated I.3.1 input. -/
theorem not_le_conjugate_normalizer_of_pumpup {K : GroupClass.{u}}
    (hG : Hypothesis1611 K G) {L : Subgroup G} (hL : IsStandardComponent L)
    (pumpup : InvolutionPumpup K G) (g : G) (hg : g ∉ normalizer (L : Set G))
    (heven : Even (Nat.card ↥(centralizer (L : Set G) ⊓
      normalizer (L.map (MulAut.conj g).toMonoidHom : Set G)))) :
    ¬ L ≤ normalizer (L.map (MulAut.conj g).toMonoidHom : Set G) := by
  let A := L.map (MulAut.conj g).toMonoidHom
  let N := normalizer (A : Set G)
  intro hLN
  change L ≤ N at hLN
  have hcard : Nat.card A = Nat.card L :=
    (Nat.card_congr ((MulAut.conj g).subgroupMap L).toEquiv).symm
  have hAL : A ≠ L := fun he => hg (mem_normalizer_iff_map_conj_eq.mpr he)
  have hqA : IsQuasisimple A := by
    let := hL.quasisimple
    exact IsQuasisimple.of_mulEquiv ((MulAut.conj g).subgroupMap L)
  have hAN : IsComponentIn A N := by
    let := hqA
    exact ⟨A.le_normalizer, (inferInstance : (A.subgroupOf N).Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe A.le_normalizer).symm⟩
  have hNproper : N ≠ ⊤ := by
    intro hN
    let := hG.simple
    let : A.Normal := normalizer_eq_top_iff.mp hN
    rcases (inferInstance : A.Normal).eq_bot_or_eq_top with hb | ht
    · exact hAN.ne_bot hb
    · have hLtop : L = ⊤ := by
        apply eq_of_le_of_card_ge le_top
        rw [Nat.card_congr Subgroup.topEquiv.toEquiv]
        exact le_of_eq (by simpa only [ht, card_top] using hcard)
      apply hg
      rw [hLtop]
      exact (⊤ : Subgroup G).le_normalizer (mem_top g)
  have hNK : IsKGroup K N := hG.properK N hNproper
  obtain ⟨i, hi⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(centralizer (L : Set G) ⊓ N)) 2 (even_iff_two_dvd.mp heven)
  let j : N := ⟨i, i.property.2⟩
  have hj : orderOf j = 2 := (orderOf_coe j).symm.trans ((orderOf_coe i).trans hi)
  have hi2 : orderOf (i : G) = 2 := (orderOf_coe i).trans hi
  have hlocal := hL.terminal i i.property.1 hi2
  have hlocalN : IsComponentIn (L.subgroupOf N) (centralizer ({j} : Set N)) := by
    have hle : L.subgroupOf N ≤ centralizer ({j} : Set N) := by
      intro x hx
      apply mem_centralizer_singleton_iff.mpr
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp (hlocal.1 hx)
    have hnlocal : centralizer ({j} : Set N) ≤ normalizer (L.subgroupOf N : Set N) := by
      rw [← subgroupOf_normalizer_eq hLN]
      intro x hx
      apply hL.involution_centralizer_le i.property.1 hi2
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx)
    have hnormal := (normal_subgroupOf_iff_le_normalizer hle).mpr hnlocal
    let := hlocal.quasisimple
    let : IsQuasisimple (L.subgroupOf N) :=
      IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLN).symm
    exact ⟨hle, hnormal.isSubnormal,
      IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hle).symm⟩
  obtain ⟨J, hJ, hBJ⟩ := pumpup N hNK j hj (L.subgroupOf N) hlocalN
  have hAc : IsComponent N (A.subgroupOf N) := hAN.2
  have hAj : (A.subgroupOf N).map (MulAut.conj j).toMonoidHom = A.subgroupOf N :=
    mem_normalizer_iff_map_conj_eq.mp (by
      rw [normalizer_eq_top]
      exact mem_top _)
  have hJj := hJ.map_equiv (MulAut.conj j)
  have hne (he : A.subgroupOf N = J) : False := by
    have hLA : L ≤ A := by
      have hh : L.subgroupOf N ≤ A.subgroupOf N := by
        rw [← he, hAj, sup_idem] at hBJ
        exact hBJ
      simpa only [map_subgroupOf_eq_of_le hLN, map_subgroupOf_eq_of_le hAN.1]
        using map_mono (f := N.subtype) hh
    apply hAL
    exact (eq_of_le_of_card_ge hLA (le_of_eq
      (Nat.card_congr ((MulAut.conj g).subgroupMap L).toEquiv).symm)).symm
  have hne' (he : A.subgroupOf N = J.map (MulAut.conj j).toMonoidHom) : False := by
    apply hne
    apply (Subgroup.map_injective (f := (MulAut.conj j).toMonoidHom) (MulAut.conj j).injective)
    exact hAj.trans he
  have hc := (component_cComponent_dichotomy hAc hJ).resolve_left hne
  have hc' := (component_cComponent_dichotomy hAc hJj).resolve_left hne'
  have hBA : L.subgroupOf N ≤ centralizer (A.subgroupOf N : Set N) := by
    apply hBJ.trans
    apply sup_le
    · exact commutator_eq_bot_iff_le_centralizer.mp (by rwa [commutator_comm])
    · exact commutator_eq_bot_iff_le_centralizer.mp (by rwa [commutator_comm])
  apply hL.no_commuting_conjugate g
  apply le_centralizer_iff.mpr
  intro x hx y hy
  exact congrArg Subtype.val (hBA (show (⟨x, hLN hx⟩ : N) ∈ L.subgroupOf N from hx)
    ⟨y, hAN.1 hy⟩ hy)

end CFSG.Quasithin.Chapter16.ConjugateComponents
