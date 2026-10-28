module

public import Theory.GroupAction.SylowCentralizerCardinality
public import Theory.GroupTheory.SylowCentralizerCounting
public import Theory.GroupTheory.SylowCentralizerInversion
public import Glauberman.ZStar.CoreFree

/-!
# Transitivity of the Sylow root action

Suzuki's counting argument bounds the number of Sylow two-subgroups by
`|P| + 1`; the general Sylow-action counting criterion then gives root
transitivity. The exceptional unique-involution case is excluded here:
uniqueness makes the involution Sylow-central and weakly closed, so Z*
makes it central in the core-free ambient group. Centralizer containment
would then force the Sylow subgroup to be the whole group.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
Corollary 5.1, p. 92; Suzuki, *Finite groups with nilpotent centralizers*
(1961), Part I, Theorems 2 and 5, pp. 428–434. Combining the
involution/coset counting bound with the exclusion of the unique-involution
case proves root transitivity without a noncommutativity hypothesis.
-/

namespace Glauberman.SuzukiCharacterization

/-- The odd-core-free, nonnormal case has more than one involution in its Sylow subgroup. -/
public theorem exists_distinct_involutions_of_centralizer_le
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (hcore : pPrimeCore 2 G = ⊥)
    (hn : ¬ (P : Subgroup G).Normal)
    (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ (P : Subgroup G)) :
    ∃ t u : P, orderOf t = 2 ∧ orderOf u = 2 ∧ t ≠ u := by
  classical
  have hPne : (P : Subgroup G) ≠ ⊥ := fun he => hn (he ▸ Subgroup.normal_bot)
  let : Nontrivial P := (P : Subgroup G).nontrivial_iff_ne_bot.mpr hPne
  obtain ⟨z, hz⟩ := exists_ne (1 : P)
  let t := z ^ (orderOf z / 2)
  have ht : orderOf t = 2 := orderOf_pow_orderOf_div (orderOf_pos z).ne'
    (P.isPGroup'.dvd_orderOf hz)
  by_contra h
  have huniq (s : P) (hs : orderOf s = 2) : s = t := by
    by_contra hne
    exact h ⟨t, s, ht, hs, Ne.symm hne⟩
  have htG : orderOf (t : G) = 2 := by simpa only [Subgroup.orderOf_coe] using ht
  have htne : (t : G) ≠ 1 := by intro he; simp [he] at htG
  have htI : BenderSuzuki.PFAppendixIII.IsInvolution (t : G) :=
    ⟨htne, by simpa only [htG] using pow_orderOf_eq_one (t : G)⟩
  have htcentral : ∀ s ∈ (P : Subgroup G), s * (t : G) = (t : G) * s := by
    intro s hs
    have he := huniq ((MulAut.conj (⟨s, hs⟩ : P)) t)
      (by rw [MulEquiv.orderOf_eq]; exact ht)
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)
  have htweak : Glauberman.ZStar.IsWeaklyClosedInSylow (t : G) (P : Subgroup G) := by
    refine ⟨t.property, fun g hg => ?_⟩
    have he := huniq ⟨g * (t : G) * g⁻¹, hg⟩ (by
      rw [← Subgroup.orderOf_coe]
      change orderOf ((MulAut.conj g) (t : G)) = 2
      rw [MulEquiv.orderOf_eq, htG])
    exact congrArg Subtype.val he
  have htZ := Glauberman.ZStar.glauberman_zstar_corefree hcore P t htI
    t.property htcentral htweak
  have htop : (P : Subgroup G) = ⊤ := by
    apply top_unique
    intro g _
    exact hcent t t.property htne (Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_center_iff.mp htZ g))
  exact hn (htop ▸ Subgroup.normal_top)

/-- A nonnormal self-centralizing Sylow two-subgroup in an odd-core-free group
acts transitively by conjugation on the other Sylow two-subgroups. -/
public theorem root_transitive_of_centralizer_le
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (hcore : pPrimeCore 2 G = ⊥)
    (hn : ¬ (P : Subgroup G).Normal)
    (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ (P : Subgroup G)) :
    ∀ Q R : Sylow 2 G, Q ≠ P → R ≠ P → ∃ x : P, (x : G) • Q = R := by
  have htwo := exists_distinct_involutions_of_centralizer_le P hcore hn hcent
  exact P.transitive_of_centralizer_le_of_card_le hcent
    (P.card_sylow_le_of_centralizer_le hn hcent htwo)

end Glauberman.SuzukiCharacterization
