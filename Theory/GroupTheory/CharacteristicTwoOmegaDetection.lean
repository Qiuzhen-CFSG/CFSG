module

public import Theory.GroupTheory.CharacteristicTwoInheritance
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Stellmacher.OmegaOneCenterMap

/-!
# Normal subgroups detected by the Sylow omega-center

In a finite group of characteristic two, every nontrivial normal subgroup
meets the omega-center of a Sylow two-subgroup. Its two-core is normalized
by the Sylow subgroup; the normal-subgroup theorem for two-groups supplies
a central involution. Characteristic-two inheritance eliminates the case
of trivial two-core. All subgroups retain their original ambient embeddings.

Source: Aschbacher--Smith, 14.1.10, printed p.978; the same argument is used
in 15.3.9, printed p.1123.
-/

public section
open Subgroup Stellmacher
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A normal local subgroup disjoint from the ambient Sylow omega-center is trivial. -/
public theorem normal_eq_bot_of_inf_omegaCenter_eq_bot
    (M N : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hNM : N ≤ M)
    (hn : (N.subgroupOf M).Normal)
    (hc : M ⊓ centralizer (M.pCoreIn 2 : Set G) ≤ M.pCoreIn 2)
    (hdis : N ⊓ omegaOneCenterAmbient (T : Subgroup G) = ⊥) : N = ⊥ := by
  have hMN := (normal_subgroupOf_iff_le_normalizer hNM).mp hn
  have hMQ : M ≤ normalizer (N.pCoreIn 2 : Set G) := by
    apply le_normalizer_iff.mpr
    intro m hm q hq
    obtain ⟨q, hq, rfl⟩ := hq
    let a := N.normalizerMonoidHom ⟨m, hMN hm⟩
    exact ⟨a q, characteristic_iff_le_comap.mp inferInstance a hq, rfl⟩
  have hQM : N.pCoreIn 2 ≤ M := (pCoreIn_le 2 N).trans hNM
  let : ((N.pCoreIn 2).subgroupOf M).Normal :=
    normal_subgroupOf_of_le_normalizer hMQ
  have hQT : N.pCoreIn 2 ≤ (T : Subgroup G) := by
    intro q hq
    have hp : IsPGroup 2 ((N.pCoreIn 2).subgroupOf M) := (isPGroup_pCoreIn 2 N).comap_subtype
    exact (hp.le_sylow_of_normal (T.subtype hTM))
      (show (⟨q, hQM hq⟩ : M) ∈ (N.pCoreIn 2).subgroupOf M from hq)
  have hQbot : N.pCoreIn 2 = ⊥ := by
    by_contra hne
    let U := (N.pCoreIn 2).subgroupOf (T : Subgroup G)
    let : U.Normal := normal_subgroupOf_of_le_normalizer (hTM.trans hMQ)
    have hUne : U ≠ ⊥ := by
      intro hb
      have he := map_subgroupOf_eq_of_le hQT
      change U.map (T : Subgroup G).subtype = N.pCoreIn 2 at he
      rw [hb, Subgroup.map_bot] at he
      exact hne he.symm
    let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
    obtain ⟨A, _, hAU, hAcard, hAZ⟩ :=
      exists_central_subgroup_card_eq_prime_in_normal (p := 2) U
        ((nontrivial_iff_ne_bot U).mpr hUne)
    have hAbot : A = ⊥ := by
      apply le_bot_iff.mp
      intro a ha
      have ha2 : a ^ 2 = 1 := by
        have h := (pow_card_eq_one' : (⟨a, ha⟩ : A) ^ Nat.card A = 1)
        rw [hAcard] at h
        exact congrArg A.subtype h
      have haZ : (a : G) ∈ omegaOneCenterAmbient (T : Subgroup G) := by
        refine ⟨a, ⟨⟨a, hAZ ha⟩, subset_closure ?_, rfl⟩, rfl⟩
        change (⟨a, hAZ ha⟩ : center T) ^ (2 ^ 1) = 1
        apply Subtype.ext
        simpa using ha2
      have han : (a : G) ∈ N := pCoreIn_le 2 N (hAU ha)
      have haone : (a : G) = 1 := by
        have : (a : G) ∈ N ⊓ omegaOneCenterAmbient (T : Subgroup G) := ⟨han, haZ⟩
        simpa only [hdis, mem_bot] using this
      exact mem_bot.mpr (Subtype.ext haone)
    have : Nat.card A = 1 := card_eq_one.mpr hAbot
    omega
  have hself := pCoreIn_selfCentralizing_of_subnormal hc hNM hn.isSubnormal
  rw [hQbot] at hself
  have he : centralizer (↑(⊥ : Subgroup G) : Set G) = ⊤ := by ext x; simp [mem_centralizer_iff]
  rw [he, inf_top_eq] at hself
  exact le_bot_iff.mp hself

/-- Every nontrivial normal subgroup contains an original central involution. -/
theorem exists_omegaCenter_mem_normal
    (M N : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hNM : N ≤ M)
    (hn : (N.subgroupOf M).Normal)
    (hc : M ⊓ centralizer (M.pCoreIn 2 : Set G) ≤ M.pCoreIn 2)
    (hne : N ≠ ⊥) :
    ∃ z : G, z ∈ N ∧ z ∈ omegaOneCenterAmbient (T : Subgroup G) ∧ z ≠ 1 := by
  have hi : N ⊓ omegaOneCenterAmbient (T : Subgroup G) ≠ ⊥ := by
    intro he
    exact hne (normal_eq_bot_of_inf_omegaCenter_eq_bot M N T hTM hNM hn hc he)
  obtain ⟨z, hz, hzne⟩ := ((N ⊓ omegaOneCenterAmbient (T : Subgroup G)).bot_or_exists_ne_one.resolve_left hi)
  exact ⟨z,hz.1,hz.2,hzne⟩

end Theory.GroupTheory
