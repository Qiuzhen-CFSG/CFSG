module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.NaturalAction
public import Theory.GroupTheory.CharacteristicTwoInheritance
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Faithfulness of the residual action in 15.3.9

In a finite group of characteristic two, a normal subgroup disjoint from
`Ω₁(Z(T))` is trivial. Its two-core is normal in the Sylow subgroup, so a
nontrivial core would contain a central subgroup of order two. Inheritance
of characteristic two then eliminates the whole normal subgroup.

Consequently a centerless normal `Y` containing `Ω₁(Z(T))` has trivial
centralizer in `M`. This proves the faithfulness step of the wreath
recognition without assuming a faithful automorphism action. Separately,
characteristic-two inheritance gives `C_Y(V) = V` when `V = O₂(Y)`.
Recognizing `Y` and computing its full automorphism group remain separate
inputs to the final source assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 15.3.9, printed p.1123 (PDF p.1140).
-/

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.WreathRecognition
variable {G : Type*} [Group G] [Finite G]

/-- Characteristic two and the Sylow omega-center detect normal subgroups. -/
public theorem normal_eq_bot_of_inf_centralInvolutions_eq_bot
    (M N : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hNM : N ≤ M)
    (hn : (N.subgroupOf M).Normal)
    (hc : M ⊓ centralizer (M.pCoreIn 2 : Set G) ≤ M.pCoreIn 2)
    (hdis : N ⊓ centralInvolutions T = ⊥) : N = ⊥ := by
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
      have haZ : (a : G) ∈ centralInvolutions T := by
        refine ⟨a, ⟨⟨a, hAZ ha⟩, subset_closure ?_, rfl⟩, rfl⟩
        change (⟨a, hAZ ha⟩ : center T) ^ (2 ^ 1) = 1
        apply Subtype.ext
        simpa using ha2
      have han : (a : G) ∈ N := pCoreIn_le 2 N (hAU ha)
      have haone : (a : G) = 1 := by
        have : (a : G) ∈ N ⊓ centralInvolutions T := ⟨han, haZ⟩
        simpa only [hdis, mem_bot] using this
      exact mem_bot.mpr (Subtype.ext haone)
    have : Nat.card A = 1 := card_eq_one.mpr hAbot
    omega
  have hself := pCoreIn_selfCentralizing_of_subnormal hc hNM hn.isSubnormal
  rw [hQbot] at hself
  have he : centralizer (↑(⊥ : Subgroup G) : Set G) = ⊤ := by ext x; simp [mem_centralizer_iff]
  rw [he, inf_top_eq] at hself
  exact le_bot_iff.mp hself

/-- The actual centralizer in the local overgroup vanishes. -/
public theorem centralizer_eq_bot_of_center_eq_bot
    (M Y : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hYM : Y ≤ M)
    (hn : (Y.subgroupOf M).Normal)
    (hc : M ⊓ centralizer (M.pCoreIn 2 : Set G) ≤ M.pCoreIn 2)
    (hZY : centralInvolutions T ≤ Y) (hz : center Y = ⊥) :
    M ⊓ centralizer (Y : Set G) = ⊥ := by
  have hMN := (normal_subgroupOf_iff_le_normalizer hYM).mp hn
  have hNC : normalizer (Y : Set G) ≤ normalizer (centralizer (Y : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp inferInstance
  have hCn : ((M ⊓ centralizer (Y : Set G)).subgroupOf M).Normal := by
    have he : (M ⊓ centralizer (Y : Set G)).subgroupOf M =
        (centralizer (Y : Set G)).subgroupOf M := by
      ext x
      simp only [mem_subgroupOf, mem_inf, x.property, true_and]
    rw [he]
    exact normal_subgroupOf_of_le_normalizer (hMN.trans hNC)
  apply normal_eq_bot_of_inf_centralInvolutions_eq_bot M _ T hTM inf_le_left hCn hc
  apply le_bot_iff.mp
  rintro x ⟨hx, hxZ⟩
  have hy : (⟨x, hZY hxZ⟩ : Y) ∈ center Y := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (hx.2 y y.property)
  rw [hz, mem_bot] at hy
  exact mem_bot.mpr (congrArg Y.subtype hy)

/-- The equality branch has no additional kernel inside the residual. -/
public theorem module_centralizer_eq_of_core_eq
    (M Y V : Subgroup G) (hYM : Y ≤ M)
    (hn : (Y.subgroupOf M).Normal) (d : NaturalOrthogonalAction M V)
    (hc : M ⊓ centralizer (M.pCoreIn 2 : Set G) ≤ M.pCoreIn 2)
    (hV : V = Y.pCoreIn 2) : Y ⊓ centralizer (V : Set G) = V := by
  have hself := pCoreIn_selfCentralizing_of_subnormal hc hYM hn.isSubnormal
  rw [← hV] at hself
  refine le_antisymm hself (le_inf ?_ ?_)
  · rw [hV]
    exact pCoreIn_le 2 Y
  · intro v hv w hw
    have he : (⟨w, hw⟩ : V) * ⟨v, hv⟩ = ⟨v, hv⟩ * ⟨w, hw⟩ :=
      d.coordinates.injective (by simp only [map_mul, mul_comm])
    exact congrArg V.subtype he

end CFSG.Quasithin.Chapter15.Section03.WreathRecognition
