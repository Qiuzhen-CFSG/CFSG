module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.OffenderSelection
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.Elementary
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# The terminal Thompson argument in Section 15.3

A maximum elementary subgroup in the action kernel supplies the equality
of maximum orders needed to transfer the minimal-image argument from `S`
to `S₀`. Containment of `J(S₀)` in `C ≤ S₀` then gives `J(S₀) = J(C)`.
Normalization of `S₀` by `T` and of `C` by `L` makes this same nontrivial
two-subgroup invariant under both `T` and `L`. Its normalizer is two-local,
so uniqueness for `Y₊T`, with `Y₊ ≤ L`, forces `L ≤ M`.

The module and offender calculations must construct the maximum subgroup
in the kernel and exclude minimal images inside `S₀`. No such calculation
or component construction is assumed to follow merely from this argument.
In the source, `C = C_I(U_L) = O₂(I)` and `S₀ = S ∩ LO₂(LS)`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the last
paragraph of the proof of Theorem 15.3.25, printed p.1134 (PDF p.1151).
-/

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo

open Subgroup Stellmacher

variable {G : Type*} [Group G] [Finite G]

/-- An intermediate subgroup containing the Thompson subgroup has the same
Thompson subgroup. The proof includes the essential maximum-order comparison. -/
public theorem thompson_eq_of_containment (S C : Subgroup G)
    (hCS : C ≤ S) (hJC : elementaryAbelianMaxJ S ≤ C) :
    elementaryAbelianMaxJ S = elementaryAbelianMaxJ C := by
  have h₁ := elementaryAbelianMaxOrder_le_and_j_le_of_eq C S hCS
  have h₂ := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le S C hJC
  have heq := le_antisymm h₁.1 h₂.1
  exact le_antisymm (h₂.2 heq.symm) (h₁.2 heq)

/-- A maximum elementary subgroup produced by the paired replacement
discharges the maximum-order premise in the minimal-image argument. -/
public theorem thompson_eq_kernel_of_replacement
    {H : Type*} [Group H] [Finite H]
    (S S0 B : Subgroup G) (f : G →* H)
    (hS0 : S0 ≤ S) (hker : f.ker ≤ S0)
    (hB : B ∈ elementaryAbelianMaxSubgroups S) (hBker : B ≤ f.ker)
    (hminimal : ∀ A ∈ minimalNontrivialActionFamily S f,
      ¬ A.map f ≤ S0.map f) :
    elementaryAbelianMaxJ S0 = elementaryAbelianMaxJ f.ker := by
  have hB0 : B ∈ elementaryAbelianMaxSubgroups S0 :=
    ⟨hBker.trans hker, hB.2.1, fun A hA he => hB.2.2 A (hA.trans hS0) he⟩
  have horder : elementaryAbelianMaxOrder S0 = elementaryAbelianMaxOrder S :=
    (elementaryAbelianMaxSubgroups_card_eq S0 B hB0).symm.trans
      (elementaryAbelianMaxSubgroups_card_eq S B hB)
  exact thompson_eq_of_containment S0 f.ker hker
    (thompson_le_kernel_of_minimal_images S S0 f hS0 horder hminimal)

/-- Transfer the local action calculation back to the global group.
Only `I` acts on the module: no action of all of `G` is required. -/
public theorem ambient_thompson_eq_of_local_replacement
    {H : Type*} [Group H] [Finite H]
    (I S S0 C : Subgroup G) (f : I →* H) (B : Subgroup I)
    (hSI : S ≤ I) (hS0 : S0 ≤ S) (hCS0 : C ≤ S0)
    (hker : f.ker.map I.subtype = C)
    (hB : B ∈ elementaryAbelianMaxSubgroups (S.subgroupOf I)) (hBker : B ≤ f.ker)
    (hminimal : ∀ A ∈ minimalNontrivialActionFamily (S.subgroupOf I) f,
      ¬ A.map f ≤ (S0.subgroupOf I).map f) :
    elementaryAbelianMaxJ S0 = elementaryAbelianMaxJ C := by
  have hker0 : f.ker ≤ S0.subgroupOf I := by
    intro x hx
    exact hCS0 (hker ▸ mem_map_of_mem I.subtype hx)
  have h := congrArg (Subgroup.map I.subtype)
    (thompson_eq_kernel_of_replacement (S.subgroupOf I) (S0.subgroupOf I) B f
      (comap_mono hS0) hker0 hB hBker hminimal)
  rwa [← elementaryAbelianMaxJ_map_injective I.subtype I.subtype_injective,
    ← elementaryAbelianMaxJ_map_injective I.subtype I.subtype_injective,
    map_subgroupOf_eq_of_le (hS0.trans hSI), hker] at h

omit [Finite G] in
private theorem normalizer_le_normalizer_thompson (S : Subgroup G) :
    normalizer (S : Set G) ≤ normalizer (elementaryAbelianMaxJ S : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq] at hx ⊢
  change S.map (MulAut.conj x).toMonoidHom = S at hx
  have h := elementaryAbelianMaxJ_map_equiv (MulAut.conj x) S
  rw [hx] at h
  exact h.symm

private theorem thompson_ne_bot_of_elementary (S E : Subgroup G)
    [IsElementaryAbelian 2 E] (hES : E ≤ S) (hE : E ≠ ⊥) :
    elementaryAbelianMaxJ S ≠ ⊥ := by
  obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty S
  intro hJ
  have hA0 : A = ⊥ := le_bot_iff.mp ((le_sSup hA).trans_eq hJ)
  have hcard := hA.2.2 E hES inferInstance
  rw [hA0, card_bot] at hcard
  exact (not_lt_of_ge hcard) ((one_lt_card_iff_ne_bot E).mpr hE)

/-- The two relative normality statements in the last paragraph yield
the contradiction with the earlier uniqueness theorem. Neither the
Thompson subgroup nor either input subgroup is assumed normal in `G`. -/
public theorem outside_contradiction_of_thompson_containment
    (T : Sylow 2 G) (S0 C E L Yplus M : Subgroup G)
    [IsElementaryAbelian 2 E]
    (hS0T : S0 ≤ (T : Subgroup G)) (hCS0 : C ≤ S0)
    (hTS0 : (T : Subgroup G) ≤ normalizer (S0 : Set G))
    (hLC : L ≤ normalizer (C : Set G))
    (hJC : elementaryAbelianMaxJ S0 ≤ C)
    (hES0 : E ≤ S0) (hE : E ≠ ⊥)
    (hYL : Yplus ≤ L) (hLM : ¬ L ≤ M)
    (hunique : Chapter4.UniqueMaximalOvergroup (Yplus ⊔ (T : Subgroup G)) M) :
    False := by
  let J := elementaryAbelianMaxJ S0
  have hJ0 : J ≠ ⊥ := thompson_ne_bot_of_elementary S0 E hES0 hE
  have hJS0 : J ≤ S0 := sSup_le fun _ hA => hA.1
  have hJtwo : IsPGroup 2 J := T.isPGroup'.to_le (hJS0.trans hS0T)
  have heq : J = elementaryAbelianMaxJ C := thompson_eq_of_containment S0 C hCS0 hJC
  have hTJ : (T : Subgroup G) ≤ normalizer (J : Set G) :=
    hTS0.trans (normalizer_le_normalizer_thompson S0)
  have hLJ : L ≤ normalizer (J : Set G) := by
    rw [heq]
    exact hLC.trans (normalizer_le_normalizer_thompson C)
  have hlocal : IsTwoLocal (normalizer (J : Set G)) := ⟨J, hJ0, hJtwo, rfl⟩
  obtain ⟨N, hJN, hN⟩ := Finite.exists_le_maximal hlocal
  have hYN : Yplus ⊔ (T : Subgroup G) ≤ N :=
    sup_le (hYL.trans (hLJ.trans hJN)) (hTJ.trans hJN)
  have hNM := hunique.2.2 N hN hYN
  exact hLM (hNM ▸ hLJ.trans hJN)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
