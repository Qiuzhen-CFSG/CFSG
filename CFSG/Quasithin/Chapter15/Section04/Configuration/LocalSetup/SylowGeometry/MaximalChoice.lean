module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.Transfer

/-!
# Choosing a largest contrary Sylow subgroup

In the contradiction argument of Aschbacher–Smith 15.4.20 (combined manuscript,
1 March 2004, printed pp.1163–1164), choose an overgroup in `H(I)` maximizing
its Sylow two-order. Extend `T₀` inside that overgroup. Finiteness and Sylow
conjugacy show that the resulting larger `T_I` remains Sylow in every member
of `H(I₀)`, including the normalizer of `O₂(I₀)`.

This supplies the missing maximal-choice justification in the printed argument.
Both occurrences of `T₀` for that normalizer during the contradiction must be
`T_I`. No desired Sylow conclusion for `T₀` is assumed here. Eliminating these
counterexamples using the embedding and pushing-up arguments is separate.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Failure of the universal Sylow conclusion yields a strictly larger Sylow
subgroup whose order is maximal over all of `H(I)`. It stays Sylow in every
`H`-overgroup of its chosen local group. -/
theorem exists_maximal_sylow_counterexample {I T₀ : Subgroup G}
    (hT₀ : IsPGroup 2 T₀) (hT₀I : T₀ ≤ I)
    (hfail : ∃ H ∈ Chapter1.HOver G (I : Set G),
      ¬ ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = T₀) :
    ∃ I₀ ∈ Chapter1.HOver G (I : Set G), ∃ T_I : Subgroup G,
      T₀ < T_I ∧ T_I ≤ I₀ ∧ IsPGroup 2 T_I ∧
      (∃ S : Sylow 2 I₀, (S : Subgroup I₀).map I₀.subtype = T_I) ∧
      (∀ H ∈ Chapter1.HOver G (I : Set G), ∀ S : Sylow 2 H,
        Nat.card ((S : Subgroup H).map H.subtype) ≤ Nat.card T_I) ∧
      (∀ H ∈ Chapter1.HOver G (I₀ : Set G),
        ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = T_I) := by
  classical
  obtain ⟨Hbad, hHbad, hbad⟩ := hfail
  let candidates : Set (Subgroup G × Subgroup G) :=
    {q | q.1 ∈ Chapter1.HOver G (I : Set G) ∧ IsPGroup 2 q.2 ∧ q.2 ≤ q.1}
  have hnonempty : candidates.Nonempty := ⟨(Hbad, T₀), hHbad, hT₀, hT₀I.trans hHbad.2⟩
  obtain ⟨⟨Hmax, Pmax⟩, hmaxmem, hmax⟩ :=
    Set.exists_max_image candidates (fun q => Nat.card q.2) candidates.toFinite hnonempty
  obtain ⟨hHmax, hPmax, hPHmax⟩ := hmaxmem
  have maxSylow (H : Subgroup G) (hH : H ∈ Chapter1.HOver G (I : Set G))
      (S : Sylow 2 H) : Nat.card ((S : Subgroup H).map H.subtype) ≤ Nat.card Pmax :=
    hmax (H, (S : Subgroup H).map H.subtype)
      ⟨hH, S.isPGroup'.map H.subtype, map_subtype_le _⟩
  -- Extend T₀ within the maximizing overgroup, rather than choosing an
  -- arbitrary conjugate of a maximal Sylow subgroup.
  have hT₀Hmax := hT₀I.trans hHmax.2
  have hT₀sub : IsPGroup 2 (T₀.subgroupOf Hmax) :=
    hT₀.comap_of_injective Hmax.subtype Hmax.subtype_injective
  obtain ⟨Smax, hSmax⟩ := hT₀sub.exists_le_sylow
  let T_I : Subgroup G := (Smax : Subgroup Hmax).map Hmax.subtype
  have hT₀TI : T₀ ≤ T_I := by
    intro x hx
    exact ⟨⟨x, hT₀Hmax hx⟩, hSmax hx, rfl⟩
  -- All Sylow subgroups of Hmax have the same order, and one contains Pmax.
  obtain ⟨Sbig, hSbig⟩ :=
    (hPmax.comap_of_injective Hmax.subtype Hmax.subtype_injective).exists_le_sylow
  have hPbig : Pmax ≤ (Sbig : Subgroup Hmax).map Hmax.subtype := by
    intro x hx
    exact ⟨⟨x, hPHmax hx⟩, hSbig hx, rfl⟩
  have hPcard : Nat.card Pmax ≤ Nat.card T_I := by
    calc
      Nat.card Pmax ≤ Nat.card ((Sbig : Subgroup Hmax).map Hmax.subtype) :=
        Nat.card_le_card_of_injective (inclusion hPbig) (inclusion_injective hPbig)
      _ = Nat.card T_I := by
        simp only [T_I, card_map_of_injective Hmax.subtype_injective]
        exact Nat.card_congr (Sbig.equiv Smax).toEquiv
  have hglobal (H : Subgroup G) (hH : H ∈ Chapter1.HOver G (I : Set G))
      (S : Sylow 2 H) : Nat.card ((S : Subgroup H).map H.subtype) ≤ Nat.card T_I :=
    (maxSylow H hH S).trans hPcard
  have hstrict : T₀ < T_I := lt_of_le_of_ne hT₀TI (by
    intro heq
    obtain ⟨Sbad, hSbad⟩ :=
      (hT₀.comap_of_injective Hbad.subtype Hbad.subtype_injective).exists_le_sylow
    have hT₀bad : T₀ ≤ (Sbad : Subgroup Hbad).map Hbad.subtype := by
      intro x hx
      exact ⟨⟨x, (hT₀I.trans hHbad.2) hx⟩, hSbad hx, rfl⟩
    apply hbad
    exact ⟨Sbad, (eq_of_le_of_card_ge hT₀bad (heq ▸ hglobal Hbad hHbad Sbad)).symm⟩)
  refine ⟨Hmax, hHmax, T_I, hstrict, map_subtype_le _, Smax.isPGroup'.map _,
    ⟨Smax, rfl⟩, hglobal, ?_⟩
  intro H hH
  have hTH : T_I ≤ H := (map_subtype_le _).trans hH.2
  obtain ⟨S, hS⟩ :=
    ((Smax.isPGroup'.map Hmax.subtype).comap_of_injective H.subtype H.subtype_injective).exists_le_sylow
  have hTS : T_I ≤ (S : Subgroup H).map H.subtype := by
    intro x hx
    exact ⟨⟨x, hTH hx⟩, hS hx, rfl⟩
  exact ⟨S, (eq_of_le_of_card_ge hTS (hglobal H ⟨hH.1, hHmax.2.trans hH.2⟩ S)).symm⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
