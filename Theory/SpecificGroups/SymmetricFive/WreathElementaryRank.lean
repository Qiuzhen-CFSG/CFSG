module
public import Theory.GroupTheory.WreathTwoElementaryRank
public import Theory.Mathieu.M22.ValueBoundParabolics.SmallQuotients

/-!
# Elementary actors in the symmetric-five wreath group

The sign map to the two-element wreath group detects the inner A₅² base.
Its two-rank is two, so an elementary actor of larger order meets the inner
base nontrivially. An elementary actor of order sixteen lies in the base,
is the full product of its order-four projections, and has a nontrivial
even involution independently supported in each coordinate.

These are the marked group inputs for the moved A₅-pair normalizer estimates
in Aschbacher–Smith D.3.5, printed pp.195–196.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymmetricFive.WreathElementaryRank
open WreathTwoElementaryRank
abbrev Sym := Equiv.Perm (Fin 5)
abbrev Wreath := W Sym
abbrev Alt := alternatingGroup (Fin 5)

def outerHom : Wreath →* W ℤˣ where
  toFun w := ⟨fun i => Equiv.Perm.sign (w.left i), w.right⟩
  map_one' := by
    apply RegularWreathProduct.ext
    · funext i; simp
    · rfl
  map_mul' a b := by
    apply RegularWreathProduct.ext
    · funext i; simp
    · rfl

theorem outerHom_eq_one (w : Wreath) : outerHom w = 1 ↔
    w.right = 1 ∧ w.left 1 ∈ Alt ∧ w.left turn ∈ Alt := by
  constructor
  · intro h
    refine ⟨congrArg RegularWreathProduct.right h, ?_, ?_⟩
    · exact congrArg (fun x : W ℤˣ => x.left 1) h
    · exact congrArg (fun x : W ℤˣ => x.left turn) h
  · rintro ⟨hr,h1,h2⟩
    apply RegularWreathProduct.ext
    · funext i
      rcases index_cases i with rfl | rfl
      · exact h1
      · exact h2
    · exact hr

theorem rank_le_four : primeRank 2 Wreath ≤ 4 := by
  exact WreathTwoElementaryRank.rank_bound
    Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two (by decide)

theorem elementary_card_le_sixteen (E : Subgroup Wreath) (hE : IsElementaryAbelian 2 E) :
    Nat.card E ≤ 16 :=
  (primeRank_le_iff_elementary_card_le Wreath).mp rank_le_four E hE

theorem large_elementary_le_base (E : Subgroup Wreath) (hE : IsElementaryAbelian 2 E)
    (hc : 8 < Nat.card E) : E ≤ base Sym := by
  by_contra hn
  have hb := elementary_card_le_of_not_le_base E hE hn
    Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two
  exact (Nat.not_lt_of_ge hb) hc

private theorem units_rank_le_one : primeRank 2 ℤˣ ≤ 1 := by
  apply (primeRank_le_iff_elementary_card_le ℤˣ).mpr
  intro E _
  exact (card_le_card_group E).trans_eq (by simp [Nat.card_eq_fintype_card])

theorem outer_rank_le_two : primeRank 2 (W ℤˣ) ≤ 2 :=
  WreathTwoElementaryRank.rank_bound units_rank_le_one (by decide)

/-- An elementary actor of order above four contains a nonidentity inner
actor; all three literal coordinates of that actor are supplied. -/
theorem exists_nontrivial_inner (E : Subgroup Wreath) (hE : IsElementaryAbelian 2 E)
    (hc : 4 < Nat.card E) :
    ∃ x ∈ E, x ≠ 1 ∧ x.right = 1 ∧ x.left 1 ∈ Alt ∧ x.left turn ∈ Alt := by
  by_contra hn
  have hf : Function.Injective (outerHom.comp E.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    by_contra hne
    have hxne : (x : Wreath) ≠ 1 := fun he => hne (Subtype.ext he)
    exact hn ⟨x,x.property,hxne,(outerHom_eq_one x).mp hx⟩
  have hr := primeRank_le_of_injective 2 (outerHom.comp E.subtype) hf
  have hr' := hr.trans outer_rank_le_two
  let := hE
  have ht : IsElementaryAbelian 2 (⊤ : Subgroup E) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup E).subtype Subtype.val_injective
  have hb := (primeRank_le_iff_elementary_card_le E).mp hr' ⊤ ht
  simp only [card_top] at hb
  norm_num at hb
  omega

private theorem exists_even_ne_one (E : Subgroup Sym) (hc : 2 < Nat.card E) :
    ∃ x ∈ E, x ≠ 1 ∧ x ∈ Alt := by
  by_contra hn
  have hf : Function.Injective ((Equiv.Perm.sign : Sym →* ℤˣ).comp E.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    by_contra hne
    exact hn ⟨x,x.property,(fun he => hne (Subtype.ext he)),hx⟩
  have hh := Nat.card_le_card_of_injective _ hf
  have hu : Nat.card ℤˣ = 2 := by simp [Nat.card_eq_fintype_card]
  omega

/-- Every elementary actor of maximum rank contains nonidentity inner
involutions independently supported on the two specified coordinates. -/
theorem exists_independent_inner (E : Subgroup Wreath) (hE : IsElementaryAbelian 2 E)
    (hc : 16 ≤ Nat.card E) :
    ∃ a b : Alt, a ≠ 1 ∧ b ≠ 1 ∧ a^2=1 ∧ b^2=1 ∧
      baseHom (a.val,1) ∈ E ∧ baseHom (1,b.val) ∈ E := by
  have hbase := large_elementary_le_base E hE (by omega)
  let F := E.comap (baseHom : Sym × Sym →* Wreath)
  have hm : F.map baseHom = E := by
    apply map_comap_eq_self
    intro w hw
    exact ⟨baseEquiv.symm ⟨w,hbase hw⟩, (baseEquiv_coe _).symm.trans (congrArg Subtype.val
      (baseEquiv.apply_symm_apply ⟨w,hbase hw⟩))⟩
  have hFc : Nat.card F = Nat.card E := by
    rw [←hm,card_map_of_injective baseHom_injective]
  let : IsElementaryAbelian 2 F := by
    let f : F →* E := baseHom.restrict (fun _ hx => hx)
    exact IsElementaryAbelian.of_injective f (fun x y h =>
      Subtype.ext (baseHom_injective (congrArg Subtype.val h)))
  let A := F.map (MonoidHom.fst Sym Sym)
  let B := F.map (MonoidHom.snd Sym Sym)
  have hA : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have ha : Nat.card A ≤ 4 := (primeRank_le_iff_elementary_card_le Sym).mp
    Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two A hA
  have hb : Nat.card B ≤ 4 := (primeRank_le_iff_elementary_card_le Sym).mp
    Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two B hB
  have hF : F ≤ A.prod B := by
    intro x hx
    exact ⟨⟨x,hx,rfl⟩,⟨x,hx,rfl⟩⟩
  have hprod : Nat.card (A.prod B) = Nat.card A * Nat.card B := by
    rw [Nat.card_congr (Subgroup.prodEquiv A B).toEquiv, Nat.card_prod]
  have hle := card_le_of_le hF
  have hac : Nat.card A = 4 := by nlinarith
  have hbc : Nat.card B = 4 := by nlinarith
  have heq : F = A.prod B := eq_of_le_of_card_ge hF (by rw [hprod,hac,hbc]; omega)
  obtain ⟨a,haA,hane,haAlt⟩ := exists_even_ne_one A (by omega)
  obtain ⟨b,hbB,hbne,hbAlt⟩ := exists_even_ne_one B (by omega)
  have haF : (a,1) ∈ F := heq ▸ ⟨haA,B.one_mem⟩
  have hbF : (1,b) ∈ F := heq ▸ ⟨A.one_mem,hbB⟩
  refine ⟨⟨a,haAlt⟩,⟨b,hbAlt⟩,(fun h => hane (congrArg Subtype.val h)),
    (fun h => hbne (congrArg Subtype.val h)),?_,?_,haF,hbF⟩
  · apply Subtype.ext
    exact congrArg Prod.fst (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ haF)
  · apply Subtype.ext
    exact congrArg Prod.snd (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hbF)
end Theory.SpecificGroups.SymmetricFive.WreathElementaryRank
