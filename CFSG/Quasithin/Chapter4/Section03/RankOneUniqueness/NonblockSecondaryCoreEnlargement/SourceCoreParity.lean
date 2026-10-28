module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceCoreFixedModule
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameCoreSections

/-!
# Even degrees on actual source core sections

The original cubic fixed module gives the order congruence modulo three,
without strict enlargement. Source: original 4.3.2, pp.618--619.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
open Nonblock.RootCoordinates
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}
namespace RootCoordinates
variable {d : MSData c 2} (m : RootCoordinates d)
  (s : SecondaryActionData c 2) (D : Chapter12.Section02.ChosenModule T L V)
  (X : Subgroup G) (hX : Nat.card X = 3) (hXK : X ≤ (K c).coreCenterIn 2)
  (hfix : Q c ⊓ centralizer (X : Set G) = ⊥)
  (hcomm : ⁅secondary c,X⁆ ≤ (secondary c).pCoreIn 2)
include m s D hX hXK hfix hcomm

/-- The original secondary centralizer acts irreducibly on the cubic-fixed radical, even on additive subgroups. -/
theorem fixedRadical_invariant_subgroup (A : Subgroup G)
    (hA : A ≤ R₂ c ⊓ centralizer (X : Set G))
    (hN : secondary c ⊓ centralizer (X : Set G) ≤ normalizer (A : Set G)) :
    A = ⊥ ∨ A = R₂ c ⊓ centralizer (X : Set G) := by
  let R := R₂ c ⊓ centralizer (X : Set G)
  let e := (SourceActionEndgame.RootCoordinates.fixedRadicalCoordinates D m) s X hX hXK hfix
  let B := A.subgroupOf R
  let E := B.map e.toMonoidHom
  have hinv : ∀ g v, v ∈ E → Matrix.SL2.naturalAction d.field.Carrier g v ∈ E := by
    intro g v hv
    obtain ⟨k,rfl⟩ := (SourceActionEndgame.RootCoordinates.fixedSecondaryLinear_surjective m) X hX hcomm g
    obtain ⟨a,ha,rfl⟩ := hv
    refine ⟨fixedRadicalAction X k a,?_,?_⟩
    · change (k : G) * (a : G) * (k : G)⁻¹ ∈ A
      exact (mem_normalizer_iff.mp (hN k.property) (a : G)).mp ha
    · exact (SourceActionEndgame.RootCoordinates.fixedRadical_action_natural D m) s X hX hXK hfix k a
  rcases Matrix.SL2.naturalAction_irreducible d.field.Carrier E hinv with hb | ht
  · left
    have hb' : B = ⊥ := (map_eq_bot_iff_of_injective B e.injective).mp hb
    apply bot_unique
    intro x hx
    have hh : (⟨x,hA hx⟩ : R) ∈ B := hx
    have he : (⟨x,hA hx⟩ : R) = 1 :=
      mem_bot.mp (show (⟨x,hA hx⟩ : R) ∈ (⊥ : Subgroup R) from hb' ▸ hh)
    exact mem_bot.mpr (congrArg (fun z : R => (z : G)) he)
  · right
    have ht' : B = ⊤ := by
      apply map_injective e.injective
      change E = (⊤ : Subgroup R).map e.toMonoidHom
      have he : (⊤ : Subgroup R).map e.toMonoidHom = ⊤ :=
        (MonoidHom.range_eq_map _).symm.trans (MonoidHom.range_eq_top.mpr e.surjective)
      exact ht.trans he.symm
    apply le_antisymm hA
    intro x hx
    exact ht'.ge (mem_top (⟨x,hx⟩ : R))

/-- Every invariant subgroup meets the cubic-fixed radical trivially or in the whole fixed radical. -/
theorem invariant_cubic_fixed_subgroup (A : Subgroup G) (hA : A ≤ R₂ c)
    (hN : secondary c ⊓ centralizer (X : Set G) ≤ normalizer (A : Set G)) :
    A ⊓ centralizer (X : Set G) = ⊥ ∨
      A ⊓ centralizer (X : Set G) = R₂ c ⊓ centralizer (X : Set G) := by
  apply (SourceActionEndgame.RootCoordinates.fixedRadical_invariant_subgroup m) s D X hX hXK hfix hcomm _ (inf_le_inf_right _ hA)
  exact (le_inf hN (inf_le_right.trans (centralizer (X : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

/-- The only fixed subgroup orders are one and sixteen. -/
theorem invariant_cubic_fixed_card (A : Subgroup G) (hA : A ≤ R₂ c)
    (hN : secondary c ⊓ centralizer (X : Set G) ≤ normalizer (A : Set G)) :
    Nat.card (A ⊓ centralizer (X : Set G) : Subgroup G) = 1 ∨
      Nat.card (A ⊓ centralizer (X : Set G) : Subgroup G) = 16 := by
  rcases (SourceActionEndgame.RootCoordinates.invariant_cubic_fixed_subgroup m) s D X hX hXK hfix hcomm A hA hN with hb | ht
  · exact Or.inl (hb ▸ Subgroup.card_bot)
  · exact Or.inr (ht ▸ (SourceActionEndgame.RootCoordinates.radical_cubic_fixed_card m) D s X hX hXK hfix)

/-- Cubic orbits force the original invariant subgroup order to be one modulo three. -/
theorem invariant_cubic_card_mod_three (A : Subgroup G) (hA : A ≤ R₂ c)
    (hN : secondary c ⊓ centralizer (X : Set G) ≤ normalizer (A : Set G))
    (hXA : X ≤ normalizer (A : Set G)) : Nat.card A % 3 = 1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hp : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by simpa using hX)
  have hc := Subgroup.card_modEq_card_inf_centralizer X A hp hXA
  change Nat.card A % 3 = Nat.card (A ⊓ centralizer (X : Set G) : Subgroup G) % 3 at hc
  rcases (SourceActionEndgame.RootCoordinates.invariant_cubic_fixed_card m) s D X hX hXK hfix hcomm A hA hN with h1 | h16
  · simpa only [h1] using hc
  · simpa only [h16] using hc

/-- The same congruence holds for a section with both original endpoints invariant. -/
theorem invariant_cubic_section_index_mod_three (A B : Subgroup G)
    (hA : A ≤ R₂ c) (hBA : B ≤ A)
    (hNA : secondary c ⊓ centralizer (X : Set G) ≤ normalizer (A : Set G))
    (hNB : secondary c ⊓ centralizer (X : Set G) ≤ normalizer (B : Set G))
    (hXA : X ≤ normalizer (A : Set G)) (hXB : X ≤ normalizer (B : Set G)) :
    B.relIndex A % 3 = 1 := by
  have ha := (SourceActionEndgame.RootCoordinates.invariant_cubic_card_mod_three m) s D X hX hXK hfix hcomm A hA hNA hXA
  have hb := (SourceActionEndgame.RootCoordinates.invariant_cubic_card_mod_three m) s D X hX hXK hfix hcomm B (hBA.trans hA) hNB hXB
  have hc := (B.subgroupOf A).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hBA).toEquiv] at hc
  have hh := congrArg (fun j => j % 3) hc
  change (Nat.card B * B.relIndex A) % 3 = Nat.card A % 3 at hh
  simpa only [Nat.mul_mod,hb,ha,one_mul,Nat.mod_mod] using hh

/-- An original invariant section cannot have odd binary degree. -/
theorem invariant_cubic_section_not_odd_degree (A B : Subgroup G)
    (hA : A ≤ R₂ c) (hBA : B ≤ A)
    (hNA : secondary c ⊓ centralizer (X : Set G) ≤ normalizer (A : Set G))
    (hNB : secondary c ⊓ centralizer (X : Set G) ≤ normalizer (B : Set G))
    (hXA : X ≤ normalizer (A : Set G)) (hXB : X ≤ normalizer (B : Set G))
    {r : ℕ} (hr : Odd r) : B.relIndex A ≠ 2^r := by
  intro he
  have hh := (SourceActionEndgame.RootCoordinates.invariant_cubic_section_index_mod_three m) s D X hX hXK hfix hcomm
    A B hA hBA hNA hNB hXA hXB
  obtain ⟨j,hj⟩ := hr
  have hj' : r = 2*j+1 := by omega
  rw [he,hj',pow_add,pow_mul,Nat.mul_mod,Nat.pow_mod] at hh
  norm_num at hh

/-- Apply parity to sections of the component core normalized by the original cubic extension. -/
theorem component_section_not_odd_degree (A B : Subgroup G)
    (hA : A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype)
    (hBA : B ≤ A)
    (hNA : s.component.map (rootNormalizer c).subtype ⊔ X ≤ normalizer (A : Set G))
    (hNB : s.component.map (rootNormalizer c).subtype ⊔ X ≤ normalizer (B : Set G))
    {r : ℕ} (hr : Odd r) : B.relIndex A ≠ 2^r := by
  have hc : ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype ≤ R₂ c := by
    change (s.component.pCoreIn 2).map (rootNormalizer c).subtype ≤ R₂ c
    rw [map_pCoreIn_of_injective 2 s.component (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective]
    exact s.component_core_le D
  have hK : secondary c ⊓ centralizer (X : Set G) ≤
      s.component.map (rootNormalizer c).subtype ⊔ X :=
    (inf_le_left.trans s.secondary_le).trans le_sup_left
  exact (SourceActionEndgame.RootCoordinates.invariant_cubic_section_not_odd_degree m) s D X hX hXK hfix hcomm A B
    (hA.trans hc) hBA (hK.trans hNA) (hK.trans hNB)
    (le_sup_right.trans hNA) (le_sup_right.trans hNB) hr
end RootCoordinates
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
