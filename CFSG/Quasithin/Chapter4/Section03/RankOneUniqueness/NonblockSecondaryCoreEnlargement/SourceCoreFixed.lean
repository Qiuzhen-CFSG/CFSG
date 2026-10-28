module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameLinearFixed
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceCoreBase

/-!
# SourceCoreFixed without strict core enlargement

These are the original core-action arguments with their literal subtype maps,
using only SecondaryActionData. No strict enlargement clause is supplied.
They feed recognition of the full component-core Frattini module.
Source: Aschbacher--Smith, original 4.3.2 and 4.3.11--16, pp.617--619.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
open Nonblock.RootCoordinates
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L}

omit [Finite G] in
private theorem index_join_of_normalizes (A B : Subgroup G)
    (hn : B ≤ normalizer (A : Set G)) : A.relIndex (A ⊔ B) = A.relIndex B := by
  let J := A ⊔ B
  let : (A.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le A.le_normalizer hn)
  have hh := relIndex_sup_left (B.subgroupOf J) (A.subgroupOf J)
  rw [←subgroupOf_sup le_sup_left le_sup_right, relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at hh
  exact hh

namespace RootCoordinates
section General
variable {n : ℕ} {d : MSData c n} (m : RootCoordinates d)
include m

/-- Coverage and the two known inclusions identify the whole radical. -/
theorem radical_eq_core_sup_secondary_core (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (s : SecondaryActionData c n) : R₂ c = Q c ⊔ (secondary c).pCoreIn 2 :=
  le_antisymm (m.radical_coverage hn D s.core_eq)
    (sup_le (core_le_radical c) (Nonblock.RootCoordinates.secondary_core_le_radical D))

/-- The root-plane index is the exact index of Q in R₂. -/
theorem radical_relIndex_core (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (s : SecondaryActionData c n) : (Q c).relIndex (R₂ c) = (2 ^ n) ^ 2 := by
  rw [(SourceActionEndgame.RootCoordinates.radical_eq_core_sup_secondary_core m) hn D s,
    index_join_of_normalizes (Q c) ((secondary c).pCoreIn 2)
      (((pCoreIn_le 2 _).trans secondary_le_original).trans
        ((map_subtype_le _).trans (core_normalized c))),
    s.core_eq_original]
  exact m.secondary_core_relIndex hn

end General
section Cubic
variable {d : MSData c 2} (m : RootCoordinates d)
include m

/-- A source cubic moves precisely Q inside the whole radical. -/
theorem radical_cubic_commutator (D : Chapter12.Section02.ChosenModule T L V)
    (s : SecondaryActionData c 2) (X : Subgroup G)
    (hX : X ≤ (K c).coreCenterIn 2) (hmoved : ⁅Q c,X⁆ = Q c) :
    ⁅R₂ c,X⁆ = Q c := by
  apply le_antisymm
  · rw [s.core_eq_original, commutator_comm]
    apply commutator_le.mpr
    intro x hx r hr
    exact ((mem_coreCenterIn_iff 2 (K c) x).mp (hX hx)).2 r
      (m.radical_le_original (by decide) D s.core_eq hr)
  · rw [←hmoved]
    exact commutator_mono (core_le_radical c) le_rfl

/-- Coprime decomposition gives a complement to Q with trivial intersection. -/
theorem radical_cubic_complement (D : Chapter12.Section02.ChosenModule T L V)
    (s : SecondaryActionData c 2) (X : Subgroup G) (hX3 : Nat.card X = 3)
    (hX : X ≤ (K c).coreCenterIn 2)
    (hfix : Q c ⊓ Subgroup.centralizer (X : Set G) = ⊥) :
    Q c ⊔ (R₂ c ⊓ Subgroup.centralizer (X : Set G)) = R₂ c ∧
      Q c ⊓ (R₂ c ⊓ Subgroup.centralizer (X : Set G)) = ⊥ := by
  have hp := isPGroup_pCoreIn 2 (secondary c ⊔ S c)
  have hcop : Nat.Coprime (Nat.card X) (Nat.card (R₂ c)) := by
    obtain ⟨j,hj⟩ := hp.exists_card_eq
    rw [hX3,hj]
    exact (by decide : Nat.Coprime 3 2).pow_right j
  have hn := coreCenter_normalizes_radical_of_le_original s.core_eq
    (m.radical_le_original (by decide) D s.core_eq) hX
  have hm := d.cubic_core_moved X hX3 (hX.trans (coreCenterIn_le 2 _)) hfix
  let : Group.IsNilpotent (R₂ c) := hp.isNilpotent
  have hd := eq_commutator_sup_centralizer_of_solvable_coprime (R₂ c) X hn
    inferInstance hcop
  rw [(SourceActionEndgame.RootCoordinates.radical_cubic_commutator m) D s X hX hm] at hd
  exact ⟨hd.symm, bot_unique ((inf_le_inf_left _ inf_le_right).trans_eq hfix)⟩

/-- The constructed source cubic fixes exactly sixteen radical elements. -/
theorem radical_cubic_fixed_card (D : Chapter12.Section02.ChosenModule T L V)
    (s : SecondaryActionData c 2) (X : Subgroup G) (hX3 : Nat.card X = 3)
    (hX : X ≤ (K c).coreCenterIn 2)
    (hfix : Q c ⊓ Subgroup.centralizer (X : Set G) = ⊥) :
    Nat.card (R₂ c ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) = 16 := by
  obtain ⟨hs,hi⟩ := (SourceActionEndgame.RootCoordinates.radical_cubic_complement m) D s X hX3 hX hfix
  have hh := index_join_of_normalizes (Q c) (R₂ c ⊓ Subgroup.centralizer (X : Set G))
    ((inf_le_left.trans (radical_le_sylow c)).trans (inf_le_right.trans (core_normalized c)))
  rw [hs, ←inf_relIndex_right (Q c) (R₂ c ⊓ Subgroup.centralizer (X : Set G)),
    hi, relIndex_bot_left] at hh
  exact hh.symm.trans ((SourceActionEndgame.RootCoordinates.radical_relIndex_core m) (by decide) D s)

/-- Every equivariant quotient of an invariant subgroup of the literal radical
has at most sixteen fixed elements under the source cubic. -/
theorem cubic_section_fixed_card_le (D : Chapter12.Section02.ChosenModule T L V)
    (s : SecondaryActionData c 2) (X : Subgroup G) (hX3 : Nat.card X = 3)
    (hX : X ≤ (K c).coreCenterIn 2)
    (hfix : Q c ⊓ Subgroup.centralizer (X : Set G) = ⊥)
    (A : Subgroup G) (hAR : A ≤ R₂ c) [Normalizes X A]
    {M : Type*} [Group M] [MulDistribMulAction X M]
    (f : A →* M) (hf : Function.Surjective f)
    (he : ∀ (x : X) (a : A), f (x • a) = x • f a) :
    Nat.card (FixedPoints.subgroup X M) ≤ 16 := by
  have hXp : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by simpa using hX3)
  have hAp : IsPGroup 2 A := (isPGroup_pCoreIn 2 (secondary c ⊔ S c)).to_le hAR
  have hk : ¬ 3 ∣ Nat.card f.ker := by
    obtain ⟨j,hj⟩ := (hAp.to_subgroup f.ker).exists_card_eq
    rw [hj]
    exact Nat.prime_three.coprime_iff_not_dvd.mp
      ((by decide : Nat.Coprime 3 2).pow_right j)
  have hsur := FixedPoints.mapHom_surjective_of_coprime_kernel hXp f hf he hk
  let i : FixedPoints.subgroup X A → (R₂ c ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) :=
    fun a => ⟨a.val, hAR a.val.property, by
      intro x hx
      have hh := congrArg Subtype.val (a.property (⟨x,hx⟩ : X))
      change x * (a.val : G) * x⁻¹ = a.val at hh
      exact mul_inv_eq_iff_eq_mul.mp hh⟩
  have hi : Function.Injective i := by
    intro a b hh
    exact Subtype.ext (Subtype.ext
      (congrArg (fun z : (R₂ c ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) => (z : G)) hh))
  exact (Nat.card_le_card_of_surjective _ hsur).trans
    ((Nat.card_le_card_of_injective i hi).trans_eq ((SourceActionEndgame.RootCoordinates.radical_cubic_fixed_card m) D s X hX3 hX hfix))

/-- Literal application to every invariant section of the secondary component's
mapped two-core, preserving both original subtype inclusions. -/
theorem cubic_component_section_fixed_card_le (D : Chapter12.Section02.ChosenModule T L V)
    (s : SecondaryActionData c 2) (X : Subgroup G) (hX3 : Nat.card X = 3)
    (hX : X ≤ (K c).coreCenterIn 2)
    (hfix : Q c ⊓ Subgroup.centralizer (X : Set G) = ⊥)
    (A : Subgroup G)
    (hA : A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype)
    [Normalizes X A] {M : Type*} [Group M] [MulDistribMulAction X M]
    (f : A →* M) (hf : Function.Surjective f)
    (he : ∀ (x : X) (a : A), f (x • a) = x • f a) :
    Nat.card (FixedPoints.subgroup X M) ≤ 16 := by
  have hcore : ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype ≤ R₂ c := by
    change (s.component.pCoreIn 2).map (rootNormalizer c).subtype ≤ R₂ c
    rw [map_pCoreIn_of_injective 2 s.component (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective]
    exact s.component_core_le D
  exact (SourceActionEndgame.RootCoordinates.cubic_section_fixed_card_le m) D s X hX3 hX hfix A (hA.trans hcore) f hf he

end Cubic
end RootCoordinates
/-- The source scalar cubic has an exact fixed subgroup of order sixteen in
R₂, and its radical commutator is exactly Q. No whole-radical movement is used. -/
theorem MSData.exists_source_cubic_fixed_radical (d : MSData c 2)
    (m : RootCoordinates d) (D : Chapter12.Section02.ChosenModule T L V)
    (s : SecondaryActionData c 2) :
    ∃ X : Subgroup G, Nat.card X = 3 ∧ X ≤ (K c).coreCenterIn 2 ∧
      X ≤ rootNormalizer c ∧ X ⊓ Subgroup.centralizer (root c : Set G) = ⊥ ∧
      Q c ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧
      ⁅secondary c,X⁆ ≤ (secondary c).pCoreIn 2 ∧ ⁅Q c,X⁆ = Q c ∧
      ⁅R₂ c,X⁆ = Q c ∧
      Q c ⊔ (R₂ c ⊓ Subgroup.centralizer (X : Set G)) = R₂ c ∧
      Nat.card (R₂ c ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) = 16 := by
  obtain ⟨X,hX,hXK,hr,hfix,hfaith,_,_,hcomm,hmoved,_⟩ := d.exists_source_cubic_root D
  exact ⟨X,hX,hXK,hr,hfaith,hfix,hcomm,hmoved,
    (SourceActionEndgame.RootCoordinates.radical_cubic_commutator m) D s X hXK hmoved,
    ((SourceActionEndgame.RootCoordinates.radical_cubic_complement m) D s X hX hXK hfix).1,
    (SourceActionEndgame.RootCoordinates.radical_cubic_fixed_card m) D s X hX hXK hfix⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
