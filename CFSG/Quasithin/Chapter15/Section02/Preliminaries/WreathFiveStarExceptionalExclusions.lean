module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveCentralTransport
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveG2Exclusion
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveSymplecticExclusion
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveLinearFiveExclusion
public import Theory.AtlasPort.LinearGroups.G2.Simplicity
public import Theory.SpecificGroups.SymplecticFour.SimpleQuotients
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# Exceptional star-model exclusions in original 15.2.4

A surjection from the source component with solvable, five-free kernel retains
both its local A₅ and its normalized solvable subgroup of order divisible by five.
For G₂ and Sp₄, proper Sylow overgroups place the local A₅ in a parabolic, whose
rank-one quotient bounds the field degree. The small Borel order then excludes
the normalized five-section. The small derived G₂ model is five-free, and the
binary SL₅ model has no solvable Sylow overgroup of order divisible by five.

These statements use the actual star quotient map; they require no identification
of that quotient with the quotient by the source two-core. They discharge the
exceptional rows of the C.2.7/B.5 catalogue in the source comparison.

Source: Aschbacher--Smith, original 15.2.4, printed pp.1106--1107.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterB.QuasisimpleSource
namespace WreathFiveStar

private theorem simple_twoCore_eq_bot
    {D : Type*} [Group D] [Finite D] [IsSimpleGroup D] [Group.IsPerfect D] :
    pCore 2 D = ⊥ := by
  rcases (inferInstance : (pCore 2 D).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · let : Group.IsNilpotent (pCore 2 D) := pCore_isPGroup.isNilpotent
    let : Group.IsSolvable (⊤ : Subgroup D) := ht ▸ inferInstance
    have hs : Group.IsSolvable D := Group.isSolvable_of_surjective
      (f := (topEquiv (G := D)).toMonoidHom) (topEquiv (G := D)).surjective
    exact (Group.IsPerfect.not_isSolvable D hs).elim

private theorem g2_card_not_dvd_sixty (F : BinaryField) :
    ¬ Nat.card (Atlas.G2.Model F.Carrier) ∣ 60 := by
  intro h
  have hh := (Atlas.G2.unipotent (K := F.Carrier)).card_subgroup_dvd_card.trans h
  rw [Atlas.G2.card_unipotent,F.card_eq,←pow_mul] at hh
  have h3 : 3 ≤ F.degree * 6 := by have := F.degree_pos; omega
  have hb : 8 ∣ 60 := (Nat.pow_dvd_pow 2 h3).trans hh
  norm_num at hb

private theorem symplectic_card_not_dvd_sixty (F : BinaryField) :
    ¬ Nat.card (Theory.SpecificGroups.SymplecticFour.Sp F.Carrier) ∣ 60 := by
  intro h
  have hh := (Theory.SpecificGroups.SymplecticFour.unipotent (F := F.Carrier)).card_subgroup_dvd_card.trans h
  rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,F.card_eq,←pow_mul] at hh
  have h3 : 3 ≤ F.degree * 4 := by have := F.degree_pos; omega
  have hb : 8 ∣ 60 := (Nat.pow_dvd_pow 2 h3).trans hh
  norm_num at hb

private theorem solvable_normalized_sup {A : Type*} [Group A]
    (B S : Subgroup A) [Group.IsSolvable B] [Group.IsSolvable S]
    (hn : S ≤ normalizer (B : Set A)) : Group.IsSolvable (B ⊔ S : Subgroup A) := by
  let D := B ⊔ S
  let : (B.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le B.le_normalizer hn)
  let : Group.IsSolvable (B.subgroupOf D) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show B ≤ D from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show B ≤ D from le_sup_left)).injective
  let : Group.IsSolvable (S.subgroupOf D) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show S ≤ D from le_sup_right)).toMonoidHom)
      (subgroupOfEquivOfLe (show S ≤ D from le_sup_right)).injective
  exact Group.isSolvable_of_normal_sup_eq_top (B.subgroupOf D) (S.subgroupOf D)
    (by rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self])

private theorem no_small_symplectic_normalized_five
    (F : BinaryField) (hF : F.degree = 2)
    (P : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F.Carrier))
    (B : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F.Carrier)) [Group.IsSolvable B]
    (hn : (P : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F.Carrier)) ≤ normalizer (B : Set _))
    (hfive : 5 ∣ Nat.card B) : False := by
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  let J := B ⊔ (P : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F.Carrier))
  let : Group.IsSolvable J := solvable_normalized_sup B P hn
  have hlarge : 2 < Nat.card F.Carrier := by rw [F.card_eq,hF]; decide
  have hle := Theory.SpecificGroups.SymplecticFour.solvable_sylow_overgroup_normalizes
    hlarge P J inferInstance le_sup_right
  have hh := hfive.trans (card_dvd_of_le (le_sup_left.trans hle))
  change 5 ∣ Nat.card (normalizer (P : Set (Theory.SpecificGroups.SymplecticFour.Sp F.Carrier))) at hh
  rw [Nat.card_congr (Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.sylowNormalizerEquiv F.card_eq F.degree_pos P).toEquiv,
    Theory.SpecificGroups.SymplecticFour.card_borel,F.card_eq,hF] at hh
  norm_num at hh

private theorem no_binary_symplectic_perfect
    (F : BinaryField) (hF : F.degree = 1)
    [Group.IsPerfect (Theory.SpecificGroups.SymplecticFour.Sp F.Carrier)] : False := by
  let a := (Theory.SpecificGroups.SymplecticFour.Binary.fieldEquivSp
      (Theory.SpecificGroups.SymplecticFour.Binary.fieldEquivZModTwo F.Carrier
        (by rw [F.card_eq,hF]; norm_num))).trans
      Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  let : Group.IsPerfect (Equiv.Perm (Fin 6)) := Group.IsPerfect.ofSurjective
    (f := a.toMonoidHom) a.surjective
  have hh := Group.IsPerfect.mem_commutator (g := Equiv.swap (0 : Fin 6) 1)
  rw [alternatingGroup.commutator_perm_eq (by simp)] at hh
  simp at hh

end WreathFiveStar
variable {G : Type*} [Group G] [Finite G]
open WreathFiveStar

/-- The full G₂ row is impossible through the original solvable, five-free
source quotient map, for every binary field. -/
theorem source_local_component_star_g2_exclusion
    {H K S W L Y : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn H) (hSH : S ≤ H)
    (heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hSyl : Chapter1.IsSylowIn 2 S W)
    (hL : L ∈ Chapter1.cComponentsIn W) (hKL : K ≤ L)
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (F : BinaryField) (q : L →* Atlas.G2.Model F.Carrier)
    (hq : Function.Surjective q) [Group.IsSolvable q.ker]
    (hk : ¬ 5 ∣ Nat.card q.ker) : False := by
  obtain ⟨P₂,B,hs,hn,hfive⟩ := source_normalized_five_image_of_surjective hSyl hL hYL hSN hc q hq hk
  let : Group.IsSolvable B := hs
  by_cases h1 : F.degree = 1
  · have hh := hfive.trans B.card_subgroup_dvd_card
    rw [Atlas.G2.card_Model,F.card_eq,h1] at hh
    norm_num at hh
  have hlarge : 2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    exact (show (2 : ℕ) ^ 1 < 2 ^ F.degree from Nat.pow_lt_pow_right (by decide) (by have := F.degree_pos; omega))
  let : IsSimpleGroup (Atlas.G2.Model F.Carrier) := Atlas.G2.isSimple hlarge
  let : Group.IsPerfect L := source_component_perfect hL
  let : Group.IsPerfect K := source_component_perfect hK
  let : Group.IsPerfect (Atlas.G2.Model F.Carrier) := Group.IsPerfect.ofSurjective hq
  obtain ⟨hD,P,f,hl⟩ := source_local_component_surjective_data hK hSH hSyl hL hKL q hq
  have hcK : Nat.card (K ⧸ pCore 2 K) = 60 := by
    rw [Nat.card_congr heK.some.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hp := local_five_join_proper_of_card hcK hD simple_twoCore_eq_bot
    (g2_card_not_dvd_sixty F) P f hl
  have hdegree := WreathFiveG2.degree_of_proper_g2_join hcK F P f hl hp
  exact WreathFiveG2.no_small_normalized_five F hdegree P₂ B hn hfive

/-- The small derived G₂ row is five-free, independently of any central
or two-group factors in the source map's solvable kernel. -/
theorem source_local_component_star_g2_derived_exclusion
    {S W L Y : Subgroup G}
    (hSyl : Chapter1.IsSylowIn 2 S W)
    (hL : L ∈ Chapter1.cComponentsIn W)
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (q : L →* commutator (Atlas.G2.Model (ZMod 2)))
    (hq : Function.Surjective q) (hk : ¬ 5 ∣ Nat.card q.ker) : False := by
  obtain ⟨_,B,_,_,hfive⟩ := source_normalized_five_image_of_surjective hSyl hL hYL hSN hc q hq hk
  have hh := hfive.trans B.card_subgroup_dvd_card
  rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hh
  norm_num at hh

/-- The full symplectic-four row is impossible through the original
solvable, five-free source quotient map, including the binary field. -/
theorem source_local_component_star_symplectic_exclusion
    {H K S W L Y : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn H) (hSH : S ≤ H)
    (heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hSyl : Chapter1.IsSylowIn 2 S W)
    (hL : L ∈ Chapter1.cComponentsIn W) (hKL : K ≤ L)
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (F : BinaryField) (q : L →* Theory.SpecificGroups.SymplecticFour.Sp F.Carrier)
    (hq : Function.Surjective q) [Group.IsSolvable q.ker]
    (hk : ¬ 5 ∣ Nat.card q.ker) : False := by
  let : Group.IsPerfect L := source_component_perfect hL
  let : Group.IsPerfect K := source_component_perfect hK
  let : Group.IsPerfect (Theory.SpecificGroups.SymplecticFour.Sp F.Carrier) := Group.IsPerfect.ofSurjective hq
  by_cases h1 : F.degree = 1
  · exact no_binary_symplectic_perfect F h1
  have hdeg : 2 ≤ F.degree := by have := F.degree_pos; omega
  let : IsSimpleGroup ((Theory.SpecificGroups.SymplecticFour.Sp F.Carrier) ⧸ center _) :=
    Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup_of_card_eq_two_pow hdeg F.card_eq
  let : IsSimpleGroup (Theory.SpecificGroups.SymplecticFour.Sp F.Carrier) :=
    (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F.Carrier)).isSimpleGroup
  obtain ⟨hD,P,f,hl⟩ := source_local_component_surjective_data hK hSH hSyl hL hKL q hq
  have hcK : Nat.card (K ⧸ pCore 2 K) = 60 := by
    rw [Nat.card_congr heK.some.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hp := local_five_join_proper_of_card hcK hD simple_twoCore_eq_bot
    (symplectic_card_not_dvd_sixty F) P f hl
  have hdegree := local_five_symplectic_degree_of_proper_join hcK F P f hl hp
  obtain ⟨P₂,B,hs,hn,hfive⟩ := source_normalized_five_image_of_surjective hSyl hL hYL hSN hc q hq hk
  let : Group.IsSolvable B := hs
  exact no_small_symplectic_normalized_five F (by omega) P₂ B hn hfive

/-- The binary linear-five row is impossible through the original five-free
source quotient map; solvability of its full kernel is not required. -/
theorem source_local_component_star_linearFive_exclusion
    {S W L Y : Subgroup G}
    (hSyl : Chapter1.IsSylowIn 2 S W)
    (hL : L ∈ Chapter1.cComponentsIn W)
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (q : L →* SL(5,ZMod 2))
    (hq : Function.Surjective q) (hk : ¬ 5 ∣ Nat.card q.ker) : False := by
  let a := BinaryLinear.OuterCyclic.slEquivLinear 5
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup 5) :=
    Finite.of_injective a.symm a.symm.injective
  let r := a.toMonoidHom.comp q
  have hr : Function.Surjective r := a.surjective.comp hq
  have hrk : r.ker = q.ker := by ext x; simp [r]
  obtain ⟨P,B,hs,hn,hfive⟩ := source_normalized_five_image_of_surjective hSyl hL hYL hSN hc r hr (hrk ▸ hk)
  let : Group.IsSolvable B := hs
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  let : Group.IsSolvable (B ⊔ (P : Subgroup (BinaryLinear.OuterCyclic.LinearGroup 5)) : Subgroup _) :=
    solvable_normalized_sup B P hn
  exact BinaryLinear.FiveFlagGeometry.solvable_sylow_overgroup_five_free P _ le_sup_right
    (hfive.trans (card_dvd_of_le (show B ≤ B ⊔ (P : Subgroup _) from le_sup_left)))

end CFSG.Quasithin.Chapter15.Section02
