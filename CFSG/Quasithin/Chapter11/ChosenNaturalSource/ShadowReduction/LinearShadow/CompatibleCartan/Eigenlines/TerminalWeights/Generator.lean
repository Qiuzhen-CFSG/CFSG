module
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Theory.GroupTheory.Hall.TwoClosedNormal
public import Mathlib.FieldTheory.Finite.Basic
/-!
# A primitive actor in the first orthogonal factor

An odd subgroup normalizing a Sylow two-subgroup embeds in the product
of the two rank-one Borel quotients. If its order is (|F| - 1)², that
embedding is surjective. Lifting a primitive unit in the first coordinate
and the identity in the second produces an actor of order |F| - 1 whose
second-factor image is trivial. Neither a torus-surjectivity premise nor
a primitive actor is assumed.

The original chosen-source application is in TerminalWeights.GeneratorSource.
Source: Aschbacher--Smith, Proposition 11.3.2, final paragraph, printed p.775.
-/
open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights
variable {A F : Type*} [Group A] [Finite A] [Field F] [Finite F] [CharP F 2]
local notation "J" => SL(2,F)

private theorem odd_sylow_disjoint (R : Sylow 2 A) (C : Subgroup A)
    (ho : Odd (Nat.card C)) : Disjoint (R : Subgroup A) C := by
  obtain ⟨n,hn⟩ := R.isPGroup'.exists_card_eq
  apply disjoint_of_coprime_natCard
  rw [hn]
  exact (Nat.coprime_two_left.mpr ho).pow_left n

omit [CharP F 2] in
private theorem pair_sylow_eq (R : Sylow 2 (J × J)) :
    (R : Subgroup (J × J)) =
      (R.mapSurjective (f := MonoidHom.fst J J) (fun x => ⟨(x,1),rfl⟩) : Subgroup J).prod
      (R.mapSurjective (f := MonoidHom.snd J J) (fun x => ⟨(1,x),rfl⟩) : Subgroup J) := by
  let R₁ := R.mapSurjective (f := MonoidHom.fst J J) (fun x => ⟨(x,1),rfl⟩)
  let R₂ := R.mapSurjective (f := MonoidHom.snd J J) (fun x => ⟨(1,x),rfl⟩)
  have htwo : IsPGroup 2 ((R₁ : Subgroup J).prod (R₂ : Subgroup J)) := by
    obtain ⟨a,ha⟩ := R₁.isPGroup'.exists_card_eq
    obtain ⟨b,hb⟩ := R₂.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := a+b) (by
      rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,ha,hb,pow_add])
  exact (R.is_maximal' htwo (fun x hx =>
    ⟨mem_map_of_mem (MonoidHom.fst J J) hx,mem_map_of_mem (MonoidHom.snd J J) hx⟩)).symm

/-- Recover a primitive first-factor actor from normalization and the actual
Cartan order; the full torus image is proved, not an input. -/
theorem exists_primitive_first_factor
    (q : A →* (J × J)) (hq : Function.Surjective q)
    (R : Sylow 2 A) (hk : q.ker ≤ (R : Subgroup A))
    (X : Subgroup A) (hn : X ≤ normalizer (R : Set A))
    (ho : Odd (Nat.card X)) (hcard : Nat.card X = (Nat.card F - 1)^2) :
    ∃ y : X, (q y).2 = 1 ∧ orderOf y = Nat.card F - 1 ∧
      orderOf (q y).1 = Nat.card F - 1 ∧
      ∀ z : X, (q z).2 = 1 → ∃ n : ℤ, y ^ n = z := by
  let Q := R.mapSurjective hq
  let Q₁ := Q.mapSurjective (f := MonoidHom.fst J J) (fun x => ⟨(x,1),rfl⟩)
  let Q₂ := Q.mapSurjective (f := MonoidHom.snd J J) (fun x => ⟨(1,x),rfl⟩)
  obtain ⟨d₁,_,hd₁⟩ := exists_sylowNormalizer_diagonal (MonoidHom.id J)
    Function.surjective_id Q₁ (by simp)
  obtain ⟨d₂,_,hd₂⟩ := exists_sylowNormalizer_diagonal (MonoidHom.id J)
    Function.surjective_id Q₂ (by simp)
  let q₁ := (MonoidHom.fst J J).comp q
  let q₂ := (MonoidHom.snd J J).comp q
  have he₁ : (R : Subgroup A).map q₁ = (Q₁ : Subgroup J) := by
    change (R : Subgroup A).map q₁ = ((R : Subgroup A).map q).map (MonoidHom.fst J J)
    exact (Subgroup.map_map _ _ _).symm
  have he₂ : (R : Subgroup A).map q₂ = (Q₂ : Subgroup J) := by
    change (R : Subgroup A).map q₂ = ((R : Subgroup A).map q).map (MonoidHom.snd J J)
    exact (Subgroup.map_map _ _ _).symm
  let f₁ : X →* normalizer (Q₁ : Set J) :=
    (q₁.comp X.subtype).codRestrict _ (by
      intro x
      have h := (R : Subgroup A).le_normalizer_map q₁ (mem_map_of_mem q₁ (hn x.property))
      rwa [he₁] at h)
  let f₂ : X →* normalizer (Q₂ : Set J) :=
    (q₂.comp X.subtype).codRestrict _ (by
      intro x
      have h := (R : Subgroup A).le_normalizer_map q₂ (mem_map_of_mem q₂ (hn x.property))
      rwa [he₂] at h)
  let r : X →* (Fˣ × Fˣ) := (d₁.comp f₁).prod (d₂.comp f₂)
  have hr : Function.Injective r := by
    apply r.ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    have hx₁ : q₁ x ∈ Q₁ := (hd₁ (f₁ x)).mp (congrArg Prod.fst hx)
    have hx₂ : q₂ x ∈ Q₂ := (hd₂ (f₂ x)).mp (congrArg Prod.snd hx)
    have hxQ : q x ∈ Q := by
      change q x ∈ (Q : Subgroup (J × J))
      rw [pair_sylow_eq Q]
      exact ⟨hx₁,hx₂⟩
    have hxR : (x : A) ∈ R := by
      have hx : (x : A) ∈ ((R : Subgroup A).map q).comap q := hxQ
      rwa [comap_map_eq_self hk] at hx
    exact Subtype.ext (disjoint_def.mp (odd_sylow_disjoint R X ho) hxR x.property)
  have hrs : Function.Surjective r := (Nat.bijective_iff_injective_and_card r).mpr
    ⟨hr,by rw [Nat.card_prod,Nat.card_units,hcard,pow_two]⟩ |>.2
  obtain ⟨a,hagen⟩ := IsCyclic.exists_generator (α := Fˣ)
  have ha := orderOf_eq_card_of_forall_mem_zpowers hagen
  obtain ⟨y,hy⟩ := hrs (a,1)
  have hysecond : (q y).2 = 1 := by
    have hy₂ : q₂ y ∈ Q₂ := (hd₂ (f₂ y)).mp (congrArg Prod.snd hy)
    have hodd : Odd (Nat.card (X.map q₂)) := ho.of_dvd_nat (card_map_dvd X q₂)
    exact disjoint_def.mp (odd_sylow_disjoint Q₂ (X.map q₂) hodd)
      hy₂ (mem_map_of_mem q₂ y.property)
  have hoy : orderOf y = Nat.card F - 1 := by
    rw [←orderOf_injective r hr y,hy,Prod.orderOf,orderOf_one,Nat.lcm_one_right,ha,Nat.card_units]
  have hqX : Function.Injective (q.comp X.subtype) := by
    apply (q.comp X.subtype).ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    exact Subtype.ext (disjoint_def.mp (odd_sylow_disjoint R X ho) (hk hx) x.property)
  refine ⟨y,hysecond,hoy,?_,?_⟩
  · have he := orderOf_injective (q.comp X.subtype) hqX y
    change orderOf (q (y : A)) = orderOf y at he
    rw [Prod.orderOf,hysecond,orderOf_one,Nat.lcm_one_right] at he
    exact he.trans hoy
  · intro z hz
    have hf₂ : f₂ z = 1 := Subtype.ext hz
    have hz₂ : (r z).2 = 1 := by
      change d₂ (f₂ z) = 1
      rw [hf₂,map_one]
    obtain ⟨n,hn⟩ := mem_zpowers_iff.mp (hagen (r z).1)
    refine ⟨n,hr ?_⟩
    rw [map_zpow,hy]
    apply Prod.ext
    · simpa using hn
    · simpa using hz₂.symm
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights
