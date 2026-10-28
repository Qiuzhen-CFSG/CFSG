module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.Preparation
public import Mathlib.GroupTheory.SchurZassenhaus
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
/-!
# Splitting and conjugation in the Sylow-five normalizer

Schur–Zassenhaus constructs a complement to the normal Sylow subgroup in
its literal normalizer. Self-centralization identifies that complement
with the image of the actual conjugation homomorphism; no dihedral model
is assumed in this construction. The remaining geometric input records a
four-group with two fixed lines, distinguished by the two source families.

This is the reduction for the final paragraph of Aschbacher, *Sporadic
Groups* (1994), 47.2, printed p.261. Identifying this action image and
constructing its marked four-group remain separate proof obligations.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction
variable {G : Type*} [Group G] [Finite G]
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
def automizer (P : Sylow 5 G) : Subgroup (MulAut P) :=
  (P : Subgroup G).normalizerMonoidHom.range

omit [Finite G] in
theorem automizer_card (P : Sylow 5 G)
    (hC : centralizer (P : Set G) = (P : Subgroup G)) :
    Nat.card (automizer P) = (P : Subgroup G).relIndex (normalizer (P : Set G)) := by
  rw [automizer, ← index_ker, normalizerMonoidHom_ker]
  change ((centralizer (P : Set G)).subgroupOf (normalizer (P : Set G))).index = _
  rw [hC]
  rfl

theorem complement_exists (P : Sylow 5 G) :
    ∃ K : Subgroup (normalizer (P : Set G)),
      K.IsComplement' ((P : Subgroup G).subgroupOf (normalizer (P : Set G))) := by
  let N := normalizer (P : Set G)
  have : ((P : Subgroup G).subgroupOf N).Normal :=
    (P : Subgroup G).normal_in_normalizer
  exact exists_left_complement'_of_coprime
    (P.subtype (show (P : Subgroup G) ≤ normalizer (P : Set G) from le_normalizer)).card_coprime_index

noncomputable def complementEquivAutomizer (P : Sylow 5 G)
    (hC : centralizer (P : Set G) = (P : Subgroup G))
    (K : Subgroup (normalizer (P : Set G)))
    (hK : K.IsComplement' ((P : Subgroup G).subgroupOf (normalizer (P : Set G)))) :
    K ≃* automizer P := by
  let f : K →* automizer P := (P : Subgroup G).normalizerMonoidHom.rangeRestrict.comp K.subtype
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    have hxC : x.val ∈ (P : Subgroup G).normalizerMonoidHom.ker := by
      change f x = 1 at hx
      exact congrArg Subtype.val hx
    rw [normalizerMonoidHom_ker] at hxC
    change (x.val : G) ∈ centralizer (P : Set G) at hxC
    rw [hC] at hxC
    have hi : x.val ∈ K ⊓ (P : Subgroup G).subgroupOf (normalizer (P : Set G)) :=
      ⟨x.property, hxC⟩
    rw [hK.disjoint.eq_bot] at hi
    exact Subtype.ext (mem_bot.mp hi)
  have hc : Nat.card K = Nat.card (automizer P) := by
    rw [automizer_card P hC]
    exact hK.index_eq_card.symm
  exact MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hc⟩)

theorem complementEquivAutomizer_apply (P : Sylow 5 G) (hC : centralizer (P : Set G) = (P : Subgroup G))
    (K : Subgroup (normalizer (P : Set G)))
    (hK : K.IsComplement' ((P : Subgroup G).subgroupOf (normalizer (P : Set G)))) (x : K) :
    ((complementEquivAutomizer P hC K hK) x).val =
      (P : Subgroup G).normalizerMonoidHom x.val := rfl

/-- The source congruence applies to the actual image of conjugation. -/
theorem automizer_card_mod (hG : Nat.card G = 604800) (P : Sylow 5 G)
    (hC : centralizer (P : Set G) = (P : Subgroup G)) :
    Nat.card (automizer P) ≡ 2 [MOD 5] := by
  rw [automizer_card P hC]
  exact sylow_normalizer_relIndex_mod hG P

/-- An identification of the conjugation image gives the required internal splitting. -/
noncomputable def splitWitnessOfAutomizer (P : Sylow 5 G)
    (hC : centralizer (P : Set G) = (P : Subgroup G))
    (e : automizer P ≃* DihedralGroup 6) : SylowSplitWitness P := by
  let K := Classical.choose (complement_exists P)
  have hK := Classical.choose_spec (complement_exists P)
  exact ⟨K, hK, (complementEquivAutomizer P hC K hK).trans e⟩

section LinearGeometry
variable {E : Type*} [Group E]

/-- Orbit membership for the specified subgroup of the literal automorphism group. -/
def InLineOrbit (H : Subgroup (MulAut E)) (A B : Subgroup E) : Prop :=
  ∃ h : H, A.map h.val.toMonoidHom = B

/-- The intermediate configuration in the source's final paragraph. The fixed
points are lines, meaning subgroups of order five, rather than vectors. -/
structure FourLineFrame (H : Subgroup (MulAut E)) where
  four : Subgroup H
  four_elementary : IsElementaryAbelian 2 four
  four_card : Nat.card four = 4
  A : Subgroup E
  B : Subgroup E
  A_card : Nat.card A = 5
  B_card : Nat.card B = 5
  /-- Among order-five subgroups, the four-group fixes exactly `A` and `B`. -/
  fixed : ∀ L : Subgroup E, Nat.card L = 5 →
    ((∀ v : four, L.map v.val.val.toMonoidHom = L) ↔ L = A ∨ L = B)
  nonfusion : ¬ InLineOrbit H A B

/-- The exact finite linear calculation still required by the reduction.
Both orbits refer to the actual automorphisms acting on the given plane. -/
structure TwoOrbitConclusion {H : Subgroup (MulAut E)} (F : FourLineFrame H) : Prop where
  dihedral : Nonempty (H ≃* DihedralGroup 6)
  six_lines : Nat.card {L : Subgroup E // Nat.card L = 5} = 6
  A_orbit_card : Nat.card {L : Subgroup E // InLineOrbit H F.A L} = 3
  B_orbit_card : Nat.card {L : Subgroup E // InLineOrbit H F.B L} = 3
  coverage : ∀ L : Subgroup E, Nat.card L = 5 →
    InLineOrbit H F.A L ∨ InLineOrbit H F.B L

end LinearGeometry

/-- The ambient image of a line in the Sylow subgroup. -/
def lineImage (P : Sylow 5 G) (L : Subgroup P) : Subgroup G :=
  L.map (P : Subgroup G).subtype

/-- The four-group geometry with its two fixed lines marked by the actual
source involution classes. This is an intermediate output, not a new seed. -/
structure SourceFrame (D : Seed G) (t : G) (P : Sylow 5 G) where
  frame : FourLineFrame (automizer P)
  root : FiveCentralizing t (lineImage P frame.A)
  twoCentral : FiveCentralizing D.z (lineImage P frame.B)

section LinearOrders
variable {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 5 E]
/-- Faithfulness embeds the given actor in GL₂(5), of order 480. -/
theorem action_card_dvd (hE : Nat.card E = 25) (H : Subgroup (MulAut E)) :
    Nat.card H ∣ 480 := by
  obtain ⟨f, hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 5) (n := 2) E (by omega)
  have hdiv := card_dvd_of_injective (f.comp H.subtype) (hf.comp H.subtype_injective)
  have h480 : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)) = 480 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ, ZMod.card]
  rwa [h480] at hdiv

private theorem card_options {n : ℕ} (hn : n ∣ 480) (hm : n ≡ 2 [MOD 5]) :
    n = 2 ∨ n = 12 ∨ n = 32 := by
  have hd : n ∈ Nat.divisors 480 := Nat.mem_divisors.mpr ⟨hn, by decide⟩
  have he : Nat.divisors 480 = {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 16, 20,
      24, 30, 32, 40, 48, 60, 80, 96, 120, 160, 240, 480} := by decide +kernel
  rw [he] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  change n % 5 = 2 % 5 at hm
  omega

/-- The source congruence and the four-group leave only orders 12 and 32. -/
theorem FourLineFrame.card_cases {H : Subgroup (MulAut E)} (F : FourLineFrame H)
    (hE : Nat.card E = 25) (hm : Nat.card H ≡ 2 [MOD 5]) :
    Nat.card H = 12 ∨ Nat.card H = 32 := by
  have hd : 4 ∣ Nat.card H := F.four_card ▸ F.four.card_subgroup_dvd_card
  rcases card_options (action_card_dvd hE H) hm with h | h | h
  · rw [h] at hd
    norm_num at hd
  · exact Or.inl h
  · exact Or.inr h

end LinearOrders

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction
