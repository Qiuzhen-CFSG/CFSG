module
public import Theory.SpecificGroups.SL2.CubicNormalizerGeneration
public import Theory.GroupTheory.CoprimeCentralizerCard
public import Theory.GroupAction.NoncentralTwoChiefLength.Native
public import Theory.GroupTheory.ConjugateSpanOrder
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Two cubic factors forced by a Sylow-central four-plane

In a finite abelian two-group, the cubic fixed index is the order of
the moved subgroup. If the whole module has cubic length at most one,
a moving four-plane is therefore the entire moved subgroup. Its
normalizer contains the cubic normalizer and its centralizer contains
the Sylow two-subgroup. For an SL₂(4) quotient with two-group kernel,
these subgroups generate, making the plane invariant. Simplicity of
the quotient then forces the plane to be centralized, a contradiction.

This is the field-four instance of the chief-factor count in
Aschbacher--Smith 5.1.23, printed pp.645--646, refs/quasithin.pdf.
All subgroups and the quotient homomorphism in the conclusion are literal.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace Matrix.SpecialLinearGroup.CubicChiefCount
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

private theorem normal_eq_top_of_sylow_le (hF : Nat.card F = 4)
    (q : G →* SL(2,F)) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (P : Sylow 2 G) (K : Subgroup G) [K.Normal] (hPK : (P : Subgroup G) ≤ K) :
    K = ⊤ := by
  let e := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).trans
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup SL(2,F) := e.isSimpleGroup
  let : (K.map q).Normal := Subgroup.Normal.map inferInstance q hq
  have him : K.map q = ⊤ := by
    rcases (inferInstance : (K.map q).Normal).eq_bot_or_eq_top with he | he
    · have hb : ((P.mapSurjective hq) : Subgroup SL(2,F)) = ⊥ :=
        bot_unique (he ▸ map_mono hPK)
      have hc := Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2
        (P.mapSurjective hq)).symm.toEquiv
      change Nat.card ((P.mapSurjective hq) : Subgroup SL(2,F)) = Nat.card F at hc
      rw [hb,Nat.card_unique,hF] at hc
      omega
    · exact he
  have hh := congrArg (comap q) him
  rwa [comap_map_eq_self ((hk.le_sylow_of_normal P).trans hPK),comap_top] at hh

theorem moved_card_eq (C W : Subgroup G) [IsMulCommutative W]
    (hC : IsPGroup 3 C) (hW : IsPGroup 2 W)
    (hCW : C ≤ normalizer (W : Set G)) :
    Nat.card (⁅W,C⁆ : Subgroup G) = 4 ^ conjugationCubicLength C W := by
  have hcop : Nat.Coprime (Nat.card C) (Nat.card W) := by
    obtain ⟨i,hi⟩ := hC.exists_card_eq
    obtain ⟨j,hj⟩ := hW.exists_card_eq
    rw [hi,hj]
    exact ((by decide : Nat.Coprime 3 2).pow_left i).pow_right j
  let := conjMulDistribMulActionOfLeNormalizer C W hCW
  have hc : FixedPoints.subgroup C W = (centralizer (C : Set G)).subgroupOf W := by
    ext x
    constructor
    · intro hx c hc
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (hx ⟨c,hc⟩))
    · intro hx c
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hx c c.property)
  have hi := FixedPoints.index_eq_four_pow_cubicLength hC hW
  rw [← conjugationCubicLength_eq C W hCW,hc] at hi
  have hcard : Nat.card ((centralizer (C : Set G)).subgroupOf W) =
      Nat.card (W ⊓ centralizer (C : Set G) : Subgroup G) := by
    rw [← inf_subgroupOf_left]
    exact Nat.card_congr (subgroupOfEquivOfLe (show W ⊓ centralizer (C : Set G) ≤ W from inf_le_left)).toEquiv
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := (W ⊓ centralizer (C : Set G) : Subgroup G)))
  rw [commutator_card_mul_centralizer_card W C hCW hcop,← hi,← hcard]
  exact ((centralizer (C : Set G)).subgroupOf W).index_mul_card.symm

theorem moved_eq_plane (C W V : Subgroup G) [IsMulCommutative W]
    (hC : IsPGroup 3 C) (hW : IsPGroup 2 W)
    (hVW : V ≤ W) (hCW : C ≤ normalizer (W : Set G))
    (hCV : C ≤ normalizer (V : Set G)) (hV : Nat.card V = 4)
    (hmove : conjugationCubicLength C V = 1)
    (hl : conjugationCubicLength C W ≤ 1) : ⁅W,C⁆ = V := by
  let : IsMulCommutative V := le_centralizer_iff_isMulCommutative.mp
    (hVW.trans ((le_centralizer W).trans (centralizer_le hVW)))
  have hv : ⁅V,C⁆ = V := by
    apply eq_of_le_of_card_ge (le_normalizer_iff_commutator_le_left.mp hCV)
    rw [moved_card_eq C V hC (hW.to_le hVW) hCV,hmove,hV]
    decide
  apply (eq_of_le_of_card_ge (hv ▸ commutator_mono hVW le_rfl) ?_).symm
  rw [moved_card_eq C W hC hW hCW,hV]
  exact Nat.pow_le_pow_right (by decide : 0 < (4 : ℕ)) hl

theorem length_ge_two (hF : Nat.card F = 4)
    (q : G →* SL(2,F)) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (P : Sylow 2 G) (C W V : Subgroup G) [W.Normal] [IsMulCommutative W]
    (hC : Nat.card C = 3) (hW : IsPGroup 2 W)
    (hCP : C ≤ normalizer (P : Set G)) (hVW : V ≤ W)
    (hCV : C ≤ normalizer (V : Set G)) (hV : Nat.card V = 4)
    (hmove : conjugationCubicLength C V = 1)
    (hPV : (P : Subgroup G) ≤ centralizer (V : Set G)) :
    2 ≤ conjugationCubicLength C W := by
  by_contra hl
  have hCW : C ≤ normalizer (W : Set G) := le_normalizer_of_normal
  have he := moved_eq_plane C W V
    (IsPGroup.of_card (n := 1) (by simpa using hC)) hW hVW hCW hCV hV hmove (by omega)
  have hNV : normalizer (C : Set G) ≤ normalizer (V : Set G) := by
    rw [← he]
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (show g ∈ normalizer (W : Set G) from
        W.normalizer_eq_top ▸ mem_top g),mem_normalizer_iff_map_conj_eq.mp hg]
  have hnorm : normalizer (V : Set G) = ⊤ := by
    apply top_unique
    rw [← Matrix.SpecialLinearGroup.cubic_normalizer_sup_sylow hF q hq hk P C hC hCP]
    exact sup_le (hPV.trans (centralizer_le_normalizer _)) hNV
  let : V.Normal := normalizer_eq_top_iff.mp hnorm
  have hcent : centralizer (V : Set G) = ⊤ :=
    normal_eq_top_of_sylow_le hF q hq hk P _ hPV
  have hz : ⁅W,C⁆ = ⊥ := by
    have hVC : V ≤ centralizer (C : Set G) := le_centralizer_iff.mpr (hcent ▸ le_top)
    have hcomm : ⁅V,C⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hVC
    have hv : ⁅V,C⁆ = V := by
      let : IsMulCommutative V := le_centralizer_iff_isMulCommutative.mp
        (hVW.trans ((le_centralizer W).trans (centralizer_le hVW)))
      apply eq_of_le_of_card_ge (le_normalizer_iff_commutator_le_left.mp hCV)
      rw [moved_card_eq C V (IsPGroup.of_card (n := 1) (by simpa using hC))
        (hW.to_le hVW) hCV,hmove,hV]
      decide
    exact he.trans (hv.symm.trans hcomm)
  have hvbot : V = ⊥ := he.symm.trans hz
  rw [hvbot,Nat.card_unique] at hV
  omega
end Matrix.SpecialLinearGroup.CubicChiefCount
