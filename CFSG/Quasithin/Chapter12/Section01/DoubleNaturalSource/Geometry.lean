module

public import CFSG.Quasithin.Chapter12.Section01
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import Theory.ElementaryAbelian.BinaryRankDifference

/-!
# The dimension estimate in 12.1.9(3)

A totally singular subspace U inside a nondegenerate fixed space F has
twice its dimension at most dim F. If F has codimension at least four
inside the doubled 2n-dimensional space, U has codimension at least n+2.
The subgroup application uses the literal relative index defining r(G,W);
no action of the whole ambient G on W is assumed.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
12.1.2 and the last paragraph of 12.1.9, pp.789,793--794.
-/

public noncomputable section
open Module Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource

/-- The improved bound once the odd actor supplies its nondegenerate fixed space. -/
theorem codimension_ge_of_nondegenerate_container
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (Q : QuadraticForm K E) (U F : Submodule K E) (n : ℕ)
    (hd : finrank K E = 2 * n) (hUF : U ≤ F)
    (hF : (Q.comp F.subtype).polarBilin.Nondegenerate)
    (hcodim : 4 ≤ finrank K (E ⧸ F)) (hU : ∀ u ∈ U, Q u = 0) :
    n + 2 ≤ finrank K (E ⧸ U) := by
  have hb := twice_finrank_le_of_totally_singular (Q.comp F.subtype) hF
    (U.comap F.subtype) (fun u hu => hU u hu)
  rw [(Submodule.comapSubtypeEquivOfLe hUF).finrank_eq] at hb
  have hUdim := Submodule.finrank_quotient_add_finrank U
  have hFdim := Submodule.finrank_quotient_add_finrank F
  omega

/-- The subspace of W belonging to a literal ambient subgroup U. -/
def subgroupSpace {G : Type*} [Group G] (W U : Subgroup G) [IsElementaryAbelian 2 W] :
    Submodule (ZMod 2) (Additive W) :=
  AddSubgroup.toZModSubmodule 2 (U.subgroupOf W).toAddSubgroup

@[simp] theorem mem_subgroupSpace {G : Type*} [Group G] (W U : Subgroup G)
    [IsElementaryAbelian 2 W] (u : Additive W) :
    u ∈ subgroupSpace W U ↔ u.toMul.val ∈ U := Iff.rfl

theorem subgroupSpace_finrank {G : Type*} [Group G] [Finite G]
    (W U : Subgroup G) [IsElementaryAbelian 2 W] (hUW : U ≤ W) :
    finrank (ZMod 2) (subgroupSpace W U) = Nat.log 2 (Nat.card U) := by
  have he : (subgroupSpace W U) ≃ U := {
    toFun u := ⟨u.val.toMul.val, u.property⟩
    invFun u := ⟨Additive.ofMul ⟨u.val, hUW u.property⟩, u.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := subgroupSpace W U)
  rw [Nat.card_congr he, Nat.card_zmod] at hc
  rw [hc, Nat.log_pow (by decide)]

/-- Convert a geometric bound for all escaping subgroups into the source r. -/
theorem globalR_ge_of_escape_codimension {G : Type*} [Group G] [Finite G]
    (W M : Subgroup G) [IsElementaryAbelian 2 W] (hNM : normalizer (W : Set G) = M)
    (b : ℕ)
    (hbound : ∀ U : Subgroup G, U ≤ W → ¬ centralizer (U : Set G) ≤ M →
      b ≤ finrank (ZMod 2) ((Additive W) ⧸ subgroupSpace W U)) :
    (b : ℕ∞) ≤ ChapterE.globalR W := by
  apply le_iInf
  intro U
  apply le_iInf
  rintro ⟨hUW, hesc⟩
  have hb := hbound U hUW (by rwa [← hNM])
  have hdim := Submodule.finrank_quotient_add_finrank (subgroupSpace W U)
  rw [subgroupSpace_finrank W U hUW] at hdim
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
  have hW : Nat.log 2 (Nat.card W) = finrank (ZMod 2) (Additive W) := by
    change Nat.card W = _ at hcard
    rw [hcard, Nat.card_zmod, Nat.log_pow (by decide)]
  have hi := log_card_sub_log_card_eq_log_relIndex W U hUW
  rw [hW] at hi
  have : b ≤ ChapterE.subgroupCorank W U := by
    unfold ChapterE.subgroupCorank
    omega
  exact_mod_cast this

/-- Actual escaping centralizers force singularity; the ambient group need
not act on W, since only its normalizer has a conjugation action on W. -/
theorem singular_of_centralizer_escape {G : Type*} [Group G]
    (W M U : Subgroup G) [IsElementaryAbelian 2 W]
    (Q : QuadraticForm (ZMod 2) (Additive W))
    (hcentral : ∀ w : W, Q (Additive.ofMul w) ≠ 0 →
      centralizer ({(w : G)} : Set G) ≤ M)
    (hescape : ¬ centralizer (U : Set G) ≤ M) :
    ∀ u ∈ subgroupSpace W U, Q u = 0 := by
  obtain ⟨g, hg, hgM⟩ := Set.not_subset.mp hescape
  intro u hu
  by_contra hq
  apply hgM
  apply hcentral u.toMul hq
  exact mem_centralizer_singleton_iff.mpr ((hg u.toMul.val hu).symm)

/-- The literal r-bound needed by 12.1.10, conditional only on the source
nonsingular centralizers and the nondegenerate odd-actor fixed spaces. -/
theorem globalR_ge_of_fixed_spaces {G : Type*} [Group G] [Finite G]
    (W M : Subgroup G) [IsElementaryAbelian 2 W]
    (Q : QuadraticForm (ZMod 2) (Additive W)) (n : ℕ)
    (hd : finrank (ZMod 2) (Additive W) = 2 * n)
    (hNM : normalizer (W : Set G) = M)
    (hcentral : ∀ w : W, Q (Additive.ofMul w) ≠ 0 →
      centralizer ({(w : G)} : Set G) ≤ M)
    (hfixed : ∀ U : Subgroup G, U ≤ W → ¬ centralizer (U : Set G) ≤ M →
      ∃ F : Submodule (ZMod 2) (Additive W), subgroupSpace W U ≤ F ∧
        (Q.comp F.subtype).polarBilin.Nondegenerate ∧
        4 ≤ finrank (ZMod 2) ((Additive W) ⧸ F)) :
    ((n + 2 : ℕ) : ℕ∞) ≤ ChapterE.globalR W := by
  apply globalR_ge_of_escape_codimension W M hNM (n + 2)
  intro U hUW hesc
  obtain ⟨F, hUF, hF, hc⟩ := hfixed U hUW hesc
  exact codimension_ge_of_nondegenerate_container Q (subgroupSpace W U) F n hd hUF hF hc
    (singular_of_centralizer_escape W M U Q hcentral hesc)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
