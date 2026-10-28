module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.EarlierGeometry
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.Mathieu.M22.ValueBoundParabolics.SmallQuotients
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# The unique invariant constituent in the case-five tensor module

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Hypothesis 14.3.10 (printed p.993), case 14.4.2(5) (p.1006), and
Lemma 14.4.10(2), first proof paragraph (p.1010).

The elementary eight-group Wᵍ* cannot embed in S₅, whose two-rank is two.
Its projection kernel therefore contains a nonidentity element (s,1),
centralizing the marked component. In the binary natural S₃-module choose
a basis (n,rn) with s(a,b) = (a+b,b). Tensoring this basis constructs the
literal displacement range and its cubic-translate complement, together
with the constituent equivalence and its alternating-group equivariance.

The S₃ projection of the actual Sylow image is cyclic, which proves
T-invariance. A T-invariant irreducible component submodule has nonzero
intersection with the fixed space of s: either a nonzero vector is fixed,
or its nonzero displacement is fixed. Both source constituent models are
proved irreducible, so this intersection proves uniqueness. The source
point is fixed by T by the earlier normalization argument.

The exported existence theorem takes only EarlierGeometry and the allowed
component-image marking. It constructs every SelectedConstituent field
and applies that witness to the literal first moved-plane split. The
source assembly owner retains the genuine Hypothesis 14.3.10, including
extraspecial U in §14.4, and discharges the component marking using the
family-images producer. This module does not assert the later intersection
calculation or the remaining clauses of 14.4.10.
-/

@[expose] public section

open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
open Theory.GroupTheory
variable {D : Subgroup Five}

/-- The two-rank of S₅ forces a nontrivial pure S₃ involution in an elementary eight-group. -/
lemma exists_pure_involution (A : Subgroup (Three × D))
    [IsElementaryAbelian 2 A] (hcard : Nat.card A = 8) :
    ∃ s : Three, s ≠ 1 ∧ s ^ 2 = 1 ∧ (s, (1 : D)) ∈ A := by
  let f : Three × D →* Five := D.subtype.comp (MonoidHom.snd Three D)
  have hn : ¬ Function.Injective (f.comp A.subtype) := by
    intro hi
    have hc : Nat.card (A.map f) = 8 := by
      have he := MonoidHom.ofInjective hi
      rw [← MonoidHom.map_range, A.range_subtype] at he
      exact (Nat.card_congr he.toEquiv).symm.trans hcard
    have hr := (primeRank_le_iff_elementary_card_le Five).mp
      Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two
      (A.map f) (IsElementaryAbelian.map f)
    rw [hc] at hr
    norm_num at hr
  have hk : (f.comp A.subtype).ker ≠ ⊥ := by
    intro he
    exact hn ((MonoidHom.ker_eq_bot_iff _).mp he)
  obtain ⟨a, ha, hne⟩ := (Subgroup.nontrivial_iff_exists_ne_one _).mp ((Subgroup.nontrivial_iff_ne_bot _).mpr hk)
  have hsnd : a.val.2 = 1 := Subtype.ext ha
  refine ⟨a.val.1, ?_, ?_, ?_⟩
  · intro hf
    apply hne
    apply Subtype.ext
    exact Prod.ext hf hsnd
  · exact congrArg Prod.fst (elemPow_eq_one_of_isElementaryAbelian a.val a.property)
  · simpa only [← hsnd, Prod.eta] using a.property

/-- The S₃ projection of a two-subgroup is cyclic, so its elements commute. -/
lemma first_coordinates_commute (B : Subgroup (Three × D)) (hB : IsPGroup 2 B)
    (a b : Three × D) (ha : a ∈ B) (hb : b ∈ B) : Commute a.1 b.1 := by
  obtain ⟨S,hS⟩ := (hB.map (MonoidHom.fst Three D)).exists_le_sylow
  have hc : Nat.card S = 2 := by
    rw [S.card_eq_multiplicity, Nat.card_perm, Nat.card_fin]
    decide +kernel
  let : IsCyclic S := isCyclic_of_prime_card hc
  let : CommGroup S := IsCyclic.commGroup
  have haS : a.1 ∈ (S : Subgroup Three) := hS (mem_map_of_mem _ ha)
  have hbS : b.1 ∈ (S : Subgroup Three) := hS (mem_map_of_mem _ hb)
  exact congrArg Subtype.val (mul_comm (⟨a.1,haS⟩ : S) ⟨b.1,hbS⟩)

namespace CaseFiveCoordinates
variable {G : Type*} [Group G]
  {hAD : AltFive ≤ D} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {H U : Subgroup G} (c : CaseFiveCoordinates hAD (V := V) H U)
  {T P : Subgroup G} {g : G}

/-- The original Sylow witness makes the literal actor image a two-group. -/
lemma EarlierGeometry.actor_pgroup (h : c.EarlierGeometry T P g) :
    IsPGroup 2 (c.actorImage T) := by
  obtain ⟨S, hS⟩ := h.sylow
  have ht : IsPGroup 2 T := hS ▸ S.isPGroup'.map H.subtype
  have hq : IsPGroup 2 (star H T) :=
    (ht.comap_of_injective H.subtype Subtype.val_injective).map (QuotientGroup.mk' _)
  exact hq.map c.actor.toMonoidHom

/-- Apply the elementary eight-group calculation to the actual image of Wᵍ. -/
lemma EarlierGeometry.exists_pure_involution (h : c.EarlierGeometry T P g) :
    ∃ s : Three, s ≠ 1 ∧ s ^ 2 = 1 ∧
      (s, (1 : D)) ∈ c.actorImage (conjugateLayer U P g) := by
  let := h.conjugate_elementary
  let : IsElementaryAbelian 2 (c.actorImage (conjugateLayer U P g)) :=
    IsElementaryAbelian.map c.actor.toMonoidHom
  apply Tensor.exists_pure_involution
  change Nat.card ((star H (conjugateLayer U P g)).map c.actor.toMonoidHom) = 8
  rw [Subgroup.card_map_of_injective c.actor.injective, h.conjugate_card]

/-- Select a nonidentity element of Wᵍ* centralizing the marked component image. -/
lemma EarlierGeometry.selected_element (h : c.EarlierGeometry T P g)
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D)) :
    ∃ x : coreQuotient H, x ∈ star H (conjugateLayer U P g) ∧ x ≠ 1 ∧
      x ∈ centralizer (star H (component H) : Set (coreQuotient H)) ∧
      (c.actor x).2 = 1 ∧ (c.actor x).1 ^ 2 = 1 := by
  obtain ⟨s, hs, hs2, x, hx, he⟩ := h.exists_pure_involution c
  change c.actor x = (s,1) at he
  refine ⟨x, hx, ?_, ?_, ?_, ?_⟩
  · intro hx1
    rw [hx1, map_one] at he
    exact hs (congrArg Prod.fst he).symm
  · apply mem_centralizer_iff.mpr
    intro y hy
    apply c.actor.injective
    have hym : c.actor y ∈ c.actorImage (component H) := mem_map_of_mem _ hy
    rw [hK] at hym
    have hy1 : (c.actor y).1 = 1 := hym.1
    simp only [map_mul, he, Prod.ext_iff, Prod.fst_mul, Prod.snd_mul, hy1,
      one_mul, mul_one, and_self]
  · exact congrArg Prod.snd he
  · simpa only [he] using hs2

end CaseFiveCoordinates
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
variable {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {σ : Representation (ZMod 2) D V}

/-- Both source constituents are irreducible under the displayed alternating-group action. -/
lemma IsSourceConstituent.invariant_dichotomy (h : IsSourceConstituent hAD σ)
    (M : Submodule (ZMod 2) V)
    (hi : ∀ (a : AltFive) (v : V), v ∈ M → σ (inclusion hAD a) v ∈ M) :
    M = ⊥ ∨ M = ⊤ := by
  by_cases hm : M = ⊥
  · exact Or.inl hm
  right
  obtain ⟨v, hv, hv0⟩ := M.ne_bot_iff.mp hm
  rcases h with ⟨e, f, he⟩ | ⟨f, he⟩
  · apply Submodule.eq_top_iff'.mpr
    intro w
    by_cases hw : w = 0
    · simp [hw]
    obtain ⟨a, ha⟩ := Representation.SL2FourNatural.transitive_nonzero (f v) (f w)
      (by simpa using hv0) (by simpa using hw)
    have hh : σ (inclusion hAD (e.symm a)) v = w := by
      apply f.injective
      rw [he, e.apply_symm_apply, ha]
    rw [← hh]
    exact hi _ _ hv
  · let j := (BinaryPermutation.core (Fin 5)).subtype.comp f.toLinearMap
    let W := M.map j
    have hW (a : AltFive) (w : BinaryPermutation.Full (Fin 5)) (hw : w ∈ W) :
        BinaryPermutation.representation (Fin 5) a.val w ∈ W := by
      obtain ⟨u, hu, rfl⟩ := hw
      refine ⟨σ (inclusion hAD a) u, hi a u hu, ?_⟩
      exact congrArg Subtype.val (he a u)
    have hle : W ≤ BinaryPermutation.core (Fin 5) := by
      rintro _ ⟨u, hu, rfl⟩
      exact (f u).property
    have hcore : BinaryPermutation.core (Fin 5) ≤ W := by
      rcases BinaryPermutation.invariant_le_constants_or_core_le (by simp) W hW with hc | hc
      · have hz : j v = 0 :=
          (Submodule.disjoint_def.mp (BinaryPermutation.core_isCompl_constants (Fin 5)
            (show Odd (Fintype.card (Fin 5)) by decide)).disjoint)
              _ (hle ⟨v, hv, rfl⟩) (hc ⟨v, hv, rfl⟩)
        have hfz : f v = 0 := Subtype.ext hz
        have : v = 0 := f.map_eq_zero_iff.mp hfz
        exact (hv0 this).elim
      · exact hc
    apply Submodule.eq_top_iff'.mpr
    intro w
    obtain ⟨u, hu, hue⟩ := hcore (f w).property
    have : u = w := f.injective (Subtype.ext hue)
    simpa [this] using hu

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
namespace Invariant
abbrev F := ZMod 2
abbrev N := BinaryPermutation.core (Fin 3)
abbrev rho := BinaryPermutation.coreRepresentation (Fin 3)
abbrev r := InvertedCubicTensor.cubic

/-- Coordinates in the binary natural module given by n and its cubic translate. -/
def frameMap (n : N) : (F × F) →ₗ[F] N where
  toFun z := z.1 • n + z.2 • rho r n
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
  map_smul' a b := by simp [smul_add, mul_smul]

/-- Every nontrivial involution admits a frame in which it sends (a,b) to (a+b,b). -/
lemma exists_frame (s : Three) (hs : s ^ 2 = 1) (hne : s ≠ 1) :
    ∃ n : N, Function.Bijective (frameMap n) ∧
      rho s n = n ∧ rho s (rho r n) = n + rho r n := by
  let : DecidablePred (· ∈ BinaryPermutation.core (Fin 3)) := fun v =>
    inferInstanceAs (Decidable ((∑ i, v i) = (0 : ZMod 2)))
  let : Fintype N := Subtype.fintype _
  revert s
  decide

variable {V : Type*} [AddCommGroup V] [Module F V]
  (n : N) (hn : Function.Bijective (frameMap n))

/-- Tensor the natural-module frame with the actual four-dimensional constituent. -/
noncomputable def pair : (V × V) ≃ₗ[F] (N ⊗[F] V) :=
  (((TensorProduct.lid F V).symm.prodCongr (TensorProduct.lid F V).symm).trans
    (TensorProduct.prodLeft F F F F V).symm).trans
      (TensorProduct.congr (LinearEquiv.ofBijective (frameMap n) hn) (LinearEquiv.refl F V))

lemma pair_left (v : V) : pair n hn (v, 0) = n ⊗ₜ[F] v := by
  change TensorProduct.congr _ _ ((TensorProduct.prodLeft F F F F V).symm
    ((TensorProduct.lid F V).symm v, (TensorProduct.lid F V).symm 0)) = _
  simp only [TensorProduct.lid_symm_apply, TensorProduct.tmul_zero]
  rw [show ((1 : F) ⊗ₜ[F] v, (0 : F ⊗[F] V)) = ((1 : F) ⊗ₜ[F] v, (0 : F) ⊗ₜ[F] v) by simp]
  rw [TensorProduct.prodLeft_symm_tmul, TensorProduct.congr_tmul]
  simp [frameMap]

lemma pair_right (v : V) : pair n hn (0, v) = rho r n ⊗ₜ[F] v := by
  change TensorProduct.congr _ _ ((TensorProduct.prodLeft F F F F V).symm
    ((TensorProduct.lid F V).symm 0, (TensorProduct.lid F V).symm v)) = _
  simp only [TensorProduct.lid_symm_apply, TensorProduct.tmul_zero]
  rw [show ((0 : F ⊗[F] V), (1 : F) ⊗ₜ[F] v) = ((0 : F) ⊗ₜ[F] v, (1 : F) ⊗ₜ[F] v) by simp]
  rw [TensorProduct.prodLeft_symm_tmul, TensorProduct.congr_tmul]
  simp [frameMap]

lemma pair_apply (a b : V) : pair n hn (a,b) = n ⊗ₜ[F] a + rho r n ⊗ₜ[F] b := by
  rw [show (a,b) = (a,0) + (0,b) by simp, map_add, pair_left, pair_right]

variable {D : Subgroup Five} (σ : Representation F D V)

lemma pair_component (d : D) (a b : V) :
    sourceTensorAction σ (1,d) (pair n hn (a,b)) = pair n hn (σ d a, σ d b) := by
  rw [pair_apply, map_add, pair_apply]
  change (rho 1 n ⊗ₜ[F] σ d a) + (rho 1 (rho r n) ⊗ₜ[F] σ d b) = _
  simp

lemma pair_cubic_left (v : V) :
    sourceTensorAction σ (r,1) (pair n hn (v,0)) = pair n hn (0,v) := by
  rw [pair_left, pair_right]
  change rho r n ⊗ₜ[F] σ 1 v = _
  simp

lemma pair_involution (s : Three) (hfix : rho s n = n)
    (hmove : rho s (rho r n) = n + rho r n) (a b : V) :
    sourceTensorAction σ (s,1) (pair n hn (a,b)) = pair n hn (a+b,b) := by
  rw [pair_apply, map_add, pair_apply]
  change (rho s n ⊗ₜ[F] σ 1 a) + (rho s (rho r n) ⊗ₜ[F] σ 1 b) = _
  simp only [hfix, hmove, map_one, Module.End.one_apply, add_tmul, tmul_add]
  abel

/-- The first coordinate summand; it will be identified with the literal displacement range. -/
noncomputable def first : Submodule F (N ⊗[F] V) :=
  LinearMap.range ((pair n hn).toLinearMap.comp (LinearMap.inl F V V))
/-- The complementary coordinate summand, obtained by cubic translation. -/
noncomputable def second : Submodule F (N ⊗[F] V) :=
  LinearMap.range ((pair n hn).toLinearMap.comp (LinearMap.inr F V V))

lemma mem_first (a b : V) : pair n hn (a,b) ∈ first n hn ↔ b = 0 := by
  constructor
  · rintro ⟨v,hv⟩
    change pair n hn (v,0) = pair n hn (a,b) at hv
    exact (congrArg Prod.snd ((pair n hn).injective hv)).symm
  · rintro rfl
    exact ⟨a,rfl⟩

lemma mem_second (a b : V) : pair n hn (a,b) ∈ second n hn ↔ a = 0 := by
  constructor
  · rintro ⟨v,hv⟩
    change pair n hn (0,v) = pair n hn (a,b) at hv
    exact (congrArg Prod.fst ((pair n hn).injective hv)).symm
  · rintro rfl
    exact ⟨b,rfl⟩

lemma compl : IsCompl (first (V := V) n hn) (second n hn) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro z hz1 hz2
    obtain ⟨⟨a,b⟩,rfl⟩ := (pair n hn).surjective z
    rw [mem_first] at hz1
    rw [mem_second] at hz2
    simp [hz1,hz2]
  · apply codisjoint_iff.mpr
    apply Submodule.eq_top_iff'.mpr
    intro z
    obtain ⟨⟨a,b⟩,rfl⟩ := (pair n hn).surjective z
    rw [show (a,b) = (a,0) + (0,b) by simp, map_add]
    exact Submodule.add_mem_sup ⟨a,rfl⟩ ⟨b,rfl⟩

lemma second_translate : second n hn = (first n hn).map (sourceTensorAction σ (r,1)) := by
  ext z
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨pair n hn (v,0), ⟨v,rfl⟩, pair_cubic_left n hn σ v⟩
  · rintro ⟨_,⟨v,rfl⟩,rfl⟩
    exact ⟨v,pair_cubic_left n hn σ v |>.symm⟩

/-- The first summand is exactly the selected involution’s displacement space. -/
lemma first_range (s : Three) (hfix : rho s n = n)
    (hmove : rho s (rho r n) = n + rho r n) :
    first n hn = LinearMap.range (sourceTensorAction σ (s,1) - LinearMap.id) := by
  ext z
  constructor
  · rintro ⟨v,rfl⟩
    refine ⟨pair n hn (0,v), ?_⟩
    change sourceTensorAction σ (s,1) (pair n hn (0,v)) - pair n hn (0,v) = pair n hn (v,0)
    rw [pair_involution n hn σ s hfix hmove, ← map_sub]
    simp
  · rintro ⟨z,rfl⟩
    obtain ⟨⟨a,b⟩,rfl⟩ := (pair n hn).surjective z
    change sourceTensorAction σ (s,1) (pair n hn (a,b)) - pair n hn (a,b) ∈ first n hn
    rw [pair_involution n hn σ s hfix hmove, ← map_sub]
    exact (mem_first n hn _ _).mpr (sub_self b)

/-- For this involution its fixed space equals its displacement space. -/
lemma fixed_iff (s : Three) (hfix : rho s n = n)
    (hmove : rho s (rho r n) = n + rho r n) (z : N ⊗[F] V) :
    sourceTensorAction σ (s,1) z = z ↔ z ∈ first n hn := by
  obtain ⟨⟨a,b⟩,rfl⟩ := (pair n hn).surjective z
  rw [pair_involution n hn σ s hfix hmove, (pair n hn).injective.eq_iff,
    Prod.mk.injEq, mem_first]
  simp

end Invariant
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
namespace Invariant
variable {V : Type*} [AddCommGroup V] [Module F V]
  (n : N) (hn : Function.Bijective (frameMap n))

/-- The actual linear identification of the constituent with the first summand. -/
noncomputable def firstEquiv : V ≃ₗ[F] first (V := V) n hn :=
  LinearEquiv.ofInjective ((pair n hn).toLinearMap.comp (LinearMap.inl F V V)) (by
    intro a b he
    change pair n hn (a,0) = pair n hn (b,0) at he
    exact congrArg Prod.fst ((pair n hn).injective he))

lemma firstEquiv_apply (v : V) : (firstEquiv n hn v).val = pair n hn (v,0) := rfl

variable {D : Subgroup Five} (σ : Representation F D V)

lemma first_component_invariant : (⊥ : Subgroup Three).prod (⊤ : Subgroup D) ≤
    subspaceStabilizer (sourceTensorAction σ) (first n hn) := by
  apply le_subspaceStabilizer
  intro a ha z hz
  obtain ⟨v,hv⟩ := hz
  change pair n hn (v,0) = z at hv
  rw [← hv, show a = (1,a.2) from Prod.ext ha.1 rfl, pair_component]
  simp only [map_zero]
  exact ⟨σ a.2 v,rfl⟩

lemma second_component_invariant : (⊥ : Subgroup Three).prod (⊤ : Subgroup D) ≤
    subspaceStabilizer (sourceTensorAction σ) (second n hn) := by
  apply le_subspaceStabilizer
  intro a ha z hz
  obtain ⟨v,hv⟩ := hz
  change pair n hn (0,v) = z at hv
  rw [← hv, show a = (1,a.2) from Prod.ext ha.1 rfl, pair_component]
  simp only [map_zero]
  exact ⟨σ a.2 v,rfl⟩

end Invariant
namespace CaseFiveCoordinates
variable {G : Type*} [Group G]
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {H U : Subgroup G} (c : CaseFiveCoordinates hAD (V := V) H U)
open Invariant

/-- Transport the proved irreducibility of either source model to the first summand. -/
lemma frame_first_irreducible
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D))
    (n : N) (hn : Function.Bijective (frameMap n)) :
    c.IsIrreducibleFor (component H) (Invariant.first n hn) := by
  have hinv : c.actorImage (component H) ≤
      subspaceStabilizer (sourceTensorAction c.constituent) (Invariant.first n hn) := by
    rw [hK]
    exact (prod_mono le_rfl le_top).trans (first_component_invariant n hn c.constituent)
  refine ⟨?_, hinv, ?_⟩
  · have hd := (firstEquiv (V := V) n hn).finrank_eq.symm.trans c.constituent_model.finrank_four
    intro hz
    rw [hz, finrank_bot] at hd
    omega
  · intro M hM hMi
    let j := (pair (V := V) n hn).toLinearMap.comp (LinearMap.inl F V V)
    have hj (v : V) : j v = pair n hn (v,0) := rfl
    have he (a : AltFive) (v : V) : j (c.constituent (inclusion hAD a) v) =
        sourceTensorAction c.constituent (1,inclusion hAD a) (j v) := by
      simp only [hj, pair_component, map_zero]
    have hW (a : AltFive) (v : V) (hv : v ∈ M.comap j) :
        c.constituent (inclusion hAD a) v ∈ M.comap j := by
      change j (c.constituent (inclusion hAD a) v) ∈ M
      rw [he]
      apply (hMi ?_ _).mpr hv
      rw [hK]
      exact ⟨rfl,a.property⟩
    rcases c.constituent_model.invariant_dichotomy (M.comap j) hW with hz | ht
    · left
      apply le_bot_iff.mp
      intro z hzM
      obtain ⟨v,hv⟩ := hM hzM
      change j v = z at hv
      have hvM : v ∈ M.comap j := by
        change j v ∈ M
        rw [hv]
        exact hzM
      rw [hz, Submodule.mem_bot] at hvM
      subst v
      change pair n hn (0 : V × V) = z at hv
      simpa only [map_zero, Submodule.mem_bot] using hv.symm
    · right
      apply le_antisymm hM
      rintro z ⟨v,hv⟩
      have hvM : v ∈ M.comap j := by rw [ht]; trivial
      change j v = z at hv
      change j v ∈ M at hvM
      rw [hv] at hvM
      exact hvM

/-- A T-invariant irreducible submodule meets the involution-fixed summand nontrivially.
Irreducibility of both submodules then identifies them. -/
lemma unique_frame_first {T : Subgroup G}
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D))
    (s : Three) (hsT : (s,(1 : D)) ∈ c.actorImage T)
    (n : N) (hn : Function.Bijective (frameMap n))
    (hfix : rho s n = n) (hmove : rho s (rho r n) = n + rho r n)
    (M : Submodule F (N ⊗[F] V)) (hM : c.IsIrreducibleFor (component H) M)
    (hMT : c.actorImage T ≤ subspaceStabilizer (sourceTensorAction c.constituent) M) :
    M = Invariant.first n hn := by
  have hfirst := c.frame_first_irreducible hK n hn
  have hi : c.actorImage (component H) ≤
      subspaceStabilizer (sourceTensorAction c.constituent) (M ⊓ Invariant.first n hn) := by
    apply le_subspaceStabilizer
    intro a ha z hz
    exact ⟨(hM.2.1 ha z).mpr hz.1,(hfirst.2.1 ha z).mpr hz.2⟩
  have hnz : M ⊓ Invariant.first n hn ≠ ⊥ := by
    obtain ⟨z,hz,hz0⟩ := M.ne_bot_iff.mp hM.1
    obtain ⟨⟨a,b⟩,rfl⟩ := (pair n hn).surjective z
    by_cases hb : b = 0
    · intro hzero
      have hzinf : pair n hn (a,b) ∈ M ⊓ Invariant.first n hn :=
        ⟨hz,(mem_first n hn a b).mpr hb⟩
      rw [hzero, Submodule.mem_bot] at hzinf
      exact hz0 hzinf
    · have hdm : sourceTensorAction c.constituent (s,1) (pair n hn (a,b)) -
          pair n hn (a,b) ∈ M := M.sub_mem ((hMT hsT _).mpr hz) hz
      have hd : sourceTensorAction c.constituent (s,1) (pair n hn (a,b)) -
          pair n hn (a,b) = pair n hn (b,0) := by
        rw [pair_involution n hn c.constituent s hfix hmove, ← map_sub]
        simp
      rw [hd] at hdm
      intro hzero
      have hzinf : pair n hn (b,0) ∈ M ⊓ Invariant.first n hn := ⟨hdm,⟨b,rfl⟩⟩
      have hzpair : pair n hn (b,0) = pair n hn (0,0) := by
        rw [hzero, Submodule.mem_bot] at hzinf
        change pair n hn (b,0) = pair n hn (0 : V × V)
        rw [map_zero]
        exact hzinf
      exact hb (congrArg Prod.fst ((pair n hn).injective hzpair))
  have hle : M ≤ Invariant.first n hn := by
    have he := (hM.2.2 _ inf_le_left hi).resolve_left hnz
    rw [← he]
    exact inf_le_right
  exact (hfirst.2.2 M hle hM.2.1).resolve_left hM.1

/-- The order-eight source subgroup constructs the unique invariant constituent. -/
lemma EarlierGeometry.exists_selectedConstituent
    {T P : Subgroup G} {g : G} (h : c.EarlierGeometry T P g)
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D)) :
    Nonempty (c.SelectedConstituent T P g) := by
  obtain ⟨s,hs,hs2,hsmem⟩ := h.exists_pure_involution c
  obtain ⟨n,hn,hfix,hmove⟩ := exists_frame s hs2 hs
  have hsT : (s,(1 : D)) ∈ c.actorImage T := c.actorImage_mono h.conjugate_le_T hsmem
  obtain ⟨x,hx,he⟩ := hsmem
  change c.actor x = (s,1) at he
  have hinv : c.actorImage T ≤
      subspaceStabilizer (sourceTensorAction c.constituent) (Invariant.first n hn) := by
    apply le_subspaceStabilizer
    intro a ha z hz
    apply (fixed_iff n hn c.constituent s hfix hmove _).mp
    have hc : (s,(1 : D)) * a = a * (s,1) := by
      apply Prod.ext
      · exact (first_coordinates_commute (c.actorImage T) (h.actor_pgroup c) _ _ hsT ha).eq
      · simp
    rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply,
      (fixed_iff n hn c.constituent s hfix hmove z).mpr hz]
  refine ⟨{
    element := x
    element_mem := hx
    element_ne_one := ?_
    element_centralizes := ?_
    firstSpace := Invariant.first n hn
    secondSpace := Invariant.second n hn
    first_eq_range := ?_
    second_eq_translate := second_translate n hn c.constituent
    isCompl := compl n hn
    first_irreducible := c.frame_first_irreducible hK n hn
    constituentEquiv := firstEquiv n hn
    constituent_equivariant := ?_
    second_invariant := ?_
    T_invariant := hinv
    point_le_fixed := h.point_fixed c
    fixed_le_first := ?_
    unique := fun M hM hMT => c.unique_frame_first hK s hsT n hn hfix hmove M hM hMT
  }⟩
  · intro hx1
    rw [hx1,map_one] at he
    exact hs (congrArg Prod.fst he).symm
  · apply mem_centralizer_iff.mpr
    intro y hy
    apply c.actor.injective
    have hym : c.actor y ∈ c.actorImage (component H) := mem_map_of_mem _ hy
    rw [hK] at hym
    have hy1 : (c.actor y).1 = 1 := hym.1
    simp only [map_mul,he,Prod.ext_iff,Prod.fst_mul,Prod.snd_mul,hy1,one_mul,mul_one,and_self]
  · rw [he]
    exact first_range n hn c.constituent s hfix hmove
  · intro a v
    simp only [firstEquiv_apply,pair_component,map_zero]
  · rw [hK]
    exact (prod_mono le_rfl le_top).trans (second_component_invariant n hn c.constituent)
  · intro z hz
    exact (fixed_iff n hn c.constituent s hfix hmove z).mp (hz ⟨(s,1),hsT⟩)

/-- Apply the constructed constituent to the literal first moved-plane split. -/
lemma EarlierGeometry.exists_selectedConstituent_first_image_split [Finite G]
    {T P : Subgroup G} {g : G} (h : c.EarlierGeometry T P g)
    (hK : c.actorImage (component H) = (⊥ : Subgroup Three).prod (AltFive.subgroupOf D)) :
    ∃ s : c.SelectedConstituent T P g,
      c.image (movedSpace P (Tensor.first H)) = c.image P ⊔
        (c.image (movedSpace P (Tensor.first H)) ⊓ s.secondSpace) := by
  obtain ⟨s⟩ := h.exists_selectedConstituent c hK
  exact ⟨s,s.first_image_split c h⟩

end CaseFiveCoordinates
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor

end
