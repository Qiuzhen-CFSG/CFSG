module
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Subgroup.Centralizer
/-!
# Lifting lower-central geometry while retaining a central kernel

Let L be normal and let K lie in L. Suppose a homomorphism maps S and
S intersect L onto the same group. If its kernel in L lies in the center
of S, an invariant lower-central term of the image lifts to the join of
the corresponding term of S and its center. Commutators with K lie in L;
matching their quotient images leaves precisely the retained central kernel.
The lifted join is characteristic in the original full S.

This elementary lifting argument is used for the Rudvalis characteristic
subgroup in Aschbacher--Smith 15.1.22, printed p.1100. It requires neither
a splitting of the central cover nor a classification of MS pairs.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory
variable {G D : Type*} [Group G] [Group D]

/-- A lower-central term, saturated by the Sylow center, lifts invariant
quotient geometry through a retained central kernel. -/
theorem lowerCentral_center_normalized
    (S L K : Subgroup G) [L.Normal] (f : G →* D) (n : ℕ)
    (hKL : K ≤ L)
    (himage : (S ⊓ L).map f = S.map f)
    (hkernel : L ⊓ f.ker ≤ (center S).map S.subtype)
    (hcenter : ((center S).map S.subtype).map f ≤ (S.map f).lowerCentralSeries n)
    (hn : K.map f ≤ normalizer ((S.map f).lowerCentralSeries n : Set D)) :
    K ≤ normalizer
      (((((⊤ : Subgroup S).lowerCentralSeries n) ⊔ center S).map S.subtype) : Set G) := by
  let C := (((⊤ : Subgroup S).lowerCentralSeries n) ⊔ center S).map S.subtype
  have hC : C = S.lowerCentralSeries n ⊔ (center S).map S.subtype := by
    dsimp only [C]
    rw [Subgroup.map_sup, top_subtype_lowerCentralSeries]
  have hCf : C.map f ≤ (S.map f).lowerCentralSeries n := by
    rw [hC, Subgroup.map_sup, map_lowerCentralSeries]
    exact sup_le le_rfl hcenter
  have hpre : L ⊓ ((S.map f).lowerCentralSeries n).comap f ≤ C := by
    rintro x ⟨hxL,hxf⟩
    have he : ((S ⊓ L).lowerCentralSeries n).map f = (S.map f).lowerCentralSeries n := by
      rw [map_lowerCentralSeries,himage]
    obtain ⟨y,hy,hyf⟩ := he.symm ▸ hxf
    have hySL : y ∈ S ⊓ L := (Subgroup.lowerCentralSeries_antitone _ (Nat.zero_le n)) hy
    have hc : x * y⁻¹ ∈ (center S).map S.subtype := hkernel
      ⟨L.mul_mem hxL (L.inv_mem hySL.2),by
        change f (x * y⁻¹) = 1
        rw [map_mul,map_inv,hyf,mul_inv_cancel]⟩
    have hym : y ∈ S.lowerCentralSeries n := by
      have hmono : ∀ k, (S ⊓ L).lowerCentralSeries k ≤ S.lowerCentralSeries k := by
        intro k
        induction k with
        | zero => exact inf_le_left
        | succ k ih => exact commutator_mono ih inf_le_left
      exact hmono n hy
    rw [hC]
    simpa only [inv_mul_cancel_right] using
      (S.lowerCentralSeries n ⊔ (center S).map S.subtype).mul_mem
        ((show (center S).map S.subtype ≤ S.lowerCentralSeries n ⊔ (center S).map S.subtype from le_sup_right) hc)
        ((show S.lowerCentralSeries n ≤ S.lowerCentralSeries n ⊔ (center S).map S.subtype from le_sup_left) hym)
  apply le_normalizer_iff_commutator_le_right.mpr
  apply commutator_le.mpr
  intro k hk c hc
  apply hpre
  refine ⟨commutator_le_left L ⊤ (commutator_mem_commutator (hKL hk) (mem_top c)),?_⟩
  change f ⁅k,c⁆ ∈ (S.map f).lowerCentralSeries n
  rw [map_commutatorElement]
  exact (le_normalizer_iff_commutator_le_right.mp hn)
    (commutator_mem_commutator (mem_map_of_mem f hk) (hCf (mem_map_of_mem f hc)))

/-- The normalized lift is a nontrivial characteristic subgroup of the full S
whenever the quotient lower-central term is nontrivial. -/
theorem exists_characteristic_lowerCentral_center
    (S L K : Subgroup G) [L.Normal] (f : G →* D) (n : ℕ)
    (hKL : K ≤ L)
    (himage : (S ⊓ L).map f = S.map f)
    (hkernel : L ⊓ f.ker ≤ (center S).map S.subtype)
    (hcenter : ((center S).map S.subtype).map f ≤ (S.map f).lowerCentralSeries n)
    (hn : K.map f ≤ normalizer ((S.map f).lowerCentralSeries n : Set D))
    (hne : (S.map f).lowerCentralSeries n ≠ ⊥) :
    ∃ C : Subgroup S, C.Characteristic ∧ C ≠ ⊥ ∧
      K ≤ normalizer (C.map S.subtype : Set G) := by
  refine ⟨(⊤ : Subgroup S).lowerCentralSeries n ⊔ center S, inferInstance, ?_,
    lowerCentral_center_normalized S L K f n hKL himage hkernel hcenter hn⟩
  intro he
  apply hne
  have hb : (⊤ : Subgroup S).lowerCentralSeries n = ⊥ :=
    bot_unique (he ▸ (le_sup_left : (⊤ : Subgroup S).lowerCentralSeries n ≤
      (⊤ : Subgroup S).lowerCentralSeries n ⊔ center S))
  have hm := congrArg (fun A : Subgroup S => (A.map S.subtype).map f) hb
  rw [top_subtype_lowerCentralSeries, map_lowerCentralSeries, Subgroup.map_bot, Subgroup.map_bot] at hm
  exact hm

end Theory.GroupTheory
