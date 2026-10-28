module
public import Theory.Representation.SL2FourCentralCover.Quotients
public import CFSG.Quasithin.ChapterJ.Defs

/-!
# The original section U/V₁ as an image of the universal natural cover

Restrict the actual S₅ marking to its marked alternating subgroup. The
indecomposable central extension in Theorem 14.7.63 is a perfect cover, so
the explicit three-dimensional F₄-cover maps onto the original U/V₁,
compatibly with its natural quotient. The given conjugation section retains
the actual subgroup kernel V₁ and gives the corresponding order bound on U.
The fixed-space/commutator identity and involution displacement dimension are
transported to this same action; no replacement of the actor marking occurs.

Inputs here are precisely module data from 14.7.63: the action on U/V₁,
its natural quotient, fixed kernel, and indecomposability for K*. The
construction of those data belongs to qt-14-07. These are calculations used
inside 14.7.69–70; the critical-pair and fusion arguments establishing the
order of Uα*, b=3, and the later local group structure are still required.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Remark 14.7.64 and Lemmas 14.7.69–70, printed pp.1069, 1072–1074.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure
open Representation Representation.OneCohomology
open Representation.SL2FourNatural

/-- The same alternating marking used by the natural action in Ru2. -/
def alternatingActor (a : ChapterJ.L2FourAction) : SL →* ChapterJ.S5 :=
  (alternatingGroup (Fin 5)).subtype.comp a.marking.toMonoidHom

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) ChapterJ.S5 W}

/-- Restriction of the original natural quotient, without choosing a new marking. -/
def restrictedProjection (a : ChapterJ.L2FourAction) (p : σ.IntertwiningMap a.action) :
    Representation.IntertwiningMap (σ.comp (alternatingActor a)) naturalRepresentation :=
  p.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g w
    exact (LinearMap.congr_fun (p.isIntertwining' (alternatingActor a g)) w).trans
      (a.restriction g (p w)))

/-- Construct the genuine universal-cover surjection onto the original section
and bound its central kernel. The order bound uses the literal subgroup V₁. -/
theorem original_section_cover
    {G : Type*} [Group G] {H U V₁ : Subgroup G}
    [FiniteDimensional (ZMod 2) W]
    (a : ChapterJ.L2FourAction) (qH : H →* ChapterJ.S5)
    (d : BinaryConjugationSection H U V₁ (σ.comp qH))
    (p : σ.IntertwiningMap a.action) (hp : Function.Surjective p)
    (hk : p.toLinearMap.ker ≤ fixed (σ.comp (alternatingActor a)))
    (hi : ∀ A B : Submodule (ZMod 2) W,
      (∀ g v, v ∈ A → σ (alternatingActor a g) v ∈ A) →
      (∀ g v, v ∈ B → σ (alternatingActor a g) v ∈ B) →
      IsCompl A B → A = ⊥ ∨ B = ⊥) :
    ∃ q : SL2FourCentralCover.binaryAction.IntertwiningMap (σ.comp (alternatingActor a)),
      Function.Surjective q ∧
      (∀ w, p (q w) = SL2FourCentralCover.projection w) ∧
      Module.finrank (ZMod 2) p.toLinearMap.ker ≤ 2 ∧
      Nat.card U ≤ 64 * Nat.card V₁ := by
  let P := restrictedProjection a p
  have hP : IsCover P := SL2FourCentralCover.isCover_of_natural_indecomposable P hp hk hi
  obtain ⟨q, hq, hc⟩ := SL2FourCentralCover.exists_quotient P hP
  refine ⟨q, hq, hc, SL2FourCentralCover.kernel_finrank_le_two P hP, ?_⟩
  have hd := (SL2FourCentralCover.finrank_bounds P hP).2
  have hcard : Nat.card W ≤ 64 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card] at h
    rw [h]
    exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hd).trans_eq (by decide)
  rw [d.card_section]
  exact Nat.mul_le_mul_right _ hcard

/-- The module identity 14.7.69(a) on the original marked section. This does
not assume the subsequent order-two conclusion for the critical actor. -/
theorem original_section_upper_moved_eq_fixed
    [FiniteDimensional (ZMod 2) W]
    (a : ChapterJ.L2FourAction) (p : σ.IntertwiningMap a.action)
    (hp : Function.Surjective p)
    (hk : p.toLinearMap.ker ≤ fixed (σ.comp (alternatingActor a)))
    (hi : ∀ A B : Submodule (ZMod 2) W,
      (∀ g v, v ∈ A → σ (alternatingActor a g) v ∈ A) →
      (∀ g v, v ∈ B → σ (alternatingActor a g) v ∈ B) →
      IsCompl A B → A = ⊥ ∨ B = ⊥) :
    SL2CentralExtension.movedSpace (σ.comp (alternatingActor a))
      (Matrix.SpecialLinearGroup.upperUnipotent F) ⊤ =
      SL2CentralExtension.upperFixed (σ.comp (alternatingActor a)) := by
  let P := restrictedProjection a p
  exact SL2FourCentralCover.quotient_upper_moved_eq_fixed P
    (SL2FourCentralCover.isCover_of_natural_indecomposable P hp hk hi)

/-- The rank-two displacement used in 14.7.70, with the original S₅ action
and the very same alternating marking as its natural quotient. -/
theorem original_section_upper_displacement_finrank
    [FiniteDimensional (ZMod 2) W]
    (a : ChapterJ.L2FourAction) (p : σ.IntertwiningMap a.action)
    (hp : Function.Surjective p)
    (hk : p.toLinearMap.ker ≤ fixed (σ.comp (alternatingActor a)))
    (hi : ∀ A B : Submodule (ZMod 2) W,
      (∀ g v, v ∈ A → σ (alternatingActor a g) v ∈ A) →
      (∀ g v, v ∈ B → σ (alternatingActor a g) v ∈ B) →
      IsCompl A B → A = ⊥ ∨ B = ⊥)
    (t : F) (ht : t ≠ 0) :
    Module.finrank (ZMod 2)
      (σ (alternatingActor a (upper t)) - LinearMap.id).range = 2 := by
  let P := restrictedProjection a p
  exact SL2FourCentralCover.quotient_upper_displacement_finrank P
    (SL2FourCentralCover.isCover_of_natural_indecomposable P hp hk hi) t ht

/-- The original marked upper commutator is a complement to the K-fixed
kernel inside the upper fixed space, as used in 14.7.70. -/
theorem original_section_upper_complement
    (a : ChapterJ.L2FourAction) (p : σ.IntertwiningMap a.action)
    (hp : Function.Surjective p)
    (hk : p.toLinearMap.ker ≤ fixed (σ.comp (alternatingActor a)))
    (hi : ∀ A B : Submodule (ZMod 2) W,
      (∀ g v, v ∈ A → σ (alternatingActor a g) v ∈ A) →
      (∀ g v, v ∈ B → σ (alternatingActor a g) v ∈ B) →
      IsCompl A B → A = ⊥ ∨ B = ⊥)
    (t : F) (ht : t ≠ 0) :
    Disjoint (σ (alternatingActor a (upper t)) - LinearMap.id).range p.toLinearMap.ker ∧
      SL2CentralExtension.upperFixed (σ.comp (alternatingActor a)) =
        (σ (alternatingActor a (upper t)) - LinearMap.id).range ⊔ p.toLinearMap.ker := by
  let P := restrictedProjection a p
  exact SL2FourCentralCover.quotient_upper_complement P
    (SL2FourCentralCover.isCover_of_natural_indecomposable P hp hk hi) t ht

end CFSG.Quasithin.Chapter14.Section07.LocalStructure
