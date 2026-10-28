module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.MinusEmbedding
import Mathlib.Tactic.Ring

/-!
# Orthogonal blocks in the actual minus carrier

Separating the last two hyperbolic pairs identifies `Minus.Space F (r + 2)`
with a split four-space and `Minus.Space F r`. The form is the sum of the two
original forms, with the same anisotropic-plane parameter. Independent
isometries extend injectively. Restriction of the two full commutator groups
then gives an injective map to the ambient full commutator group.

These are the covering blocks used by Aschbacher–Smith A.2.17, printed p.39.
The construction works on the defined carriers and does not assume a
comparison between elementary and commutator Omega groups.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix Theory.AlgebraicGroup
namespace ClassicalOrthogonal.Fundamental.MinusCentralizer
open TheoremDRootNormalizer.HigherRanks
variable {F : Type*} [Field F]

/-- Separate the last two hyperbolic pairs from the minus space. -/
def splitCoordinates (r : ℕ) : Minus.Space F (r + 2) ≃ₗ[F]
    VectorD 2 F × Minus.Space F r where
  toFun x := (Sum.elim (fun i => (x.1 (Fin.natAdd r i)).1)
    (fun i => (x.1 (Fin.natAdd r i)).2),
    (fun i => x.1 (Fin.castAdd 2 i), x.2))
  invFun x := (Fin.addCases x.2.1 (fun i => (x.1 (.inl i), x.1 (.inr i))), x.2.2)
  left_inv x := by
    apply Prod.ext
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    · rfl
  right_inv x := by
    apply Prod.ext
    · funext i
      cases i <;> simp
    · apply Prod.ext
      · funext i; simp
      · rfl
  map_add' x y := by
    apply Prod.ext
    · funext i; cases i <;> rfl
    · rfl
  map_smul' a x := by
    apply Prod.ext
    · funext i; cases i <;> rfl
    · rfl

/-- The coordinate splitting is an orthogonal direct sum. -/
theorem splitCoordinates_form (r : ℕ) (a : F) (x : Minus.Space F (r + 2)) :
    Minus.form F (r + 2) a x = formD 2 F (splitCoordinates r x).1 +
      Minus.form F r a (splitCoordinates r x).2 := by
  simp only [Minus.form_apply, formD_apply, Fin.sum_univ_add, splitCoordinates,
    LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr]
  ring

/-- Independent orthogonal actions on the marked four-space and complement. -/
def blockHom (r : ℕ) (a : F) : O 2 F × Minus.Orthogonal F (Minus.Space F r)
    (Minus.form F r a) →* Minus.Orthogonal F (Minus.Space F (r + 2))
      (Minus.form F (r + 2) a) where
  toFun g := ⟨(splitCoordinates r).trans
    ((LinearEquiv.prodCongr g.1.val g.2.val).trans (splitCoordinates r).symm),
    (mem_quadraticIsometrySubgroup _ _).mpr (by
      intro x
      rw [splitCoordinates_form, splitCoordinates_form]
      change formD 2 F ((splitCoordinates r) ((splitCoordinates r).symm
        (g.1.val (splitCoordinates r x).1, g.2.val (splitCoordinates r x).2))).1 +
        Minus.form F r a ((splitCoordinates r) ((splitCoordinates r).symm
        (g.1.val (splitCoordinates r x).1, g.2.val (splitCoordinates r x).2))).2 = _
      rw [LinearEquiv.apply_symm_apply]
      rw [(mem_quadraticIsometrySubgroup _ _).mp g.1.property,
        (mem_quadraticIsometrySubgroup _ _).mp g.2.property])⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact (splitCoordinates r).symm_apply_apply x
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change (splitCoordinates r).symm
      (g.1.val (h.1.val (splitCoordinates r x).1),
        g.2.val (h.2.val (splitCoordinates r x).2)) =
      (splitCoordinates r).symm
      (g.1.val ((splitCoordinates r) ((splitCoordinates r).symm
        (h.1.val (splitCoordinates r x).1, h.2.val (splitCoordinates r x).2))).1,
       g.2.val ((splitCoordinates r) ((splitCoordinates r).symm
        (h.1.val (splitCoordinates r x).1, h.2.val (splitCoordinates r x).2))).2)
    rw [LinearEquiv.apply_symm_apply]

theorem blockHom_coordinates (r : ℕ) (a : F)
    (g : O 2 F × Minus.Orthogonal F (Minus.Space F r) (Minus.form F r a))
    (x : Minus.Space F (r + 2)) :
    splitCoordinates r ((blockHom r a g).val x) =
      (g.1.val (splitCoordinates r x).1, g.2.val (splitCoordinates r x).2) :=
  (splitCoordinates r).apply_symm_apply _

theorem blockHom_injective (r : ℕ) (a : F) : Function.Injective (blockHom r a) := by
  intro g h hgh
  have he (v : VectorD 2 F × Minus.Space F r) :=
    congrArg (fun k : Minus.Orthogonal F (Minus.Space F (r + 2))
      (Minus.form F (r + 2) a) => splitCoordinates r (k.val ((splitCoordinates r).symm v))) hgh
  simp only [blockHom_coordinates, LinearEquiv.apply_symm_apply] at he
  apply Prod.ext
  · apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact congrArg Prod.fst (he (v, 0))
  · apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact congrArg Prod.snd (he (0, v))

/-- Restriction of a homomorphism to the actual derived subgroups. -/
def derivedMap {G H : Type*} [Group G] [Group H] (f : G →* H) :
    commutator G →* commutator H :=
  (f.comp (commutator G).subtype).codRestrict _ (by
    intro g
    have hm : f g.val ∈ (commutator G).map f := Subgroup.mem_map_of_mem _ g.property
    rw [map_commutator_eq] at hm
    exact Subgroup.commutator_mono le_top le_top hm)

/-- The block action of the two full derived groups, before scalar quotient. -/
def derivedBlockHom (r : ℕ) (a : F) :
    commutator (O 2 F) × Minus.Omega F (Minus.Space F r) (Minus.form F r a) →*
      Minus.Omega F (Minus.Space F (r + 2)) (Minus.form F (r + 2) a) :=
  ((blockHom r a).comp
    ((commutator (O 2 F)).subtype.prodMap
      (commutator (Minus.Orthogonal F (Minus.Space F r) (Minus.form F r a))).subtype)).codRestrict _ (by
        intro g
        have h1 := (derivedMap ((blockHom r a).comp (MonoidHom.inl _ _)) g.1).property
        have h2 := (derivedMap ((blockHom r a).comp (MonoidHom.inr _ _)) g.2).property
        have he : (g.1.val, g.2.val) = (g.1.val, 1) * (1, g.2.val) := by simp
        change blockHom r a (g.1.val, g.2.val) ∈ _
        rw [he, map_mul]
        exact Subgroup.mul_mem _ h1 h2)

theorem derivedBlockHom_injective (r : ℕ) (a : F) :
    Function.Injective (derivedBlockHom r a) := by
  intro g h hgh
  have he := blockHom_injective r a (congrArg Subtype.val hgh)
  exact Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Subtype.ext (congrArg Prod.snd he))

end ClassicalOrthogonal.Fundamental.MinusCentralizer
