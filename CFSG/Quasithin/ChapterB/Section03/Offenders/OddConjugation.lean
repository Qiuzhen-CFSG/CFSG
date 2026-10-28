module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.OddParity
public import Theory.Representation.NormalElementaryQuotient.BestOffender

/-!
# Thompson subgroups acting on odd binary cores

Let W be a normal elementary two-subgroup contained in Q, with its actual
conjugation action identified with the binary core on five or seven letters.
If Q acts by even permutations, every maximum elementary subgroup of Q
centralizes W: a nontrivial image would be an offender on the odd core,
contradicting B.3.2(4). Thus the elementary Thompson subgroup lies in the
literal action kernel.

Source: Aschbacher--Smith, B.2.5--7 and B.3.2(4), printed pp.76 and83;
application to preliminary 15.2.23, printed p.1115, refs/quasithin.pdf.
-/

public section
open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterB.Offenders
open Stellmacher Representation Representation.BinaryOffender
variable {A : Type*} [Group A] [Finite A]

theorem thompson_le_kernel_of_even_core_action
    {n : ℕ} (hn : n = 5 ∨ n = 7) (W Q : Subgroup A) [W.Normal] [IsElementaryAbelian 2 W]
    (hWQ : W ≤ Q) (f : A →* Equiv.Perm (Fin n))
    (hker : f.ker = centralizer (W : Set A))
    (E : W ≃* Multiplicative (BinaryPermutation.core (Fin n)))
    (hE : ∀ a w, (E (MulAut.conjNormal a w)).toAdd =
      BinaryPermutation.coreRepresentation (Fin n) (f a) (E w).toAdd)
    (heven : Q.map f ≤ alternatingGroup (Fin n)) :
    elementaryAbelianMaxJ Q ≤ f.ker := by
  let q := f.rangeRestrict
  have hq : Function.Surjective q := f.rangeRestrict_surjective
  have hk : q.ker = centralizer (W : Set A) := by
    rw [MonoidHom.ker_rangeRestrict,hker]
  let ρ := NormalElementaryQuotient.representation W q hq hk
  let e : Additive W ≃ₗ[ZMod 2] BinaryPermutation.core (Fin n) :=
    LinearEquiv.ofBijective (E.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) E.bijective
  have he (a : f.range) (w : Additive W) :
      e (ρ a w) = BinaryPermutation.coreRepresentation (Fin n) a.val (e w) := by
    obtain ⟨a,rfl⟩ := hq a
    have hconj : (ρ (q a) w).toMul = MulAut.conjNormal a w.toMul :=
      Subtype.ext (NormalElementaryQuotient.representation_apply W q hq hk a w)
    change (E (ρ (q a) w).toMul).toAdd =
      BinaryPermutation.coreRepresentation (Fin n) (f a) (E w.toMul).toAdd
    rw [hconj,hE]
  apply sSup_le
  intro B hB
  apply (map_eq_bot_iff B).mp
  by_contra hne
  have hne' : B.map q ≠ ⊥ := by
    intro hb
    apply hne
    have hm := congrArg (map f.range.subtype) hb
    simpa only [q,map_map,Subgroup.map_bot,MonoidHom.subtype_comp_rangeRestrict] using hm
  have hoff := Representation.NormalElementaryQuotient.maxElementary_isBestOffender
    W q hq hk Q B hWQ hB hne'
  have ho := (hoff.isOffender ρ).map_equivariant ρ
    (BinaryPermutation.coreRepresentation (Fin n)) f.range.subtype
    f.range.subtype_injective e he
  apply core_offender_not_le_alternating hn ho
  have hm : (B.map q).map f.range.subtype = B.map f := by
    rw [map_map,MonoidHom.subtype_comp_rangeRestrict]
  rw [hm]
  exact (map_mono hB.1).trans heven
end CFSG.Quasithin.ChapterB.Offenders
