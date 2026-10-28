module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingSevenFixed
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
import all CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
public import Theory.Representation.BinaryPermutation.SevenNormalizer

/-!
# Whole-module coordinates for an ordinary A₇ block

The vanishing fixed layer identifies the actual U(L) with its module quotient.
At odd degree the natural module is the augmentation core. Conjugation on the
marked L/O₂(L) induces a seven-letter actor for every automorphism of L; the
trivial linear centralizer of A₇ makes that same actor equivariant on all of
U(L). Its restriction to inner automorphisms retains the chosen quotient map.

The private import is an intentional proof extension of AutomorphismAction:
it compares its actor with the literal quotient map. The public statement
uses only the quotient isomorphism and the characteristic module action.

Source application: Aschbacher--Smith, original14.6.10(5), printed p.1029;
permutation-module conventions are those of §B.3 (combined manuscript,
1 March 2004).
-/

public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L]

/-- The whole ordinary block module and its automorphism action have compatible
seven-letter coordinates, with the literal O₂-quotient marking on inner actors. -/
theorem IsAlternatingBlock.seven_automorphism_coordinates (h : IsAlternatingBlock L 7) :
    ∃ q : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7),
    ∃ E : blockU L ≃* Multiplicative (core (Fin 7)),
    ∃ f : MulAut L →* Equiv.Perm (Fin 7),
      (∀ l : L, f (MulAut.conj l) = (q (QuotientGroup.mk' (pCore 2 L) l)).val) ∧
      ∀ a u, (E (MulAut.characteristic (blockU L) a u)).toAdd =
        coreRepresentation (Fin 7) (f a) (E u).toAdd := by
  classical
  obtain ⟨r, ⟨m⟩, hm⟩ := h.2.2
  let t := coreEquivNatural (Fin 7) (by decide)
  let p : blockU L ≃* BlockModule L := MulEquiv.ofBijective
    (QuotientGroup.mk' (blockFixed L))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by
      rw [QuotientGroup.ker_mk', h.seven_fixed_eq_bot]), QuotientGroup.mk'_surjective _⟩
  let E : blockU L ≃* Multiplicative (core (Fin 7)) :=
    (p.trans m.moduleIso).trans t.symm.toAddEquiv.toMultiplicative
  have hq (u : blockU L) : t (E u).toAdd =
      (m.moduleIso (QuotientGroup.mk' (blockFixed L) u)).toAdd :=
    t.apply_symm_apply _
  have hE (l : L) (u : blockU L) :
      (E (blockConjugate L l u)).toAdd =
        coreRepresentation (Fin 7) (m.actor l).val (E u).toAdd := by
    apply t.injective
    rw [hq, coreEquivNatural_equivariant, hq, m.intertwining, hm]
    rfl
  let f : MulAut L →* Equiv.Perm (Fin 7) :=
    SevenNormalizer.permutationOfAut.toMonoidHom.comp m.quotientAction
  have hf (l : L) : f (MulAut.conj l) = (m.actor l).val := by
    have he : m.quotientAction (MulAut.conj l) = MulAut.conj (m.actor l) := by
      ext g
      obtain ⟨k, rfl⟩ := m.actor_surjective g
      rw [m.quotientAction_actor]
      simp only [MulAut.conj_apply, map_mul, map_inv]
    change SevenNormalizer.permutationOfAut (m.quotientAction (MulAut.conj l)) = _
    rw [he, SevenNormalizer.permutationOfAut_conj]
  refine ⟨m.quotientIso, E, f, hf, ?_⟩
  intro a u
  let δ : MulAut (Multiplicative (core (Fin 7))) :=
    (MulAut.congr E) (MulAut.characteristic (blockU L) a)
  let F : core (Fin 7) ≃ₗ[ZMod 2] core (Fin 7) :=
    { AddEquiv.toMultiplicative.symm δ with
      map_smul' := fun c v => ZMod.map_smul (AddEquiv.toMultiplicative.symm δ) c v }
  have hF (v : blockU L) : F (E v).toAdd =
      (E (MulAut.characteristic (blockU L) a v)).toAdd := by
    change (E (MulAut.characteristic (blockU L) a (E.symm (E v)))).toAdd = _
    rw [E.symm_apply_apply]
  have hc (g : alternatingGroup (Fin 7)) (v : core (Fin 7)) :
      F (coreRepresentation (Fin 7) g.val v) =
        coreRepresentation (Fin 7) (m.quotientAction a g).val (F v) := by
    obtain ⟨l, rfl⟩ := m.actor_surjective g
    obtain ⟨w, hw⟩ := E.surjective (Multiplicative.ofAdd v)
    have hv : (E w).toAdd = v := congrArg Multiplicative.toAdd hw
    rw [← hv, m.quotientAction_actor, ← hE, hF, hF]
    have he : MulAut.characteristic (blockU L) a (blockConjugate L l w) =
        blockConjugate L (a l) (MulAut.characteristic (blockU L) a w) := by
      apply Subtype.ext
      change a (l * (w : L) * l⁻¹) = a l * a (w : L) * (a l)⁻¹
      simp only [map_mul, map_inv]
    rw [he, hE]
  exact (hF u).symm.trans (SevenNormalizer.intertwiner F (m.quotientAction a) hc (E u).toAdd)
end CFSG.Quasithin.ChapterC
