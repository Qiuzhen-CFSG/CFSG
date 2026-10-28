module

public import Theory.Mathieu.M24.ChapterHStabilizers.TrioAction

/-!
# Tensor conjugation at every native trio

Choose an actual M24 element transporting the standard octad partition. Its
conjugation identifies both stabilizers and their intrinsic mapped cores.
The same stabilizer isomorphism induces the quotient identification, so the
tensor equivalence intertwines conjugation at the new trio with its literal
intrinsic quotient. No geometric transport or action premise remains.

Source: Aschbacher–Smith H.14.1(3) and its preceding marking, printed pp.396–397.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open MathieuCode.TrioCalculation
open scoped Pointwise MatrixGroups
namespace Sporadic.Mathieu.M24ChapterHStabilizers.TrioAction
noncomputable section

def trioConjugator (T : Trio) : M24 := (exists_smul_standardTrio T).choose

lemma trioConjugator_spec (T : Trio) :
    trioConjugator T • standardTrio.parts = T.parts :=
  (exists_smul_standardTrio T).choose_spec

def stabilizerEquivAt (T : Trio) : Stabilizer ≃* trioStabilizer T :=
  MulAction.stabilizerEquivStabilizer (trioConjugator_spec T).symm

lemma stabilizerEquivAt_apply (T : Trio) (g : Stabilizer) :
    (stabilizerEquivAt T g).val =
      trioConjugator T * g.val * (trioConjugator T)⁻¹ :=
  MulAction.stabilizerEquivStabilizer_apply _ _

def coreEquivAt (T : Trio) : core ≃* coreAt T :=
  (core.equivMapOfInjective (MulAut.conj (trioConjugator T)).toMonoidHom
    (MulAut.conj (trioConjugator T)).injective).trans
      (MulEquiv.subgroupCongr (core_map _ (trioConjugator_spec T)))

lemma coreEquivAt_apply (T : Trio) (k : core) :
    (coreEquivAt T k).val = trioConjugator T * k.val * (trioConjugator T)⁻¹ := rfl

/-- Tensor coordinates at an arbitrary native geometric trio. -/
def tensorEquivAt (T : Trio) : Multiplicative NaturalTensor ≃* coreAt T :=
  ambientTensorEquiv.trans (coreEquivAt T)

/-- The quotient by the actual intrinsic core at the same geometric trio. -/
def sourceQuotientEquivAt (T : Trio) :
    (trioStabilizer T ⧸ pCore 2 (trioStabilizer T)) ≃*
      (PSL(3, ZMod 2) × Equiv.Perm (Fin 3)) :=
  (QuotientGroup.congr _ _ (stabilizerEquivAt T).symm
    (pCore_map_iso 2 (stabilizerEquivAt T).symm)).trans standardSourceQuotientEquiv

lemma sourceQuotientEquivAt_mk (T : Trio) (g : trioStabilizer T) :
    sourceQuotientEquivAt T (QuotientGroup.mk g) =
      standardSourceQuotientEquiv (QuotientGroup.mk ((stabilizerEquivAt T).symm g)) := rfl

lemma tensorEquivAt_conjugation (T : Trio) (g : trioStabilizer T) (z : NaturalTensor) :
    g.val * (tensorEquivAt T (Multiplicative.ofAdd z)).val * g.val⁻¹ =
      (tensorEquivAt T (Multiplicative.ofAdd
        (sourceTensorRepresentation (sourceQuotientEquivAt T (QuotientGroup.mk g)) z))).val := by
  let h := (stabilizerEquivAt T).symm g
  have hg : g.val = trioConjugator T * h.val * (trioConjugator T)⁻¹ := by
    rw [← stabilizerEquivAt_apply]
    exact congrArg Subtype.val ((stabilizerEquivAt T).apply_symm_apply g).symm
  rw [sourceQuotientEquivAt_mk]
  change g.val * (coreEquivAt T (ambientTensorEquiv (Multiplicative.ofAdd z))).val * g.val⁻¹ =
    (coreEquivAt T (ambientTensorEquiv (Multiplicative.ofAdd
      (sourceTensorRepresentation (standardSourceQuotientEquiv (QuotientGroup.mk h)) z)))).val
  rw [coreEquivAt_apply, coreEquivAt_apply, hg, ← ambientTensorEquiv_conjugation h z]
  group

end
end Sporadic.Mathieu.M24ChapterHStabilizers.TrioAction
