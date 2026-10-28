module

public import Theory.Mathieu.M24.ChapterHStabilizers.TrioAction.Kernel
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.Transport
public import Theory.GroupTheory.SylowKernelCore

/-!
# Native geometric transport of the trio core

An actual M24 conjugator carries the standard octad partition to every trio.
Functoriality of the intrinsic two-core under the corresponding stabilizer
isomorphism identifies the mapped cores. Thus the elementary structure and
order 64 hold for every geometric trio, with no ambient normality assumption.

Source: Aschbacher–Smith, the marking preceding H.14.1 and part (3),
printed pp.396–397.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open MathieuCode.TrioCalculation
open scoped Pointwise
namespace Sporadic.Mathieu.M24ChapterHStabilizers.TrioAction
noncomputable section

def coreAt (T : Trio) : Subgroup M24 :=
  (pCore 2 (trioStabilizer T)).map (trioStabilizer T).subtype

lemma stabilizer_map {T : Trio} (g : M24) (hg : g • standardTrio.parts = T.parts) :
    Stabilizer.map (MulAut.conj g).toMonoidHom = trioStabilizer T := by
  rw [← conjugateTrioStabilizer_eq_map]
  change MulAction.stabilizer M24 (g • standardTrio.parts) =
    MulAction.stabilizer M24 T.parts
  rw [hg]

lemma core_map {T : Trio} (g : M24) (hg : g • standardTrio.parts = T.parts) :
    core.map (MulAut.conj g).toMonoidHom = coreAt T := by
  change (Stabilizer.pCoreIn 2).map _ = (trioStabilizer T).pCoreIn 2
  rw [Subgroup.map_pCoreIn_of_injective 2 Stabilizer _ (MulAut.conj g).injective,
    stabilizer_map g hg]

lemma exists_core_conjugator (T : Trio) : ∃ g : M24,
    g • standardTrio.parts = T.parts ∧
      core.map (MulAut.conj g).toMonoidHom = coreAt T := by
  obtain ⟨g, hg⟩ := exists_smul_standardTrio T
  exact ⟨g, hg, core_map g hg⟩

lemma coreAt_card (T : Trio) : Nat.card (coreAt T) = 64 := by
  obtain ⟨g, _, hg⟩ := exists_core_conjugator T
  rw [← hg, Subgroup.card_map_of_injective (MulAut.conj g).injective, core_ambient_card]

lemma coreAt_elementary (T : Trio) : IsElementaryAbelian 2 (coreAt T) := by
  obtain ⟨g, _, hg⟩ := exists_core_conjugator T
  let := core_ambient_elementary
  rw [← hg]
  exact IsElementaryAbelian.map _

end
end Sporadic.Mathieu.M24ChapterHStabilizers.TrioAction
