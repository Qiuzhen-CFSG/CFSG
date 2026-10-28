module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupLocalImage

/-!
# The marked old local image inside the offender actor

The literal component image embeds in the offender subgroup. Its canonical
subgroup equivalence carries the old A₅ image and its full Sylow marking to
the exact actor used by the source B.5 classification. Properness, the two-core
quotient and local C-component membership are all preserved.

Source: Aschbacher–Smith 9.3.7, printed p.734, and B.5.1, printed pp.99–103.
The component containment is supplied by the original Thompson-movement route.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open ChapterB.InternalThompsonAction ChapterA.Section03
open Representation Representation.BinaryOffender
variable {H : Type*} [Group H] [Finite H]

theorem source_tensor_local_image_in_offender
    (K W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (hKN : K.map (actionMk W) ≤ offenderSubgroup (action W))
    (R : Sylow 2 (K.map (actionMk W)))
    (B : Subgroup (K.map (actionMk W)))
    (hB : B ∈ localCComponents R) (hp : B < ⊤)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    let i := (subgroupOfEquivOfLe hKN).symm
    let C := B.map i.toMonoidHom
    C < ⊤ ∧ Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) ∧
      C ∈ localCComponents (R.mapSurjective (f := i.toMonoidHom) i.surjective) := by
  let i := (subgroupOfEquivOfLe hKN).symm
  let C := B.map i.toMonoidHom
  have hproper : C < ⊤ := lt_top_iff_ne_top.mpr (fun he => hp.ne (by
    apply map_injective (f := i.toMonoidHom) i.injective
    exact he.trans (map_top_of_surjective i.toMonoidHom i.surjective).symm))
  let b : B ≃* C := B.equivMapOfInjective i.toMonoidHom i.injective
  let eC : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ b.symm (pCore_map_iso 2 b.symm)).trans eB
  let : Group.IsSolvable i.toMonoidHom.ker := by
    rw [i.toMonoidHom.ker_eq_bot_iff.mpr i.injective]
    infer_instance
  have hc := Chapter1.Section02.localCComponents_map_of_solvable_ker hB i.toMonoidHom
  refine ⟨hproper,⟨eC⟩,?_⟩
  change C ∈ localCComponents ((R : Subgroup (K.map (actionMk W))).map i.toMonoidHom)
  exact hc
end CFSG.Quasithin.Chapter10
