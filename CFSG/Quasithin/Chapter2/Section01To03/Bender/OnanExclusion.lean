module

public import CFSG.Quasithin.GoldschmidtONan
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ExceptionalExclusion
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.FusionIndexTwo
public import Mathlib.RepresentationTheory.Irreducible

/-!
# The complete Goldschmidt–O'Nan contradiction in the Bender reduction

The source's selected U has no proper nontrivial M-invariant subgroup.
The order isomorphism between binary submodules and subgroups therefore
proves that its actual faithful image representation is irreducible.

Apply the unconditional Goldschmidt–O'Nan theorem to any actor Y in that
image satisfying its genuine geometric hypotheses. Irreducibility removes
the invariant-space cases. Binary transfer excludes the swapped case,
and the distinguished z/u centralizer difference excludes the order-21
case. There is no Alternatives, irreducibility, recognition or transfer
premise left in the source consumer.

Source: Aschbacher–Smith, Proposition 2.2.2, printed pp.519–520.
The remaining component argument must construct the actual GO Input from
the image of N_L(U)=L∩M, including its cyclic actor and TI fixed-space orbit.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.BenderFusion

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {M : Subgroup G}
  (w : LocalControlWitness T M) [IsElementaryAbelian 2 w.U]

omit [Finite G] in
/-- Irreducibility of the actual image representation follows from the
already constructed minimal normal subgroup, with no representation premise. -/
theorem sourceImageRepresentation_irreducible :
    Representation.IsIrreducible (sourceImageRepresentation w) := by
  let : Nontrivial w.U := w.U.nontrivial_iff_ne_bot.mpr w.ne_bot
  let e : Submodule (ZMod 2) (Additive w.U) ≃o Subgroup w.U :=
    (AddSubgroup.toZModSubmodule 2).symm.trans AddSubgroup.toSubgroup'
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  constructor
  · refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro he
    have hh : (⊥ : Submodule (ZMod 2) (Additive w.U)) = ⊤ :=
      congrArg Subrepresentation.toSubmodule he
    exact bot_ne_top hh
  · intro S
    let W : Subgroup w.U := e S.toSubmodule
    have hW : ∀ m : M, ∀ v : w.U, v ∈ W →
        conjugationAction M w.U w.normalizes m v ∈ W := by
      intro m v hv
      exact S.apply_mem_toSubmodule
        ((conjugationAction M w.U w.normalizes).rangeRestrict m) hv
    rcases w.irreducible W hW with hb | ht
    · left
      apply Subrepresentation.toSubmodule_injective
      apply e.injective
      change e S.toSubmodule = e (⊥ : Submodule (ZMod 2) (Additive w.U))
      rw [e.map_bot]
      exact hb
    · right
      apply Subrepresentation.toSubmodule_injective
      apply e.injective
      change e S.toSubmodule = e (⊤ : Submodule (ZMod 2) (Additive w.U))
      rw [e.map_top]
      exact ht

omit [IsElementaryAbelian 2 w.U] in
/-- The source's bad-centralizer witness rules out a GO pair on the actual
image of M. Only the component/TI/cyclic-actor construction remains to
supply Input; all subsequent classification alternatives are discharged. -/
theorem LocalControlWitness.not_onanInput_of_bad_centralizer
    {C : GroupClass.{u}} (hG : IsSimpleQTKE C G)
    (hTM : (T : Subgroup G) ≤ M)
    (hbad : ∃ u ∈ w.U, u ≠ 1 ∧ ¬ centralizer ({u} : Set G) ≤ M)
    (Y : Subgroup (sourceActionImage w)) :
    let _ : IsElementaryAbelian 2 w.U := w.elementary
    ¬ Representation.GoldschmidtONan.Input (sourceImageRepresentation w) Y := by
  let _ : IsElementaryAbelian 2 w.U := w.elementary
  change ¬ Representation.GoldschmidtONan.Input (sourceImageRepresentation w) Y
  intro hpair
  let _ : IsSimpleGroup G := hG.simple
  let _ : Representation.IsIrreducible (sourceImageRepresentation w) :=
    sourceImageRepresentation_irreducible w
  have hns : ¬ Group.IsSolvable G := fun hs =>
    hG.nonabelian ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr hs⟩⟩
  have halt := CFSG.Quasithin.GoldschmidtONan.alternatives hpair
  rcases hpair.swapped_or_exceptional_of_irreducible halt with hswap | hexceptional
  · obtain ⟨K, _, hK⟩ := hpair.normal_index_two_of_swapped hswap
    exact w.image_index_ne_two hns hTM
      (conjugationAction M w.U w.normalizes).rangeRestrict
      (conjugationAction M w.U w.normalizes).rangeRestrict_surjective K hK
  · exact w.not_exceptional_of_bad_centralizer hbad Y hexceptional

end CFSG.Quasithin.Chapter2.BenderFusion
