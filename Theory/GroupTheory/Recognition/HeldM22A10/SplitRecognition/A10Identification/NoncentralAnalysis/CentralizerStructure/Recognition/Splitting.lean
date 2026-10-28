module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.Lift
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.NoEight
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Core
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Section
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Commutator.CentralDihedralExponentFour

/-!
# Splitting the derived subgroup of Held's inverse-image core

The inverse image J of the supplied quotient core has central kernel of
order two. Its Sylow two-subgroups have exponent dividing four, since
they embed in Sylow subgroups of C, all isomorphic to the known P.
Their images in the quotient core are isomorphic to its specified D8.
The dihedral-cover calculation and central Sylow transfer therefore show
that the kernel misses the intrinsic derived subgroup of J.

Consequently the published restricted quotient map `derivedMap` is injective.
The explicit perfectness input is discharged by the separate recognition
argument; combined with `derivedMap_surjective`, it identifies the derived
lift with the quotient core and splits the central extension. This module
assumes no complement, splitting, or model recognition.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, proof of Lemma 4.2, p.234.
-/

open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
universe u
variable {G : Type u} [Group G] [Finite G] {D : LocalData G}
  {e : D.centralizer ≃* CentralizerModels.a10Centralizer}

namespace QuotientCore
variable (c : QuotientCore D e)

private theorem sylow_lift_pow_four
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (S : Sylow 2 c.lift) (x : S) : x ^ 4 = 1 := by
  obtain ⟨T, hT⟩ := (S.isPGroup'.map c.lift.subtype).exists_le_sylow
  obtain ⟨U, hU⟩ := exists_sylow_eq_P D e hfusion
  let f : T ≃* P D e := (T.equiv U).trans (MulEquiv.subgroupCongr hU)
  let tx : T := ⟨x.1.1, hT (mem_map_of_mem c.lift.subtype x.property)⟩
  have ht : tx ^ 4 = 1 := by
    apply f.injective
    rw [map_pow, map_one]
    exact P_pow_four D e (f tx)
  have hx4 : (x.1.1 : C D e) ^ 4 = 1 :=
    congrArg (fun y : T => (y : C D e)) ht
  exact Subtype.ext (Subtype.ext hx4)

private theorem kernel_inf_commutator_eq_bot
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) :
    c.liftMap.ker ⊓ _root_.commutator c.lift = ⊥ := by
  let S : Sylow 2 c.lift := Classical.choice Sylow.nonempty
  let f : Sylow.mapSurjective c.liftMap_surjective S ≃* DihedralGroup 4 :=
    ((Sylow.mapSurjective c.liftMap_surjective S).equiv c.sylow).trans c.sylowEquiv
  exact CentralExtension.ker_inf_commutator_eq_bot_of_dihedral_four_sylow
    c.liftMap c.liftMap_surjective
    (by rw [c.ker_liftMap]; exact c.liftKernel_le_center)
    (by rw [c.ker_liftMap]; exact c.liftKernel_card)
    S f (c.sylow_lift_pow_four hfusion S)

/-- The intrinsic derived subgroup of the actual lift maps injectively to
Held's quotient core. Together with perfectness and `derivedMap_surjective`,
this supplies the central-extension splitting. -/
public theorem derivedMap_injective
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    [Group.IsPerfect c.subgroup] : Function.Injective c.derivedMap := by
  have hker := c.kernel_inf_commutator_eq_bot hfusion
  apply c.derivedMap.ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro x hx
  have hder : x.1 ∈ (_root_.commutator c.lift).map c.lift.subtype := x.property
  obtain ⟨y, hy, hyx⟩ := hder
  change (y : C D e) = x.1 at hyx
  have hyker : y ∈ c.liftMap.ker := by
    change c.liftMap y = 1
    apply Subtype.ext
    change q D e (y : C D e) = 1
    rw [hyx]
    exact congrArg Subtype.val (show c.derivedMap x = 1 from hx)
  have hyone : y = 1 := by
    have hmem : y ∈ c.liftMap.ker ⊓ _root_.commutator c.lift := ⟨hyker, hy⟩
    rwa [hker, mem_bot] at hmem
  apply Subtype.ext
  exact hyx.symm.trans (congrArg Subtype.val hyone)

end QuotientCore
end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
