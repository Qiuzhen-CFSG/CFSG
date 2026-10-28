module

public import CFSG.Quasithin.ChapterG.Section07.AlternatingSevenCover.LocalStructure
public import CFSG.Quasithin.ChapterG.Section07.AlternatingSevenCover.Nonembedding
public import CFSG.Quasithin.ChapterG.Section07.AlternatingSevenCover.ScalarField
public import CFSG.Quasithin.ChapterG.Section07.CoprimeDegrees

/-!
# Excluding small binary representations of the genuine triple cover of A₇

For a finite quasisimple L with center of order three and an actual equivalence
L/Z(L) ≃ A₇, a Sylow three-subgroup P is extraspecial of order 27 and has the
same center as L. On a faithful irreducible binary module the central fixed
space vanishes. The exact extraspecial degree theorem, through semisimple
restriction to P, therefore makes the binary dimension divisible by six.

A positive dimension at most eight is consequently six. The central order-three
action supplies a field of four scalars and a faithful action of dimension three;
perfectness puts it in SL₃(4). The order-five normalizer calculation excludes
that embedding. The imported local-structure module also proves the
three upper bound for the automorphism two-ranks of A₇ and its covers.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, G.7.3(3),
printed pp.348–349 (PDF pp.359–360, combined 1 March 2004 manuscript).
The simple A₇ case and the assembly for the ambient generalized Fitting
subgroup belong to the source-section owner.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section07.AlternatingSevenCover

open Subgroup Theory.GroupTheory

variable {L V : Type*} [Group L] [Finite L] [IsQuasisimple L]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Vanishing of the Sylow-center fixed space forces divisibility by six. -/
theorem six_dvd_dimension
    (e : (L ⧸ center L) ≃* alternatingGroup (Fin 7)) (hz : Nat.card (center L) = 3)
    (rho : Representation (ZMod 2) L V) [rho.IsIrreducible]
    (hfaith : Function.Injective rho) : 6 ∣ Module.finrank (ZMod 2) V := by
  let P : Sylow 3 L := Classical.choice inferInstance
  have hP := sylow_three_structure e hz P
  let : IsExtraspecial 3 (P : Subgroup L) := hP.2.1
  exact Representation.BinaryCoprimeDegree.six_dvd_finrank_of_extraspecial_twentySeven
    (rho.comp (P : Subgroup L).subtype) hP.1
    (sylow_center_invariants_eq_bot e hz P rho hfaith)

/-- In the source's range `d ≤ 8`, divisibility and nontriviality force `d = 6`. -/
theorem dimension_eq_six_of_le_eight
    (e : (L ⧸ center L) ≃* alternatingGroup (Fin 7)) (hz : Nat.card (center L) = 3)
    (rho : Representation (ZMod 2) L V) [rho.IsIrreducible]
    (hfaith : Function.Injective rho) (hdim : Module.finrank (ZMod 2) V ≤ 8) :
    Module.finrank (ZMod 2) V = 6 := by
  have hdiv := six_dvd_dimension e hz rho hfaith
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial rho
  have hpos := Module.finrank_pos (R := ZMod 2) (M := V)
  omega

/-- The genuine triple cover of A₇ has no faithful irreducible binary module
of dimension at most eight, as required at the end of G.7.3. -/
theorem no_small_faithful_binary_representation
    (e : (L ⧸ center L) ≃* alternatingGroup (Fin 7)) (hz : Nat.card (center L) = 3)
    (rho : Representation (ZMod 2) L V) [rho.IsIrreducible]
    (hfaith : Function.Injective rho) (hdim : Module.finrank (ZMod 2) V ≤ 8) : False := by
  have hd := dimension_eq_six_of_le_eight e hz rho hfaith hdim
  obtain ⟨S⟩ := exists_four_field_realization rho hfaith hz hd
  let : CharP S.Scalar 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) S.Scalar).injective 2
  obtain ⟨j, hj⟩ := S.embeds_sl3 hfaith
  exact not_embeds_sl3 (projection e) (projection_surjective e)
    ((projection_ker e).le) (by rw [projection_ker e]; exact hz) j hj

end CFSG.Quasithin.ChapterG.Section07.AlternatingSevenCover
