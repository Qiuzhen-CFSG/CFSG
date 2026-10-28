module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.NormalizerResidual
public import Theory.GroupTheory.ConjugateCentralizerFactorization

/-!
# The counting factorization in the binary G₂ local core

The centralizer of the chosen module in R=O₂(O²(C_L(Ω₁Z(T)))T)
is the actual Q=O₂(LT). An element of N_G(T) preserves R, so the
centralizer of its conjugate module has order |Q|. The source point-radical
centralizer bound and the two index-eight identities then give
Q=V C_Q(Vᵈ). The model inputs remain explicit for their action producer.

Source: Aschbacher--Smith 3.3.28, printed p.601.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 Chapter12.Section02.RecognitionSource
open Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The chosen module's centralizer inside the source residual core is Q. -/
theorem local_centralizer_chosen_eq_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    omegaResidualCore T L ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hR := local_core_containments (T := T) (L := L)
  calc
    _ = omegaResidualCore T L ⊓ ((T : Subgroup G) ⊓ centralizer (V : Set G)) := by
      rw [← inf_assoc, inf_eq_left.mpr hR.2]
    _ = _ := by
      rw [chosen_sylow_centralizer_eq_core_at h D structural, inf_eq_right.mpr hR.1]

/-- The centralizer of Vᵈ is exactly Qᵈ inside the same invariant local core. -/
theorem local_centralizer_conjugate_eq_core_conjugate
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    {d : G} (hd : d ∈ normalizer (T : Set G)) :
    omegaResidualCore T L ⊓ centralizer (V.map (MulAut.conj d).toMonoidHom : Set G) =
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj d).toMonoidHom := by
  have hR : (omegaResidualCore T L).map (MulAut.conj d).toMonoidHom =
      omegaResidualCore T L := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer_preserves_local_residual h D e hne).2 hd)
  rw [← local_centralizer_chosen_eq_core h D structural,
    map_inf _ _ _ (MulAut.conj d).injective, hR,
    Theory.GroupTheory.map_centralizer_equiv]
  rfl

/-- Source 3.3.28's counting step for the literal original modules and cores.
The remaining inputs are precisely the point-radical centralizer and the
image/fixed-space index-eight calculations. -/
theorem core_eq_chosen_sup_centralizer_of_point_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (hcover : omegaResidualCore T L ⊓
        centralizer (V.map (MulAut.conj d).toMonoidHom : Set G) ≤
      V.map (MulAut.conj d).toMonoidHom ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (himage : Nat.card (V.map (MulAut.conj d).toMonoidHom) =
      8 * Nat.card (V.map (MulAut.conj d).toMonoidHom ⊓
        (L ⊔ (T : Subgroup G)).pCoreIn 2 : Subgroup G))
    (hfixed : Nat.card V = 8 * Nat.card (V ⊓
      centralizer (V.map (MulAut.conj d).toMonoidHom : Set G) : Subgroup G)) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 = V ⊔
      ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓
        centralizer (V.map (MulAut.conj d).toMonoidHom : Set G)) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let B := V.map (MulAut.conj d).toMonoidHom
  have hBQ : B ≤ normalizer (Q : Set G) :=
    ((conjugate_chosen_le_local_core h D structural e hne hd).trans
      local_core_containments.2).trans
      (le_sup_right.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))))
  have hBB : B ≤ centralizer (B : Set G) := by
    let := D.elementary
    exact (map_mono (f := (MulAut.conj d).toMonoidHom) V.le_centralizer).trans
      (map_centralizer_le_centralizer_image _ _)
  have hcard : Nat.card (omegaResidualCore T L ⊓ centralizer (B : Set G) : Subgroup G) =
      Nat.card Q := by
    rw [local_centralizer_conjugate_eq_core_conjugate h D structural e hne hd,
      card_map_of_injective (MulAut.conj d).injective]
  exact eq_sup_centralizer_of_equal_indices (omegaResidualCore T L) Q V B 8
    local_core_containments.1 D.le_core
    (conjugate_chosen_le_local_core h D structural e hne hd)
    ((local_centralizer_chosen_eq_core h D structural).symm.le.trans inf_le_right)
    hBB hBQ hcover hcard himage hfixed

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
