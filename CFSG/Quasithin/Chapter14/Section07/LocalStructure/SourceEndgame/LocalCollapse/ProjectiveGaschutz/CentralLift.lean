module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.Escape
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.Preparation
public import Theory.GroupTheory.Commutator.PerfectLayerLift

/-!
# Lowering the first Gaschütz displacement to U

The earlier 14.7.71 calculation gives [C_H(U),K]≤U. Perfection of the
actual K, from its genuine C-component property, therefore lowers a bound
[QC,K]≤C_H(U) to [QC,K]≤U. All quotient normality is relative to H.
The second theorem applies Escape's original conjugate-span argument.

The bound into C_H(U) remains the marked Gaschütz module obligation; this
file does not assume it to be proved. The earlier inputs are exactly
ChiefFactors.Earlier d c for one critical choice, whose producers remain
with the 14.7.71 and parent source assembly owners.

Source: Aschbacher--Smith, 14.7.71 and 14.7.74, printed pp.1075 and 1077
(PDF pp.1092 and 1094), combined manuscript of 1 March 2004.
-/

public section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- The precise earlier 14.7.71 centralizer calculation lowers a displacement
bound into C_H(U) to the required bound into U. Normality is only in H. -/
theorem QC_K_le_U_of_centralizer_bound (c : CriticalPath (L := L) F)
    (e : ChiefFactors.Earlier d c)
    (hC : ⁅QC T L V, K F⁆ ≤ ChiefFactors.C F) :
    ⁅QC T L V, K F⁆ ≤ F.U := by
  let M := (QC T L V).subgroupOf F.H
  let A := (K F).subgroupOf F.H
  let C := (ChiefFactors.C F).subgroupOf F.H
  let N := F.U.subgroupOf F.H
  let : Group.IsPerfect A := d.component.perfect
  let : N.Normal := normal_subgroupOf_of_le_normalizer d.conjugationSection.normalized
  have hMC : ⁅M,A⁆ ≤ C := by
    apply commutator_le.mpr
    intro x hx y hy
    exact hC (commutator_mem_commutator hx hy)
  have hCN : ⁅C,A⁆ ≤ N := by
    apply commutator_le.mpr
    intro x hx y hy
    have hh := ChiefFactors.centralizer_commutator d c e
    rw [commutator_comm] at hh
    exact hh (commutator_mem_commutator hx hy)
  have hMN := commutator_le_of_iterated_le M A N
    ((commutator_mono hMC le_rfl).trans hCN)
  have hm := map_mono (f := F.H.subtype) hMN
  dsimp only [M, A, N] at hm
  rw [map_commutator,
    map_subgroupOf_eq_of_le (show QC T L V ≤ F.H from
      (commutatorPreimage_le _ _ _).trans (Q_le_H F)),
    map_subgroupOf_eq_of_le (K_le_H F),
    map_subgroupOf_eq_of_le d.conjugationSection.section_le] at hm
  exact hm

/-- The first commutator bound really feeds Escape's two-span centralization. -/
theorem QC_centralizes_S_of_centralizer_bound (a : Prior d)
    (c : CriticalPath (L := L) F) (e : ChiefFactors.Earlier d c)
    (hC : ⁅QC T L V, K F⁆ ≤ ChiefFactors.C F) :
    QC T L V ≤ centralizer (S L F : Set G) :=
  QC_centralizes_S d a (QC_K_le_U_of_centralizer_bound d c e hC)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse
