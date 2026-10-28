module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RuRecords
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.Basic
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.PCoreImage

/-!
# The actual groups in the 14.7.74 collapse

The fixed preimage is the greatest subgroup of Q centralizing L modulo V;
QL is the literal C_Q(L). The input below contains earlier-source conclusions
through 14.7.73 and the genuine unique maximal two-local over LT. It contains
no collapse assertion. In particular the Steinberg coordinates use the same
qL as the original natural coordinates, and the parabolic in 14.7.73(1)
uses its two-core, whereas K remains the two-residual of H.

The producers of the 71--73 fields are the chief-factor, Steinberg and root
branches of the local endgame. The 14.7.74 owner must discharge the separate
projective splitting, Gaschütz and natural-extension arguments.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
14.7.71--74, printed pp.1075--1077 (PDF pp.1092--1094).
-/

@[expose] public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The original L-span of U. -/
def S (L : Subgroup G) (F : InvariantFlag T V 3) : Subgroup G :=
  conjugateSpanBy F.U L

/-- The actual preimage of C_{Q/V}(L). -/
def QC (T : Sylow 2 G) (L V : Subgroup G) : Subgroup G :=
  commutatorPreimage (Q T L) L V

/-- The fixed subgroup before taking any quotient. -/
def QL (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  Q T L ⊓ centralizer (L : Set G)

/-- Earlier-source inputs, with no assertion from the proof of 14.7.74. -/
structure Prior (d : Data T L V F W) where
  separation : d.ModuleSeparation
  sylow_normalizes : (T : Subgroup G) ≤ normalizer (L : Set G)
  unique_overgroup :
    {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} =
      {normalizer (L : Set G)}
  centralizer_LT : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) = Q T L
  core : S L F = L.pCoreIn 2
  steinberg : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL)
  center : (Subgroup.center (S L F)).map (S L F).subtype = V
  frattini : (_root_.frattini (S L F)).map (S L F).subtype = V
  derived : (_root_.commutator (S L F)).map (S L F).subtype = V
  commutator : ⁅Q T L, L⁆ = S L F
  point_kernel : d.U₀ = F.Vi 1
  parabolic_core : (F.Li L 1).pCoreIn 2 = S L F ⊔ (K F).pCoreIn 2
  parabolic_sylow : Chapter1.IsSylowIn 2 (S L F ⊔ (K F).pCoreIn 2) (K F)
  sylow_index : ((T : Subgroup G) ⊓ K F).relIndex ((T : Subgroup G) ⊓ L) = 2
  core_order : Nat.card ((K F).pCoreIn 2) = 2 ^ 11

variable (d : Data T L V F W)

include d in
/-- Membership in H_z gives escape, not containment in M. -/
theorem H_not_le_normalizer : ¬ F.H ≤ normalizer (L : Set G) := by
  have hh : F.H ∈ F.Hz L (normalizer (L : Set G)) := by
    rw [d.unique_Hz]
    exact Set.mem_singleton _
  exact hh.2.2

include d in
/-- H=KT and T≤M turn the same escape into K≰M. -/
theorem K_not_le_normalizer (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ¬ K F ≤ normalizer (L : Set G) := by
  intro hk
  exact H_not_le_normalizer d (d.residual_product ▸ sup_le hk hTL)

variable (a : Prior d)

omit [Finite G] in
include F in
/-- Q normalizes the original V, directly from the T-invariant flag. -/
theorem Q_normalizes_V : Q T L ≤ normalizer (V : Set G) := by
  have hQT : Q T L ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  exact hQT.trans (by simpa only [F.last] using F.invariant 3)

omit [Finite G] in
include F in
/-- The definition of QC supplies the literal commutator bound. -/
theorem QC_commutator_le : ⁅QC T L V, L⁆ ≤ V :=
  commutator_commutatorPreimage_le _ _ _ (Q_normalizes_V (F := F))

include a in
/-- LT preserves the actual fixed preimage. -/
theorem LT_normalizes_QC : L ⊔ (T : Subgroup G) ≤ normalizer (QC T L V : Set G) := by
  apply commutatorPreimage_normalized _ _ _ _ (Q_normalizes_V (F := F))
  · exact (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  · exact sup_le L.le_normalizer a.sylow_normalizes
  · exact sup_le d.natural.chosen.normalizes
      (by simpa only [F.last] using F.invariant 3)

include a in
/-- LT also preserves the literal C_Q(L). -/
theorem LT_normalizes_QL : L ⊔ (T : Subgroup G) ≤ normalizer (QL T L : Set G) := by
  have hQ : L ⊔ (T : Subgroup G) ≤ normalizer (Q T L : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hC := (sup_le L.le_normalizer a.sylow_normalizes).trans
    (normalizer_le_normalizer_centralizer L)
  intro g hg
  apply mem_normalizer_iff.mpr
  intro x
  exact and_congr (mem_normalizer_iff.mp (hQ hg) x)
    (mem_normalizer_iff.mp (hC hg) x)

omit [Finite G] in
/-- The two-core of K is contained in the two-core of H by relative normality. -/
theorem P_le_QH : (K F).pCoreIn 2 ≤ F.H.pCoreIn 2 :=
  pCoreIn_mono_of_normalizes (K_le_H F) (H_normalizes_K F)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse
