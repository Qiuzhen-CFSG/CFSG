module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.SourceCompletion.Gaschutz
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.EvenCovers.NaturalSection
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ChiefObstruction.PointCommutator
public import Theory.Representation.BinaryConjugationSection.FixedSplitting
public import Theory.Representation.SL2FourNaturalBorelFixedLifting.Cocycles

/-!
# The original fixed subgroup is centralized by K

For x in Q_L=C_Q(L), the first Gaschütz bound makes its K-commutators
lie in U. Their original U/U₀ coordinates form a natural crossed
homomorphism vanishing on L₁. The marked Borel and actual Sylow placement
force this cocycle to vanish. Hence [Q_L,K]≤U₀=V₁. The original H
centralizes V₁, so perfection of K kills the remaining displacement.
This implements the second Gaschütz step directly on commutator cocycles;
no elementary structure on Q_L or Q_CU is presumed.

Source: Aschbacher–Smith,14.7.74,second paragraph,printed p.1077.
-/

public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (a : Prior d) (mark : UpperMarking d)

private theorem natural_actor_eq : d.KSL2FourMap = RootRecognition.qK d := by
  apply MonoidHom.ext
  intro k
  apply d.naturalQuotient.marking.injective
  apply Subtype.val_injective
  exact (d.KSL2FourMap_apply k).trans (RootRecognition.qK_marking d k)

omit [Finite G] in
private theorem QL_le_QC : QL T L ≤ QC T L V := by
  apply le_commutatorPreimage inf_le_left
  exact (commutator_eq_bot_iff_le_centralizer.mpr
    (show QL T L ≤ centralizer (L : Set G) from inf_le_right)).le.trans bot_le

include d structural a mark in
/-- The actual displacement of Q_L lies in the original point kernel. -/
theorem QL_K_le_point (hKC : ⁅QC T L V,K F⁆ ≤ F.U) :
    ⁅QL T L,K F⁆ ≤ F.Vi 1 := by
  let s := d.KNaturalSection d.U_eq_commutator_K
  have hdisp : ⁅K F,QL T L⁆ ≤ F.U := by
    rw [commutator_comm]
    exact (commutator_mono (QL_le_QC (T := T) (L := L) (V := V)) le_rfl).trans hKC
  let B := ProjectiveFixedDetection.parabolic (L := L) (F := F)
  obtain ⟨P,hP⟩ := ProjectiveFixedDetection.parabolic_contains_sylow d a
  have hm : B.map d.KSL2FourMap = Matrix.SpecialLinearGroup.rankOneBorel SL2FourNatural.F := by
    rw [natural_actor_eq d]
    exact ProjectiveFixedDetection.parabolic_marking d
      (compatibleBorel_of_upperMarking d structural mark).left_image
  rw [commutator_comm]
  apply commutator_le.mpr
  intro k hk x hx
  let f := s.commutatorCocycle d.KSL2FourMap (QL T L) hdisp ⟨x,hx⟩
  have hf : ∀ b ∈ B, f.val b = 0 := by
    intro b hb
    have hbx : ⁅(b : G),x⁆ = 1 := by
      apply commutatorElement_eq_one_iff_mul_comm.mpr
      exact mem_centralizer_iff.mp hx.2 b ((F.Li_le L 1 hb).1)
    have he : (⟨⁅(b : G),x⁆,hdisp (commutator_mem_commutator b.property hx)⟩ : F.U) = 1 :=
      Subtype.ext hbx
    change (s.coordinates _).toAdd = 0
    rw [he, map_one]
    rfl
  have hz := SL2FourNaturalBorelFixedLifting.cocycle_eq_zero_of_borel
    d.KSL2FourMap d.KSL2FourMap_surjective B P hP hm f hf
  have he : f.val ⟨k,hk⟩ = 0 := congrArg (fun z => z.val ⟨k,hk⟩) hz
  have hu : ⁅k,x⁆ ∈ d.U₀ := (s.coordinates_eq_one_iff _).mp
    (Multiplicative.toAdd.injective he)
  rwa [a.point_kernel] at hu

include d structural a mark in
/-- Perfection removes the remaining central point displacement. -/
theorem K_centralizes_QL (hKC : ⁅QC T L V,K F⁆ ≤ F.U) :
    K F ≤ centralizer (QL T L : Set G) := by
  let M := (QL T L).subgroupOf F.H
  let A := (K F).subgroupOf F.H
  let Z := (F.Vi 1).subgroupOf F.H
  let : Group.IsPerfect A := d.component.perfect
  have hMZ : ⁅M,A⁆ ≤ Z := by
    apply commutator_le.mpr
    intro x hx y hy
    exact QL_K_le_point d structural a mark hKC (commutator_mem_commutator hx hy)
  have hZA : ⁅Z,A⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro z hz k hk
    apply Subtype.ext
    exact (d.H_centralizes_point (K_le_H F hk) z hz).symm
  have hzero : ⁅⁅M,A⁆,A⁆ = ⊥ :=
    eq_bot_iff.mpr ((commutator_mono hMZ le_rfl).trans hZA.le)
  have hfirst := commutator_eq_bot_of_iterated_eq_bot M A hzero
  have hm := congrArg (Subgroup.map F.H.subtype) hfirst
  dsimp only [M,A] at hm
  rw [map_commutator, map_subgroupOf_eq_of_le (show QL T L ≤ F.H from
    inf_le_left.trans (Q_le_H F)), map_subgroupOf_eq_of_le (K_le_H F),Subgroup.map_bot] at hm
  rw [commutator_comm] at hm
  exact commutator_eq_bot_iff_le_centralizer.mp hm

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.SourceCompletion
