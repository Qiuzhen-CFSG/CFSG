module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCoreMovement
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.BinaryConjugationSection.FixedMoving
public import Theory.GroupTheory.ConjugateSpanNormalizer

/-!
# The outer span's plane in the original residual-core quotient

Use the literal duality P/C_P(U) ≃ (U/V₁)*, where P = O₂(K). The
commutator [U,Q] has rank four modulo V₁, so the dual Q-fixed space
has dimension two. The image of S ∩ P lies in that fixed space, because
[S,Q] = R centralizes U. A critical involution's displacement has dimension
two and lifts into S ∩ P, proving equality. Full L₁-movement on U/V₁
also excludes L₁-fixed vectors on the dual.

Both original coordinate maps and the full C_P(U) kernel remain literal.
The application in ExtraspecialOuterCore uses this plane as the second
noncentral chief factor of S/R.
Source: Aschbacher–Smith 14.7.24(1), printed p.1051, refs/quasithin.pdf.
The named earlier inputs retain their existing producers and final discharge
at qt-d-14775-source.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original S-image in P/C_P(U) is exactly its Q-fixed plane; the
whole dual module has no nonzero L₁-fixed vector. -/
theorem extraspecial_core_outer_fixed_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (sU : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (sP : BinaryConjugationSection F.H ((K F).pCoreIn 2)
      ((K F).pCoreIn 2 ⊓ centralizer (F.U : Set G)) ρ.dual) :
    fixedSpace ρ.dual ((Q T L).subgroupOf F.H) =
      sP.imageSpace (conjugateSpanBy F.U L) ∧
    Module.finrank (ZMod 2) (sP.imageSpace (conjugateSpanBy F.U L)) = 2 ∧
    ∀ w : Module.Dual (ZMod 2) W,
      (∀ a : F.Li L 1, ρ.dual (inclusion ((F.Li_le L 1).trans inf_le_right) a) w = w) →
      w = 0 := by
  let : Finite W := Finite.of_surjective (fun u => (sU.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp sU.onto)
  let P := (K F).pCoreIn 2
  let S := conjugateSpanBy F.U L
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  let E := ⁅F.U,Q T L⁆
  let A := (Q T L).subgroupOf F.H
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨_,_,_,hd,_⟩ := extraspecial_section h hab structural previous hex hcard hexp sU
  obtain ⟨c,hs,_,_,hEc,_,hSQ,_,_,_,_,_,hRC,_,hinter,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful ⟨e⟩
  have hEU : E ≤ F.U := hinter.symm.le.trans inf_le_left
  have hZE : F.Vi 1 ≤ E := by
    exact (F.le_seed 1).trans
      ((extraspecial_critical_commutator_eq_seed h hab structural previous faithful ⟨e⟩ c hs).symm.le.trans
        (commutator_mono le_rfl (critical_le_Q h structural c)))
  have hEi : (F.Vi 1).relIndex E = 16 := by
    have hh := relIndex_mul_card_of_le hZE
    have hz : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    rw [hz,hEc] at hh
    omega
  have hEd := sU.imageSpace_finrank_of_index E hEU 4 hEi
  have hmove : subspaceCommutator ρ ⊤ A = sU.imageSpace E := by
    rw [←sU.imageSpace_self,←sU.imageSpace_commutator (Q T L) F.U (Q_le_H F) le_rfl]
    rw [commutator_comm]
  have hcodim : fixedCodim ρ.dual A = 4 := by
    rw [fixedCodim_dual_eq_moved_finrank,hmove,hEd]
  have hfixdim : Module.finrank (ZMod 2) (fixedSpace ρ.dual A) = 2 := by
    have hh := fixedCodim_add_finrank ρ.dual A
    rw [Subspace.dual_finrank_eq,hd,hcodim] at hh
    omega
  have hfixed : sP.imageSpace S ≤ fixedSpace ρ.dual A := by
    intro w hw a
    obtain ⟨p,hp,rfl⟩ := (sP.mem_imageSpace_iff S w).mp hw
    apply (sP.fixed_coordinate_iff_commutator_mem a p).mpr
    refine ⟨?_,?_⟩
    · exact (le_normalizer_iff_commutator_le_left.mp
        ((Q_le_H F).trans sP.normalized))
        (commutator_mem_commutator p.property a.property)
    · apply hRC.trans inf_le_right
      apply hSQ.le
      exact commutator_mem_commutator hp a.property
  obtain ⟨a,b,ha,hane,_,_,_,hb,hba,hbo⟩ :=
    exists_extraspecial_critical_actor_square_root h hab structural previous faithful ⟨e⟩ c hs
  have htwo := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  have haQ : a ∉ pCore 2 F.H := fun hh => hane ((QuotientGroup.eq_one_iff _).mpr hh)
  have hdis : Module.finrank (ZMod 2) (ρ a-1).range = 2 :=
    critical_displacement_two_of_normal_card_two h hab structural
      (h.flag_escape F previous) hn sU c hs htwo a ha haQ
  have hdualdis : Module.finrank (ZMod 2) (ρ.dual a-1).range = 2 := by
    change Module.finrank (ZMod 2) (ρ.dual a-LinearMap.id).range = 2
    rw [←fixedCodim_zpowers_eq_displacement_rank,fixedCodim_zpowers_dual,
      fixedCodim_zpowers_eq_displacement_rank]
    exact hdis
  have hPT : P ≤ (T : Subgroup G) := (pCoreIn_mono_of_normalizes (K_le_H F) (H_normalizes_K F)).trans
    ((pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
      (map_subgroupOf_eq_of_le (F.invariant 1)))
  have hPnS : P ≤ normalizer (S : Set G) := hPT.trans
    (normalizes_conjugateSpanBy F.U L (T : Subgroup G)
      ((F.invariant 1).trans (le_normalizer_conjugateSpanBy V F.H))
      (h.sylow_normalizes structural))
  obtain ⟨_,_,g,hg,hgU,_⟩ := extraspecial_critical_interchange h hab structural previous faithful ⟨e⟩ c hs
  have hAS : c.Uα ≤ S := by
    change c.Uα ≤ conjugateSpanBy F.U L
    rw [←hgU,conjugateSpanBy_eq_iSup_conj]
    exact le_iSup_of_le (⟨g,hg⟩ : L) le_rfl
  have hcomm : ⁅c.Uα,P⁆ ≤ S := (commutator_mono hAS le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp hPnS)
  have hdispS : (ρ.dual a-1).range ≤ sP.imageSpace S :=
    sP.displacement_range_le_imageSpace_of_commutator_le c.Uα S hcomm a ha
  have hdim : Module.finrank (ZMod 2) (sP.imageSpace S) = 2 := by
    have hl := Submodule.finrank_mono hdispS
    have hu := Submodule.finrank_mono hfixed
    omega
  refine ⟨(Submodule.eq_of_le_of_finrank_eq hfixed (hdim.trans hfixdim.symm)).symm,hdim,?_⟩
  let B := (F.Li L 1).subgroupOf F.H
  have hfull : subspaceCommutator ρ ⊤ B = ⊤ := by
    rw [←sU.imageSpace_self,←sU.imageSpace_commutator (F.Li L 1) F.U
      ((F.Li_le L 1).trans inf_le_right) le_rfl,
      commutator_comm,commutator_U_point_of_normal h hn,sU.imageSpace_self]
  have hdfull : fixedCodim ρ.dual B = 6 := by
    rw [fixedCodim_dual_eq_moved_finrank,hfull,finrank_top,hd]
  have hdbot : fixedSpace ρ.dual B = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    have hh := fixedCodim_add_finrank ρ.dual B
    rw [hdfull,Subspace.dual_finrank_eq,hd] at hh
    omega
  intro w hw
  have hh : w ∈ fixedSpace ρ.dual B := fun a => hw ⟨a,a.property⟩
  simpa only [hdbot,Submodule.mem_bot] using hh

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
