module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceOrbits.TwoOrbits
public import Theory.GroupTheory.Commutator.TwoOrbitSpan
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.SourceGeneration.Algebra
/-!
# Original 14.7.13 central, derived and Frattini spans

The actual natural action and the length-three critical path give the
two-orbit cover. The original Q normalizes U and every L-conjugate, so
the commutator family generates the derived subgroup. All generators of
S have exponent two, giving its Frattini equality. If [U,Q] centralizes
Uα, the same two-orbit cover places the entire [U,Q]-span in Z(S).

The final theorem constructs the exact EarlierThirteen record consumed
by 14.7.72, uniformly for every permitted rechoice of the original path.
Only the genuine earlier Structural1222 is retained for T-normalization
and the natural centralizer theorem.

Source: Aschbacher–Smith 14.7.12–13, printed p.1046.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceOrbits
open Chapter12.Section08 CriticalFusion.Source
open SourceEndgame.SteinbergRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
 {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
 {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
 (d : Data T L V F W)
 (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
include d structural in
/-- The source two-orbit cover at the actual b=3 critical path. -/
theorem source_two_orbit (c : CriticalPath (L := L) F) (hb : c.b = 3) (l : L) :
    F.U.conjBy (l : G) = F.U ∨
      ∃ p : (L ⊓ F.H : Subgroup G), F.U.conjBy (l : G) = c.Uα.conjBy (p : G) :=
  two_orbit d (three_conjugate d structural c hb) (critical_ne d c) l
include d structural in
/-- Original 14.7.13(3), on the literal U,Q,L and S. -/
theorem central_span (c : CriticalPath (L := L) F) (hb : c.b = 3)
    (hc : ⁅⁅F.U,Q T L⁆,c.Uα⁆ = ⊥) :
    conjugateSpanBy ⁅F.U,Q T L⁆ L ≤ (center (S F L)).map (S F L).subtype := by
  have hEU : ⁅F.U,Q T L⁆ ≤ F.U :=
    le_normalizer_iff_commutator_le_left.mp ((Q_le_H F).trans d.conjugationSection.normalized)
  have hUU : ⁅F.U,F.U⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff_isMulCommutative.mpr d.abelian)
  have hPE : L ⊓ F.H ≤ normalizer ((⁅F.U,Q T L⁆ : Subgroup G) : Set G) := by
    intro p hp
    have heU : F.U.map (MulAut.conj p).toMonoidHom = F.U :=
      mem_normalizer_iff_map_conj_eq.mp (d.conjugationSection.normalized hp.2)
    have heQ : (Q T L).map (MulAut.conj p).toMonoidHom = Q T L :=
      mem_normalizer_iff_map_conj_eq.mp (L_normalizes_Q hp.1)
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅F.U,Q T L⁆).map (MulAut.conj p).toMonoidHom = _
    rw [map_commutator,heU,heQ]
  have h := iSup_conjugates_le_center_of_two_orbits F.U ⁅F.U,Q T L⁆ c.Uα L (L ⊓ F.H)
    hEU hPE (bot_unique ((commutator_mono hEU le_rfl).trans hUU.le)) hc
    (source_two_orbit d structural c hb)
  rw [←conjugateSpanBy_eq_iSup_conj,←conjugateSpanBy_eq_iSup_conj] at h
  intro x hx
  have hh := h hx
  refine ⟨⟨x,hh.1⟩,mem_center_iff.mpr ?_,rfl⟩
  intro s
  exact Subtype.ext (hh.2 s s.property)
include d structural in
/-- Original 14.7.13(4), including the literal ambient Frattini image. -/
theorem frattini_derived_span (c : CriticalPath (L := L) F) (hb : c.b = 3) :
    (frattini (S F L)).map (S F L).subtype = conjugateSpanBy ⁅F.U,c.Uα⁆ L ∧
      ⁅S F L,S F L⁆ = conjugateSpanBy ⁅F.U,c.Uα⁆ L := by
  have hUQ := (U_and_span_le_Q d structural).1
  have hSQ := (U_and_span_le_Q d structural).2
  have hQU : Q T L ≤ normalizer (F.U : Set G) := (Q_le_H F).trans d.conjugationSection.normalized
  have hUU : ⁅F.U,F.U⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff_isMulCommutative.mpr d.abelian)
  have hA : ∃ a : L, c.Uα = F.U.conjBy (a : G) := by
    obtain ⟨a,ha,he⟩ := three_conjugate d structural c hb
    exact ⟨⟨a,ha⟩,he⟩
  have hd := TwoOrbitSpan.derived_span F.U c.Uα L (L ⊓ F.H) (Q T L)
    hUQ hQU L_normalizes_Q (inf_le_right.trans d.conjugationSection.normalized)
    inf_le_left hUU hA (source_two_orbit d structural c hb)
  have hp : IsPGroup 2 (conjugateSpanBy F.U L) := (isPGroup_pCoreIn 2 _).to_le hSQ
  have hPhi := TwoOrbitSpan.frattini_span F.U L hp (fun u hu => by
    let := d.U_elementary
    exact elemPow_eq_one_of_isElementaryAbelian u hu)
  exact ⟨hPhi.trans hd,hd⟩
include d structural in
/-- Discharge both earlier source implications used in 14.7.72. -/
theorem earlier_thirteen (c : CriticalPath (L := L) F) : SourceGeneration.EarlierThirteen c :=
  ⟨central_span d structural c,frattini_derived_span d structural c⟩
include d structural in
/-- The same producer applies to every permitted original-path rechoice. -/
theorem earlier_thirteen_reselect (c : CriticalPath (L := L) F) :
    ∀ n : Rechoice.group F L, SourceGeneration.EarlierThirteen (c.reselect n) :=
  fun n => earlier_thirteen d structural (c.reselect n)
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceOrbits
