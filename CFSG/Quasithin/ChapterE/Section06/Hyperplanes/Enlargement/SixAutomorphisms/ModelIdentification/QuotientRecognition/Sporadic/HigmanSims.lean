module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.MarkedAction
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.CentralCoverSylow
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Sporadic.HSGeometry
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Sporadic.Reduction
/-!
# The HS source exclusion in E.6.23

The actual quotient action has a central-class actor with derived fixed-group
order 3840 and a distinguished actor with fixed-group order 2880. The original
common Sylow and central-cover commutator transfer force the former derived
Sylow order 256 to divide 2880, a contradiction. The full central cover is
retained throughout; no quotient fixed point is assumed to lift.

Source: Aschbacher–Smith E.6.23, printed p.254 (PDF p.265).
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.Sporadic
open RankTwo
variable {G : Type*} [Group G] [Finite G]
theorem higman_sims_source (T : Sylow 2 G) (M V : Subgroup G) [IsElementaryAbelian 2 V] :
    SourceExclusion _root_.Sporadic.LeechRelated.HS.Carrier T M V := by
  intro h h15 _ U A L X g d _ Y hY he
  obtain ⟨e⟩ := he
  let := extension_quasisimple hY
  let : IsSimpleGroup (Y ⧸ center Y) := IsQuasisimple.simple
  let : Group.IsPerfect (Y ⧸ center Y) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center Y))
      (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup _root_.Sporadic.LeechRelated.HS.Carrier := e.symm.isSimpleGroup
  let : Group.IsPerfect _root_.Sporadic.LeechRelated.HS.Carrier :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨s,hs,_⟩ := quotient_fixed_six_action_marked h d hY
  let sm := s.map e
  obtain ⟨hc,a,ha,ha1,hder⟩ := HSGeometry.exists_actor_derived_card sm
  obtain ⟨aq,haq,hqa⟩ := ha
  have haq' : aq ∈ (actionImage V Y).map (quotientAut (center Y)) := hs ▸ haq
  obtain ⟨ay,hay,hya⟩ := haq'
  have hea : MulAut.congr e (quotientAut (center Y) ay) = a := by
    rw [hya]
    exact hqa
  have hay1 : ay ≠ 1 := by
    intro hy1
    exact ha1 (hea.symm.trans (by rw [hy1,map_one,map_one]))
  have hcs : s.involution ∈ (actionImage V Y).map (quotientAut (center Y)) :=
    hs ▸ s.involution_mem
  obtain ⟨cy,hcy,hec⟩ := hcs
  have hec' : MulAut.congr e (quotientAut (center Y) cy) = sm.involution := by
    rw [hec]
    rfl
  let b := MulAut.congr e (quotientAut (center Y) ay)
  let Q : Sylow 2 (commutator b.fixedSubgroup) := default
  have hd := quotient_actor_derived_sylow_dvd h h15 d hY e ay cy hay hay1 hcy Q
  have hcQ : Nat.card Q = 256 := by
    rw [Q.card_eq_multiplicity]
    have hh : Nat.card (commutator b.fixedSubgroup) = 3840 := by
      change Nat.card (commutator (MulAut.congr e (quotientAut (center Y) ay)).fixedSubgroup) = _
      rw [hea]
      exact hder
    rw [hh]
    decide +kernel
  rw [hcQ,hec',hc] at hd
  norm_num at hd
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.Sporadic
