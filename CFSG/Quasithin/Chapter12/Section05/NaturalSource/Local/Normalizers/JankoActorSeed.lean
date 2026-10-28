module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoNativeParabolic
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ParabolicSeed

/-!
# An elementary seed for the original Janko projected actor

Under actual max1 or max4 placement of the original point parabolic,
the original full Sylow normalizes the actual Y-normal closure inside
that parabolic. The native self-centralizing two-core argument makes
the closure's two-core nontrivial. Its central omega is therefore a
nonzero elementary subgroup normalized by the same projected actor.

The original containment Y ≤ L_i ≤ G_i also puts the closure and its
seed inside that actor. Thus the actor itself has nontrivial two-core.
Every restriction and image uses the supplied component map, the literal
original Y and the original G_i projection. No independent Sylow or
replacement actor is chosen. This discharges the elementary-seed premise
for a future native cover application to the actor.

The cover and symmetry have their existing native producers. The max1
trio-to-max4 incidence comparison and the original actor's normalization
of L1* remain with qt-d-1251-local. Final source assembly is qt-d-1251-source;
this conditional seed result does not finish 12.5.4.
Source: Aschbacher–Smith 12.5.4, printed p.819/PDF p.836.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The same original projected actor normalizes a nonzero elementary seed,
when the original parabolic is in either surviving characteristic-two local. -/
theorem point_projection_janko_elementary_seed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (hplace : (s.pointComponentParabolic K).map e.toMonoidHom ≤
        Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four ∨
      (s.pointComponentParabolic K).map e.toMonoidHom ≤
        Janko4.LocalStructure.SymmetricLinear.max4Subgroup)
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    let C := s.pointCoreImage K
    let U := ((s.pointCoreImage s.Y).subgroupOf C).map e.toMonoidHom
    let A := ((s.localPointProjection K i).subgroupOf C).map e.toMonoidHom
    let N := conjugateSpanBy U A
    let E := omegaCenterIn (N.pCoreIn 2)
    pCore 2 N ≠ ⊥ ∧ pCore 2 A ≠ ⊥ ∧ E ≠ ⊥ ∧ IsElementaryAbelian 2 E ∧ E ≤ A ∧
      A ≤ normalizer (E : Set Janko4.Model) := by
  have hYK := s.Y_le_point_component_of_large_model h hK hN
    (.inr (.inr ⟨(s.pointComponentCoreEquivImage hK.1 hN).trans e⟩))
  let C := s.pointCoreImage K
  let Y := (s.pointCoreImage s.Y).subgroupOf C
  let A := (s.localPointProjection K i).subgroupOf C
  let P := s.pointComponentParabolic K
  have hYC : s.pointCoreImage s.Y ≤ C := s.pointCoreImage_mono hYK
  have hYA : Y ≤ A := by
    apply comap_mono
    exact le_inf hYC ((s.pointCoreImage_mono (le_inf
      ((s.Y_le_local_residual i hi).trans (s.marking.Li_le_Gi i))
      ((map_subtype_le _).trans (s.P_le_M₁.trans inf_le_right)))).trans le_sup_left)
  have hYnot : ¬ IsPGroup 2 Y := fun ht => s.pointCoreImage_Y_not_two
    (ht.of_equiv (subgroupOfEquivOfLe hYC))
  have heYnot : ¬ IsPGroup 2 (Y.map e.toMonoidHom) := fun ht =>
    hYnot (ht.of_equiv (e.subgroupMap Y).symm)
  have hc : conjugateSpanBy Y A ≤ P := by
    have hh : (conjugateSpanBy Y A).map C.subtype ≤ s.pointCoreImage (s.marking.Mi 1) := by
      rw [map_conjugateSpanBy, map_subgroupOf_eq_of_le hYC,
        map_subgroupOf_eq_of_le (show s.localPointProjection K i ≤ C from inf_le_left)]
      exact (s.projected_Y_span_le_point_parabolic h hN hYK i hi).trans inf_le_left
    exact map_le_iff_le_comap.mp hh
  have hec : conjugateSpanBy (Y.map e.toMonoidHom) (A.map e.toMonoidHom) ≤
      P.map e.toMonoidHom := by
    rw [← map_conjugateSpanBy]
    exact map_mono hc
  obtain ⟨S, hS, hSA⟩ := s.point_projection_contains_original_sylow hN i hi
  have hSP : (S : Subgroup C) ≤ P := by
    rw [hS]
    exact comap_mono (s.pointCoreImage_mono (le_inf le_sup_right s.sylow_le_G₁))
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hRH : (R : Subgroup Janko4.Model) ≤ P.map e.toMonoidHom := map_mono hSP
  have hn : conjugateSpanBy (Y.map e.toMonoidHom) (A.map e.toMonoidHom) ≠ ⊥ := by
    intro hz
    have hbot : Y.map e.toMonoidHom = ⊥ :=
      bot_unique ((le_conjugateSpanBy _ _).trans_eq hz)
    apply heYnot
    rw [hbot]
    exact IsPGroup.of_bot
  have hseed := Janko4.LocalStructure.ParabolicSeed.elementary_seed R _ _
    (map_mono hSA) (le_normalizer_conjugateSpanBy _ _) hn
    (hplace.imp ((sup_le hRH hec).trans ·) ((sup_le hRH hec).trans ·))
  let N := conjugateSpanBy (Y.map e.toMonoidHom) (A.map e.toMonoidHom)
  let E := omegaCenterIn (N.pCoreIn 2)
  have hNA : N ≤ A.map e.toMonoidHom :=
    conjugateSpanBy_le (map_mono hYA) (A.map e.toMonoidHom).le_normalizer
  have hEA : E ≤ A.map e.toMonoidHom :=
    (map_subtype_le _).trans ((pCoreIn_le 2 N).trans hNA)
  have hcoreA : pCore 2 (A.map e.toMonoidHom) ≠ ⊥ := by
    intro hz
    have hEQ : E ≤ (A.map e.toMonoidHom).pCoreIn 2 :=
      le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 E) hEA hseed.2.2.2
    rw [pCoreIn, hz, Subgroup.map_bot] at hEQ
    exact hseed.2.1 (bot_unique hEQ)
  exact ⟨hseed.1, hcoreA, hseed.2.1, hseed.2.2.1, hEA, hseed.2.2.2⟩

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
