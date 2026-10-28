module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.SourceThree

/-!
# The exact calculation in the source-(3.3) quotient

Put R₀ = [Z_a,Z_a'] and D = [X_a,X_a']. The already constructed action
of Q_t ∩ C(R₀) on X_a'/R₀ turns the printed bound into a displacement
calculation with values in the image of D ⊔ [X_a ∩ Q_a',Y].

Keeping D in that image makes the criterion equivalent to the printed
bound. In particular, it does not silently replace D by R₀ in the outer
extension. No normalization of D by the actors is needed. The forward
direction takes the image of each commutator; the reverse direction lifts
the quotient calculation and absorbs R₀ into D.

The model calculation remains to be proved in the three bad branches.
The equivalence is a transfer lemma, not a proof of the source theorem.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3), printed pp.866–868.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
open SourceThree

/-- In the literal source quotient, retaining the image of [X_a,X_a'] gives
an equivalent calculation, with no invariance assumption on that subgroup. -/
theorem bound_iff_quotient_displacement (source : LocalSource L R)
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a' t)
    (Y : Subgroup (FreeAmalgam R)) (hY : Y ≤ centralizingActors R a a' t) :
    letI := critical_Z_quotient_normal a a'
    ∀ action : centralizingActors R a a' t →*
        MulAut (X R a' ⧸ (⁅Z R a, Z R a'⁆).subgroupOf (X R a')),
      (∀ actor : centralizingActors R a a' t, ∀ point : X R a',
        action actor
          (QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a')) point) =
        QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a'))
          ⟨(actor : FreeAmalgam R) * (point : FreeAmalgam R) *
              (actor : FreeAmalgam R)⁻¹,
            (mem_normalizer_iff.mp
              (centralizingActors_normalize_X a a' t hat actor.property) point).mp
                point.property⟩) →
      (⁅Z R a', Y⁆ ≤ ⁅X R a, X R a'⁆ ⊔ ⁅X R a ⊓ Q R a', Y⁆ ↔
        ∀ actor : centralizingActors R a a' t, (actor : FreeAmalgam R) ∈ Y →
          ∀ point : X R a', (point : FreeAmalgam R) ∈ Z R a' →
          (QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a')) point)⁻¹ *
            action actor
              (QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a')) point) ∈
            ((⁅X R a, X R a'⁆ ⊔ ⁅X R a ⊓ Q R a', Y⁆).subgroupOf (X R a')).map
              (QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a')))) := by
  let := critical_Z_quotient_normal a a'
  intro action hformula
  constructor
  · intro hbound actor hactor point hpoint
    rw [hformula, ← map_inv, ← map_mul]
    apply mem_map_of_mem
    change (point : FreeAmalgam R)⁻¹ *
      ((actor : FreeAmalgam R) * (point : FreeAmalgam R) * (actor : FreeAmalgam R)⁻¹) ∈
        ⁅X R a, X R a'⁆ ⊔ ⁅X R a ⊓ Q R a', Y⁆
    have he : (point : FreeAmalgam R)⁻¹ *
        ((actor : FreeAmalgam R) * (point : FreeAmalgam R) * (actor : FreeAmalgam R)⁻¹) =
        ⁅(point : FreeAmalgam R)⁻¹, (actor : FreeAmalgam R)⁆ := by
      simp only [commutatorElement_def, inv_inv, mul_assoc]
    rw [he]
    exact hbound (commutator_mem_commutator ((Z R a').inv_mem hpoint) hactor)
  · intro hdisplacement
    have h := quotient_conjugation_commutator_le_sup
      (centralizingActors R a a' t) (X R a') (⁅Z R a, Z R a'⁆) (Z R a') Y
      (⁅X R a, X R a'⁆ ⊔ ⁅X R a ⊓ Q R a', Y⁆)
      (centralizingActors_normalize_X a a' t hat) hY
      (critical_endpoint_choice source geometry hb a ha a' hc).1
      action hformula hdisplacement
    rw [commutator_comm] at h
    exact h.trans (sup_le le_rfl
      ((critical_Z_commutator_le_auxiliary source geometry hb a ha a' hc).trans le_sup_left))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation
