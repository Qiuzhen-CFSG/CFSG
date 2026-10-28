module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootSpanOffender
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSpanFixedFree
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSpanNatural

/-!
# Natural moved coordinates on the actual root-offender span

The literal endpoint offender supplies FF recognition on the full midpoint
span quotient, with its original full kernel and quotient coordinates.
The original SQTK hypothesis descends along this same vertex projection.
Thus the moved section is natural at the original field degree, and the
full quotient has no fixed vectors.

Both source seed budgets and the actual midpoint-stabilizer conjugator
remain visible. The statement recognizes only the moved section; it does
not identify it with the whole quotient or change the original field mark.
Source: the final FF recognition in MS93 (5.12), printed p.927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
/-- The full literal root-offender span quotient, its zero fixed space,
and natural moved section in original-degree coordinates. -/
@[expose] def distanceFourRootSpanNatural {M : Type*} [Group M] {R : Subgroup M}
    (geometry : Geometry R) (a e z : Vertex R) (n : ℕ) : Prop :=
  let W := localZSpan R e a
  let D := W ⊓ B R a (geometry.Z_normal a)
  ∃ E : BinaryField, E.degree=n ∧
    ∃ f : stabilizer R a →* Sp E.Carrier,
      Function.Surjective f ∧ f.ker.map (stabilizer R a).subtype=Q R a ∧
      ∃ hD : (D.subgroupOf W).Normal,
        letI := hD
        ∃ hEA : IsElementaryAbelian 2 (W ⧸ D.subgroupOf W),
          letI := hEA
          ∃ σ : Representation (ZMod 2) (Sp E.Carrier) (Additive (W ⧸ D.subgroupOf W)),
            Function.Injective σ ∧
            ∃ c : BinaryConjugationSection (stabilizer R a) W D (σ.comp f),
              (∀ w : W, (c.coordinates w).toAdd=
                Additive.ofMul (QuotientGroup.mk' (D.subgroupOf W) w)) ∧
              IsOffender σ (((Z R z).subgroupOf (stabilizer R a)).map f) ∧
              fixedSpace σ ⊤=⊥ ∧
              IsIrrPlus σ ⊤ (subspaceCommutator σ ⊤ ⊤) ∧
              ∃ Eₙ : BinaryField, Eₙ.degree=n ∧
                Nonempty (ActionEquiv
                  ((MovedSection.ofNormal σ ⊤).action.comp
                    (⊤ : Subgroup (Sp E.Carrier)).subtype)
                  (binarySymplectic Eₙ))

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The same literal root-offender quotient has zero fixed space and a
natural moved section, with original-degree field and full-kernel marking. -/
theorem Input.replacement_distance_four_root_span_natural
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (path.walk.getVert 2))
    (hga : act d.radical g a=z)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hfirst : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F)
    (hlast : (B d.radical (path.walk.getVert 2) (geometry.Z_normal _)).relIndex
      (U d.radical z) ≤ Nat.card F) :
    distanceFourRootSpanNatural geometry a (path.walk.getVert 2) z n := by
  obtain ⟨E,hE,f,hf,hfQ,hD,hdata⟩ :=
    h.replacement_distance_four_root_span_offender d path hb g hg hga hfixed hfirst hlast
  let := hD
  obtain ⟨hEA,hdata⟩ := hdata
  let := hEA
  obtain ⟨σ,hfaith,c,hcoord,hactor⟩ := hdata
  let := finite_stabilizer d.radical a
  let W := localZSpan d.radical (path.walk.getVert 2) a
  let : Finite W := Finite.of_injective (inclusion c.section_le) (inclusion_injective _)
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 3 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let := SimpleQuotients.isSimpleGroup hlarge
  let : IsSimpleGroup (Sp E.Carrier) := EvenProjective.equiv.isSimpleGroup
  let : IsQuasisimple (Sp E.Carrier) := CentralCovers.Even.isQuasisimple hlarge
  let : IsSimpleGroup (⊤ : Subgroup (Sp E.Carrier)) :=
    (topEquiv : (⊤ : Subgroup (Sp E.Carrier)) ≃* Sp E.Carrier).isSimpleGroup
  let : IsQuasisimple (⊤ : Subgroup (Sp E.Carrier)) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have hs := actual_vertex_projection_sqtk h d path.start_color E f hf hfQ
  have hcent : centralizer (↑(⊤ : Subgroup (Sp E.Carrier)) : Set (Sp E.Carrier))=⊥ := by
    rw [coe_top,centralizer_univ,EvenProjective.center_eq_bot]
  have hnat := ff_card_sp_moved_natural σ ⊤ E.Carrier
    (show Nat.card E.Carrier=2^n by rw [E.card_eq,hE]) h.nonbinary
    (Nat.card_congr (topEquiv : (⊤ : Subgroup (Sp E.Carrier)) ≃* Sp E.Carrier).toEquiv)
    hcent (hs.subgroup ⊤) hfaith ⟨_,hactor⟩
  have hWV : W ≤ V d.radical a := localZSpan_le_V d.radical (by
    rw [SimpleGraph.dist_comm,path.dist_start (by rw [path.length_eq_b,hb]; omega)])
  have hzero := h.replacement_radius_section_fixedSpace_eq_bot d geometry (by omega)
    path.start_color W hWV f σ c
  exact ⟨E,hE,f,hf,hfQ,hD,hEA,σ,hfaith,c,hcoord,hactor,hzero,hnat⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
