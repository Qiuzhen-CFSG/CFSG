module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSpanOffenders
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.NaturalRecognition
public import CFSG.Quasithin.KnownSimpleSectionTransport
public import Theory.Quasithin.CoprimeRank
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even

/-!
# Natural recognition on the selected literal midpoint span quotient

Retain the full marked quotient and the actual opposite-span offender
constructed in DistanceFourSpanOffenders. The original SQTK hypothesis
transports to its vertex stabilizer, descends through the actual two-group
kernel, and then transports to the same marked symplectic group. The proved
FF classification therefore recognizes the literal moved section of this
faithful action at the original field degree.

The full quotient, its projection and its coordinates remain in the
certificate. The new natural coordinates describe only its moved section
modulo the fixed part there. No splitting of the full quotient, identification
of reciprocal carriers, or whole-quotient naturality is asserted.
Source: MS93 (5.12)(2), printed p.926, and Aschbacher--Smith B.5.1.
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

/-- The original full span quotient and offender, enriched by natural
coordinates on its literal moved section only. -/
@[expose] def distanceFourSpanNatural {M : Type*} [Group M] {R : Subgroup M}
    (geometry : Geometry R) (a e : Vertex R) (n : ℕ) : Prop :=
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
              IsOffender σ (((localZSpan R a e).subgroupOf (stabilizer R a)).map f) ∧
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

omit [Finite F] [CharP F 2] in
private theorem actual_vertex_projection_sqtk
    {a : Vertex d.radical} (ha : color d.radical a=false)
    (E : BinaryField) (f : stabilizer d.radical a →* Sp E.Carrier)
    (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype=Q d.radical a) :
    IsSQTK KnownSimple.IsKnownSimple (Sp E.Carrier) := by
  let S := stabilizer d.radical a
  let := finite_stabilizer d.radical a
  have hs : IsSQTK KnownSimple.IsKnownSimple S := by
    obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical ha
    let j : d.overgroup ≃* stabilizer d.radical (mVertex d.radical g) :=
      (MonoidHom.ofInjective (embedM_injective d.radical)).trans
        (((MulAut.conj g⁻¹).subgroupMap (Mbar d.radical)).trans
          (MulEquiv.subgroupCongr (stabilizer_mVertex d.radical g).symm))
    exact (h.sqtk.subgroup d.overgroup).knownSimple_of_equiv j
  have hk : f.ker=(Q d.radical a).subgroupOf S := by
    rw [←hfQ]
    exact (comap_map_eq_self_of_injective S.subtype_injective f.ker).symm
  have hp : IsPGroup 2 f.ker := by
    rw [hk]
    exact (Q_isPGroup d.radical (h.replacement_two_group d)
      (h.replacement_core_le d) a ha).comap_subtype
  have hquot : IsSQTK KnownSimple.IsKnownSimple (S ⧸ f.ker) := by
    refine ⟨?_,hs.isKGroup.quotient f.ker⟩
    intro p hprime hodd
    let : Fact p.Prime := ⟨hprime⟩
    rw [primeRank_quotient_eq_of_isTwoGroup p hodd f.ker hp]
    exact hs.stronglyQuasithin p hprime hodd
  exact hquot.knownSimple_of_equiv (QuotientGroup.quotientKerEquivOfSurjective f hf)

omit [Finite F] [CharP F 2] in
private theorem enrich_actual_span_offender
    {geometry : Geometry d.radical} {a e : Vertex d.radical}
    (ha : color d.radical a=false)
    (hoff : distanceFourSpanOffender geometry a e n) :
    distanceFourSpanNatural geometry a e n := by
  obtain ⟨E,hE,f,hf,hfQ,hD,hEA,σ,hfaith,c,hcoord,hactor⟩ := hoff
  let := hD
  let := hEA
  let := finite_stabilizer d.radical a
  let W := localZSpan d.radical e a
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
  have hs := actual_vertex_projection_sqtk h d ha E f hf hfQ
  have hcent : centralizer (↑(⊤ : Subgroup (Sp E.Carrier)) : Set (Sp E.Carrier))=⊥ := by
    rw [coe_top,centralizer_univ,EvenProjective.center_eq_bot]
  have hnat := ff_card_sp_moved_natural σ ⊤ E.Carrier
    (show Nat.card E.Carrier=2^n by rw [E.card_eq,hE]) h.nonbinary
    (Nat.card_congr (topEquiv : (⊤ : Subgroup (Sp E.Carrier)) ≃* Sp E.Carrier).toEquiv)
    hcent (hs.subgroup ⊤) hfaith ⟨_,hactor⟩
  exact ⟨E,hE,f,hf,hfQ,hD,hEA,σ,hfaith,c,hcoord,hactor,hnat⟩

/-- The actual fixed-radius, large-back branch recognizes the moved section
of the chosen faithful full-span quotient, retaining its reciprocal orientation
and all the original offender coordinates. -/
theorem Input.replacement_distance_four_span_natural_or_reciprocal
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hlarge : Nat.card F < (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u))
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    distanceFourSpanNatural geometry a (path.walk.getVert 2) n ∨
      distanceFourSpanNatural geometry (path.walk.getVert 2) a n := by
  rcases h.replacement_distance_four_span_offender_or_reciprocal d path hb back hmid
    hlarge hfixed with hoff | hoff
  · exact Or.inl (enrich_actual_span_offender h d path.start_color hoff)
  · have he : color d.radical (path.walk.getVert 2)=false :=
      (path.vertex_color (by have hl := path.length_eq_b; omega)).mpr (by decide)
    exact Or.inr (enrich_actual_span_offender h d he hoff)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
