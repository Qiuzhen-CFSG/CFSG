module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.FaithfulDerived
public import Theory.Representation.HexacodeAction.InvariantForms

/-!
# Fixed vectors and the two model obstructions for the faithful radius

The literal moving central quotient is fully moved by the original residual.
Its separating invariant commutator forms consequently force its residual
fixed space to be zero. This assertion does not assume irreducibility or
identify the whole core with a constituent.

If this quotient has the actual hexacode model, every commutator form
vanishes by the even-cover calculation, forcing the moving radius to be
abelian. The established derived-order lower bound excludes that possibility.
Together with the natural-four obstruction this excludes both model markings
at every faithful larger-distance radius. The original exhaustion and all
whole-block clauses, followed by the literal small-MS rank-two consumer, are
proved when either actual marking is supplied.

Exhaustive recognition of this quotient from the original marked action,
the cubic larger-distance branch and natural/exceptional final assembly
remain with task qt-e-ms-small-a6-reconstruction. The conditional model
applications do not establish those remaining source premises.
Source: Meierfrankenfeld--Stellmacher (1993), (3.8), printed pp.878--879;
Aschbacher--Smith C.1.31--32, printed pp.135--136. The imported hexacode
operators retain their documented ATLAS attribution and license.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance
open NaturalStructure.Exclusion
universe u
variable {G : Type u} [Group G] {L R : Subgroup G}
local notation "T" => edge L R

/-- A hexacode marking on the literal central quotient of the moving radius,
retaining the original residual actor and an arbitrary kernel. -/
def HasHexacodeMovingQuotient (a : Vertex T) : Prop :=
  ∃ he : IsElementaryAbelian 2 ((Vcirc T a) ⧸ center (Vcirc T a)),
    letI := he
    ∃ π : pResidual 2 (stabilizer T a) →* Atlas.Codes.HexAutomorphisms,
      Atlas.Codes.hexSign.ker ≤ π.range ∧
      ∃ E : Additive ((Vcirc T a) ⧸ center (Vcirc T a)) ≃ₗ[ZMod 2]
          Atlas.Codes.hexacode,
        ∀ g v, E (Offenders.linearize (movingQuotientAction a) g.val v) =
          Hexacode.action (π g) (E v)

/-- A hexacode-marked central quotient with residual-fixed commutators is
abelian, since its separating commutator forms all vanish. -/
theorem moving_commutative_of_hexacode
    (geometry : Geometry T) (hb : 0 < geometry.b T)
    (a : Vertex T) (ha : color T a = false)
    (hfixed : ⁅V T a,V T a⁆ ≤ fixedCore T a)
    (hn : HasHexacodeMovingQuotient (L := L) (R := R) a) :
    IsMulCommutative (Vcirc T a) := by
  obtain ⟨he,π,hπ,E,hE⟩ := hn
  let := he
  obtain ⟨forms,halt,hsep,hinv⟩ := movingQuotient_separating_forms geometry hb a ha hfixed
  let ρ := (Offenders.linearize (movingQuotientAction a)).comp
    (pResidual 2 (stabilizer T a)).subtype
  have hzero (B : LinearMap.BilinForm (ZMod 2)
      (Additive ((Vcirc T a) ⧸ center (Vcirc T a)))) (hB : B ∈ forms) : B = 0 :=
    Hexacode.invariant_bilinear_eq_zero_of_hexacode_marking ρ π hπ E hE B
      (fun g v w => hinv g.val g.property B hB v w)
  have hvzero (v : Additive ((Vcirc T a) ⧸ center (Vcirc T a))) : v = 0 := by
    apply hsep v
    intro B hB w
    rw [hzero B hB]
    rfl
  refine ⟨⟨fun x y => ?_⟩⟩
  have hx0 := hvzero (Additive.ofMul (QuotientGroup.mk' (center (Vcirc T a)) x))
  have hxq : QuotientGroup.mk' (center (Vcirc T a)) x = 1 := congrArg Additive.toMul hx0
  exact (mem_center_iff.mp ((QuotientGroup.eq_one_iff x).mp hxq) y).symm

variable [Finite G]
variable (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = pCore 2 (L ⊔ R : Subgroup G))
include h e hz hk

omit e hz hk in
/-- Full residual movement and the separating commutator forms leave no
fixed vectors on the literal moving central quotient. -/
theorem movingQuotient_fixedSpace_eq_bot_original
    (geometry : Geometry T) (hb : 2 < geometry.b T)
    (a : Vertex T) (ha : color T a = false)
    (hfixed : ⁅V T a,V T a⁆ ≤ fixedCore T a) :
    letI := moving_central_quotient_elementary geometry (by omega) a ha hfixed
    fixedSpace (Offenders.linearize (movingQuotientAction a))
      (pResidual 2 (stabilizer T a)) = ⊥ := by
  let := moving_central_quotient_elementary geometry (by omega) a ha hfixed
  let ρ := Offenders.linearize (movingQuotientAction a)
  let D := pResidual 2 (stabilizer T a)
  have hfull := movingQuotientAction_full_original h geometry hb a ha hfixed
  obtain ⟨forms,halt,hsep,hinv⟩ := movingQuotient_separating_forms geometry (by omega) a ha hfixed
  apply le_bot_iff.mp
  intro v hv
  apply hsep v
  intro B hB w
  have hker : subspaceCommutator ρ ⊤ D ≤ (B v).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,x,_,rfl⟩
    change B v (ρ g x - x) = 0
    rw [map_sub]
    have he := hinv g hg B hB v x
    change B (ρ g v) (ρ g x) = B v x at he
    rw [show ρ g v = v from hv ⟨g,hg⟩] at he
    rw [he,sub_self]
  rw [hfull] at hker
  exact hker Submodule.mem_top

/-- In particular the faithful larger-distance central quotient has no
residual-fixed attachment. No irreducibility is assumed here. -/
theorem faithful_moving_fixedSpace_eq_bot
    (hb : 2 < sourceDistance h) (a : Vertex T) (ha : color T a = false) :
    letI := moving_central_quotient_elementary (sourceGeometry h) (sourceDistance_pos h)
      a ha (faithful_radius_derived_le_fixed h e hz hk hb a ha)
    fixedSpace (Offenders.linearize (movingQuotientAction a))
      (pResidual 2 (stabilizer T a)) = ⊥ :=
  movingQuotient_fixedSpace_eq_bot_original h (sourceGeometry h) hb a ha
    (faithful_radius_derived_le_fixed h e hz hk hb a ha)

/-- Every faithful exceptional moving radius excludes the hexacode quotient. -/
theorem faithful_moving_not_hexacode (hb : 2 < sourceDistance h)
    (a : Vertex T) (ha : color T a = false) :
    ¬ HasHexacodeMovingQuotient (L := L) (R := R) a := by
  intro hn
  let hcomm := moving_commutative_of_hexacode (sourceGeometry h) (sourceDistance_pos h)
    a ha (faithful_radius_derived_le_fixed h e hz hk hb a ha) hn
  have hlo := faithful_moving_derived_card_lower h e hz hk hb a ha
  rw [commutator_eq_bot,card_bot] at hlo
  omega

/-- Either of the two actual irreducible model markings at one radius
excludes larger faithful distance. Their exhaustive recognition is still required. -/
theorem faithful_distance_eq_two_of_recognized_radius
    (a : Vertex T) (ha : color T a = false)
    (hn : HasNaturalMovingQuotient (L := L) (R := R) a ∨
      HasHexacodeMovingQuotient (L := L) (R := R) a) : sourceDistance h = 2 := by
  apply sourceDistance_eq_two h
  by_contra! hb
  rcases hn with hn | hn
  · exact faithful_moving_not_natural h e hz hk hb a ha hn
  · exact faithful_moving_not_hexacode h e hz hk hb a ha hn

/-- The original entire-core exhaustion follows from either actual quotient
marking. This owner retains the task of recognizing the quotient. -/
theorem coreExhaustion_of_faithful_recognized_radius
    (a : Vertex T) (ha : color T a = false)
    (hn : HasNaturalMovingQuotient (L := L) (R := R) a ∨
      HasHexacodeMovingQuotient (L := L) (R := R) a) : CoreExhaustion L R :=
  coreExhaustion_of_distanceTwo h e hz
    (faithful_distance_eq_two_of_recognized_radius h e hz hk a ha hn)

open ChapterC in
/-- All clauses for the entire intrinsic block, including its central attachment. -/
theorem core_facts_of_faithful_recognized_radius
    (a : Vertex T) (ha : color T a = false)
    (hn : HasNaturalMovingQuotient (L := L) (R := R) a ∨
      HasHexacodeMovingQuotient (L := L) (R := R) a) :
    IsElementaryAbelian 2 (blockU L) ∧
      blockU L ≤ centralizer (pCore 2 L : Set L) ∧
      BlockModuleIrreducible L ∧ Nat.card (blockU L) = 2 ^ 6 ∧
      centralizer (blockU L : Set L) = pCore 2 L :=
  core_facts_of_exhaustion h e hz
    (coreExhaustion_of_faithful_recognized_radius h e hz hk a ha hn)

/-- The actual small-MS rank-two application with the same recognition premise. -/
theorem rankTwo_of_faithful_recognized_radius
    (a : Vertex T) (ha : color T a = false)
    (hn : HasNaturalMovingQuotient (L := L) (R := R) a ∨
      HasHexacodeMovingQuotient (L := L) (R := R) a) : RankTwoAlternatives L R :=
  rankTwo_of_exhaustion h e hz
    (coreExhaustion_of_faithful_recognized_radius h e hz hk a ha hn)

/-- The remaining larger-distance branch has neither actual model on its
moving central quotient, at any original-group vertex. -/
theorem faithful_coreExhaustion_or_unrecognized_radius :
    CoreExhaustion L R ∨
      sourceDistance h = 4 ∧ ∀ a : Vertex T, color T a = false →
        4 ≤ Nat.card (_root_.commutator (Vcirc T a)) ∧
        ¬ HasNaturalMovingQuotient (L := L) (R := R) a ∧
        ¬ HasHexacodeMovingQuotient (L := L) (R := R) a := by
  rcases faithful_coreExhaustion_or_nonNatural_radius h e hz hk with hc | ⟨hb,hr⟩
  · exact Or.inl hc
  · refine Or.inr ⟨hb,fun a ha => ?_⟩
    exact ⟨(hr a ha).1,(hr a ha).2,
      faithful_moving_not_hexacode h e hz hk (by rw [hb]; decide) a ha⟩

/-- The remaining branch is retained in the literal rank-two consumer. -/
theorem faithful_rankTwo_or_unrecognized_radius :
    RankTwoAlternatives L R ∨
      sourceDistance h = 4 ∧ ∀ a : Vertex T, color T a = false →
        4 ≤ Nat.card (_root_.commutator (Vcirc T a)) ∧
        ¬ HasNaturalMovingQuotient (L := L) (R := R) a ∧
        ¬ HasHexacodeMovingQuotient (L := L) (R := R) a :=
  (faithful_coreExhaustion_or_unrecognized_radius h e hz hk).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
