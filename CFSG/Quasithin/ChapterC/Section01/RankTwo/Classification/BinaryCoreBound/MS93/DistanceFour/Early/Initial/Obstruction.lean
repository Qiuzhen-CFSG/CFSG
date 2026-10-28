module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Obstruction.Actor
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Obstruction.Forms
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Obstruction.Pairing

/-!
# The binary radius offender obstruction

Small displacement on the literal V/Z gives a simple-constituent budget for
the actual actor. The residual commutator subspace therefore lies in the
radical of every residual-invariant binary form. Applying this to the
commutator pairing modulo U gives [Vcirc,V] ≤ U. The decomposition
V = Vcirc ∨ V_b, with V_b abelian, finishes V' ≤ U.

The center premise is retained in the conditional source interface below.
The binary pairing proof already has V' ≤ Z and does not need that premise;
it does not assume centrality of [V,Q] or construct `InitialFacts`.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.2), printed pp.901--902.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial

variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The conditional binary obstruction in MS93 (4.6.2): an actor with the
intrinsic Frattini condition and small displacement on V/Z forces V' ≤ U.
The center premise from (4.6.1) is retained for the source assembly, although
the binary form argument proves the conclusion without using it. -/
theorem radius_offender_obstruction [Finite M]
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (_hcenter : ∀ c, color R c = false →
      (center (V R c)).map (V R c).subtype ≤ B R c (geometry.Z_normal c))
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ Q R b) (hnot : ¬ A ≤ Q R a)
    (hPhi : (frattini A).map A.subtype ≤ Q R a)
    (hsmall : (radiusFixed geometry a A).relIndex (V R a) ≤ (Q R a).relIndex A) :
    ⁅V R a, V R a⁆ ≤ U R a := by
  apply radius_derived_le_U_of_form_radical common hb a b ha hab
  let := radiusZ_normal common a ha
  let := radiusQuotient_elementary common hb a ha
  let := finite_stabilizer R a
  let := finite_radius common a ha
  obtain ⟨d, hbudget, hcost⟩ :=
    radius_offender_budget common hb a b ha hab A hA hnot hPhi hsmall
  intro B hB
  exact form_annihilates_residual_commutator (radiusRepresentation common hb a ha)
    (A.subgroupOf (stabilizer R a)) d hbudget hcost B hB

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
