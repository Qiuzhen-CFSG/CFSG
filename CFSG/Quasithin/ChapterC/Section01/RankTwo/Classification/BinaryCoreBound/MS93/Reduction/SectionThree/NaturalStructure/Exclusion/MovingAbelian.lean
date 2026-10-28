module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.Radius
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.MovingAbelian.Pairing
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.MovingAbelian.Displacement
public import Theory.Representation.PSL3Two.ResidualFFForms

/-!
# The moving-radius representation argument

The actual moving radius has an elementary central quotient with a
commutator-generated residual action and separating residual-invariant
alternating forms. The geometric displacement estimate and the binary
constituent obstruction are the remaining inputs to abelianness; none is
assumed as a source hypothesis here.

Source: Meierfrankenfeld--Stellmacher (1993), (3.8), printed p.878.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open ModuleAlternatives
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/- The projected actor and the residual-invariant separating commutator forms
close the binary representation step of MS93 (3.8). -/
theorem moving_commutative_of_badCase_of_derived_fixed
    (source : LocalSource L R) (geometry : Geometry R) (hb : 2 < geometry.b R)
    (hbad : BadCase source) (a : Vertex R) (ha : color R a = false)
    (hfixed : ⁅V R a, V R a⁆ ≤ fixedCore R a) :
    IsMulCommutative (Vcirc R a) := by
  let := moving_central_quotient_elementary geometry (by omega) a ha hfixed
  let := finite_moving geometry hb a ha
  let := finite_stabilizer R a
  let ρ := Offenders.linearize (movingQuotientAction a)
  obtain ⟨π, A, hπ, hker, hA, hmap, hcost⟩ :=
    moving_projected_offender source geometry hb hbad a ha hfixed
  have hfull := movingQuotientAction_full source geometry hb a ha hfixed
  obtain ⟨forms, halt, hsep, hinv⟩ :=
    movingQuotient_separating_forms geometry (by omega) a ha hfixed
  have hzero (B : LinearMap.BilinForm (ZMod 2)
      (Additive ((Vcirc R a) ⧸ center (Vcirc R a)))) (hB : B ∈ forms) : B = 0 := by
    exact BinaryLinearThree.ResidualFFForms.form_zero_of_projected_SL3_residual_invariance
      π hπ (by rw [hker]; exact (Q_isPGroup R source.two_group source.core_le a ha).comap_subtype)
      ρ hfull A hA hmap hcost B (by
        intro g hg v w
        exact hinv g hg B hB v w)
  have hvzero (v : Additive ((Vcirc R a) ⧸ center (Vcirc R a))) : v = 0 := by
    apply hsep v
    intro B hB w
    rw [hzero B hB]
    rfl
  refine ⟨⟨fun x y => ?_⟩⟩
  have hx0 := hvzero (Additive.ofMul (QuotientGroup.mk' (center (Vcirc R a)) x))
  have hxq : QuotientGroup.mk' (center (Vcirc R a)) x = 1 :=
    congrArg Additive.toMul hx0
  have hxc : x ∈ center (Vcirc R a) := (QuotientGroup.eq_one_iff x).mp hxq
  exact (mem_center_iff.mp hxc y).symm

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
