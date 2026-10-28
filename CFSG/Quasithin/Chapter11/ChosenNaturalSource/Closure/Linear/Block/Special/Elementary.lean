module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Sections
public import Theory.Frattini.PGroup

/-!
# The original elementary central quotient

The marked point lies in Z(U). Thus the given Frattini bound Φ(U)≤V₁
puts Φ(U) in Z(U), and the quotient U/Z(U) is elementary abelian.
This uses the literal closure U=E.W and no special-group hypothesis.
Source: Aschbacher--Smith 11.5.7, refs/quasithin.pdf, printed p.782.
-/

@[expose] public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)

include d

theorem point_le_center : E.V₁ ≤ closureCenter E := by
  intro v hv
  refine ⟨⟨v, le_conjugateSpanBy V E.G₁ (E.V₁_le hv)⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro u
  apply Subtype.ext
  exact (d.setup.toBaseHypothesis.U_le_centralizer_point u.property v hv).symm

theorem frattini_le_center
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁) :
    frattini E.W ≤ center E.W := by
  intro u hu
  obtain ⟨z, hz, he⟩ := point_le_center E d (hf (mem_map_of_mem E.W.subtype hu))
  exact (Subtype.ext he : z = u) ▸ hz

theorem centralQuotient_elementary
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁) :
    IsElementaryAbelian 2 (CentralQuotient E) := by
  let : Fact (IsPGroup 2 E.W) := ⟨d.U_isPGroup hUT⟩
  refine { toIsMulCommutative := (Subgroup.Normal.quotient_commutative_iff_commutator_le
    (N := center E.W)).mpr ((commutator_le_frattini_of_isPGroup (p := 2)).trans
      (frattini_le_center E d hf)), exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro u
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (center E.W) u
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr
    (frattini_le_center E d hf (pth_power_mem_frattini_of_isPGroup (p := 2) u))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
