module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Dual.Marking
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Dual.Residual

/-!
# The dual-module inclusion in the inside-B branch

For x in [Z_a,Q_c] contained in B_c, construct the actual extension
<x>Z_cD_c/D_c and mark its Z_c-image as the binary natural module. Its
quotient by that image is trivial and its fixed space is zero. If Q_a
and Q_c differ, an involution in the actual image of Q_a fixes x, since
x belongs to Z_a. The checked natural cocycle calculation then places
x in the Z_c-image, excluding the exceptional nonsplit extension. Equal
kernels give trivial displacement. Thus [Z_a,Q_c] lies in Z_cD_c.

The consumer below discharges precisely the dual-module premise of
`exists_conjugate_of_representation_inputs`. The separate (1.6) recognition
premise remains with the inside-branch assembly owner.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1), claim (2), printed p.891, applying (1.5)(i), pp.843--845.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The source dual-module inclusion. B_c is the fixed preimage on V_c/Z_c,
whereas D_c is the literal fixed core used as the quotient denominator.
The common facts already supply b > 2, which suffices for this step. -/
theorem displacement_le_Z_join_fixedCore
    (common : CommonFacts R source geometry) (_hb : 4 < geometry.b R)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hB : ⁅Z R a,Q R c⁆ ≤ B R c (geometry.Z_normal c)) :
    ⁅Z R a,Q R c⁆ ≤ Z R c ⊔ fixedCore R c := by
  intro x hx
  by_cases hfixed : x ∈ fixedCore R c
  · exact (show fixedCore R c ≤ Z R c ⊔ fixedCore R c from le_sup_right) hfixed
  by_cases heq : Q R c = Q R a
  · have hbot : ⁅Z R a,Q R c⁆ = ⊥ := by rw [heq]; exact geometry.centralizes a ha
    have hxone : x = 1 := hbot.le hx
    rw [hxone]
    exact (Z R c ⊔ fixedCore R c).one_mem
  let modules := moduleFacts common
  let data := Dual.pointData common ha hc hd hB x hx
  obtain ⟨A⟩ := Dual.action_nonempty modules hc data
  let := A.normal
  let := A.elementary
  obtain ⟨marking,e,he⟩ := Dual.action_hasNaturalMarking modules c x hc A
  obtain ⟨g,hg,hgne,hgfix⟩ := Dual.fixed_involution_exists common ha hc hd heq x hx A
  let xH : Dual.carrier c x := ⟨x,
    (show zpowers x ≤ Dual.carrier c x from le_sup_left.trans le_sup_left) (mem_zpowers x)⟩
  have hv := DistanceFour.Early.Containment.Transfer.SpanBound.fixed_involution_mem_natural_sup_fixed
    A.representation A.natural marking e he
    (Dual.action_hasTrivialQuotient modules hc data A) g hg hgne
    (Additive.ofMul (QuotientGroup.mk' ((fixedCore R c).subgroupOf (Dual.carrier c x)) xH))
    (hgfix xH rfl)
  rw [Dual.action_fixed_eq_bot modules hc data A, sup_bot_eq] at hv
  exact (A.mem_natural_iff xH).mp hv

/-- Apply the proved dual inclusion to the actual inside-branch consumer.
Only the independent escaping-span recognition from (1.6) remains explicit. -/
theorem exists_conjugate_of_escaping_recognition
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c e : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hB : ⁅Z R a, Q R c⁆ ≤ B R c (geometry.Z_normal c))
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c)
    (hnone : ¬ HasNaturalSection R a c)
    (htriple : ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c)
    (p : CriticalPath R geometry c e)
    (hrecognition : ∀ x : stabilizer R c,
      (x : FreeAmalgam R) ∈ ⁅Z R a, Q R c⁆ →
      (x : FreeAmalgam R) ∉ fixedCore R c →
      (x : FreeAmalgam R) ∈ Z R c ⊔ fixedCore R c →
      ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c →
      (Z R c).relIndex ⁅escapingSpan a c e x, Z R e⁆ ≤ 2 →
      HasNaturalSection R a c) :
    ∃ g ∈ stabilizer R c,
      ¬ Z R (act R g a) ≤ Q R (p.walk.getVert (p.walk.length - 2)) ∧
      ⁅⁅Z R (act R g a), Q R c⁆, Z R e⁆ ≠ ⊥ :=
  exists_conjugate_of_representation_inputs common hb ha hc hd hB hn hnone htriple p
    (fun _ hx => displacement_le_Z_join_fixedCore common hb ha hc hd hB hx) hrecognition

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside
