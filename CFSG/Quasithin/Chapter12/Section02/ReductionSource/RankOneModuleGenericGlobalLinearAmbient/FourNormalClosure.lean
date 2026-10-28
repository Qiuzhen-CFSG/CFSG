module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.FourClosureAlternatives
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLinearAmbient.FourSylow

/-!
# The exceptional normal closure in the original Chapter12 row

The original chosen module supplies the unchanged generic Input. In the
degree-two row the central-line normal closure lies in the actual
involution-centralizer two-core and has elementary central quotient.
Its abelian and inside-S cases now give the source centralizer bound.
The same marked quaternion subgroup supplies a binary flag and the
normal-closure orbit supplies the literal Sylow-index lower bound. These
discharge the exceptional quaternion contradiction. Together with the
large-field branch, every original degree now satisfies the source
centralizer intersection bound. Ambient recognition and GlobalExit remain
separate obligations.
Source: Aschbacher--Smith §5.3.7, pp.660--661, used in §12.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (d : Global.Preparation T L H A B (residual H))
  (hp : Group.IsPerfect (residual H))
  (F : Type) [Field F] [Finite F] [CharP F 2]
  {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
  (he : Nonempty (RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
    (LinearThree.amalgam F)) ∨
    Nonempty (RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
    (LinearThree.amalgam F).reverse))
  (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include D h hmany hn hpsl hH d hp hm hF he hmax

/-- The source four-group normal closure lies in the literal two-core,
with squares in the same original involution subgroup. -/
theorem rankOne_global_linear_four_normalClosure (hn2 : n=2)
    (z : G) (hz2 : orderOf z=2) (hz : z ∈ centerIn (Global.sourceS L H))
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    Global.linearCentralLineClosure L H z ≤ (centralizer ({z} : Set G)).pCoreIn 2 ∧
      ∀ x ∈ Global.linearCentralLineClosure L H z, x^2 ∈ zpowers z :=
  d.linear_four_normalClosure (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax hn2 z hz2 hz hzT

/-- The abelian normal-closure branch discharges the actual centralizer
bound, with no hyperplane-centralizer callback. -/
theorem rankOne_global_linear_four_centralizer_of_abelian_normalClosure (hn2 : n=2)
    (z : G) (hz2 : orderOf z=2) (hz : z ∈ centerIn (Global.sourceS L H))
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hab : IsMulCommutative (Global.linearCentralLineClosure L H z)) :
    centralizer ({z} : Set G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) :=
  d.linear_four_centralizer_le_inter_of_abelian_normalClosure
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hmax hn2 z hz2 hz hzT hab

/-- The literal degree-two row has either the source centralizer bound or
the actual self-centralizing quaternion normal closure, with both planes
retained under a single marked Sylow isomorphism. -/
theorem rankOne_global_linear_four_centralizer_or_quaternion_closure (hn2 : n=2) :
    (∃ z : G, orderOf z=2 ∧ z ∈ centerIn (Global.sourceS L H) ∧
      centralizer ({z} : Set G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G)) ∨
    ∃ c : Chapter5.Section03ExceptionalSylowModel.MarkedCopy G,
      c.carrier=(T : Subgroup G) ∧ c.S=Global.sourceS L H ∧
      ((c.V₁=L.pCoreIn 2 ∧ c.V₂=(residual H).pCoreIn 2) ∨
       (c.V₁=(residual H).pCoreIn 2 ∧ c.V₂=L.pCoreIn 2)) ∧
      c.Z=centerIn (Global.sourceS L H) ∧ orderOf c.z=2 ∧
      (T : Subgroup G) ≤ centralizer ({c.z} : Set G) ∧
      Global.linearCentralLineClosure L H c.z=c.Q ∧
      c.Q ≤ (centralizer ({c.z} : Set G)).pCoreIn 2 ∧
      centralizer ({c.z} : Set G) ≤ normalizer (c.Q : Set G) ∧
      centralizer ({c.z} : Set G) ⊓ centralizer (c.Q : Set G) ≤ c.Q ∧
      4 ≤ (T : Subgroup G).relIndex (centralizer ({c.z} : Set G)) :=
  d.linear_four_centralizer_or_quaternion_closure
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hmax hn2

/-- The exceptional degree-two source branch has its actual centralizer
bound, with the same-Sylow quaternion alternative completely eliminated. -/
theorem rankOne_global_linear_four_exists_centralizer_le_inter (hn2 : n=2) :
    ∃ z : G, orderOf z=2 ∧ z ∈ centerIn (Global.sourceS L H) ∧
      centralizer ({z} : Set G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) :=
  d.linear_four_exists_centralizer_le_inter
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hmax hn2

/-- The original Chapter12 row satisfies source §5.3.7 at every original
degree and in either orientation, without an extra centralizer premise. -/
theorem rankOne_global_linear_centralizer_le_inter
    (z : G) (hz2 : orderOf z=2) (hz : z ∈ centerIn (Global.sourceS L H)) :
    centralizer ({z} : Set G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) :=
  d.linear_centralizer_le_inter (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax z hz2 hz

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
