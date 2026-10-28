module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldCubicNormalizing
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesCentralizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeDefs
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearField

/-!
# The original three-prime centralizer kernel

Maximality of the actual residual in L(G,T) makes its normalizer a
two-local. Quasithinness supplies the odd-rank bound, and the literal
residual quotient transfers through its inclusion in G. The resulting
kernel theorem is 5.1.16(1), before choosing any cubic Cartan or imposing
parity. It is shared by the parity, normalizing and escaping branches.

Source: Aschbacher--Smith, 5.1.14(1) and 5.1.16(1), printed pp.638--639.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H : Subgroup G}

/-- 5.1.16(1) on the original normalizer action. No parity or cubic
normalization premise is needed. -/
theorem linear_residual_action_kernel_three_prime
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    Nat.Coprime 3 (Nat.card (linearResidualAction H).ker) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.simpleQTKE T hK
  have horbit : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
      (hH.1.1.2.trans (le_normalizer_residual H))) (le_componentOrbit _ _)
  have hmax : IsMaximalTwoLocal (normalizer (residual H : Set G)) := by
    simpa only [horbit] using hu.normalizer_maximal
  have hsq : IsStronglyQuasithin (normalizer (residual H : Set G)) :=
    (isQuasithin_iff_twoLocal.mp h.simpleQTKE.quasithin) _ hmax.1
  let e := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let q := QuotientGroup.congr (pCore 2 (pResidual 2 H)) (pCore 2 (residual H))
    e (pCore_map_iso 2 e)
  exact CubicEscape.quotientAction_kernel_three_prime (residual H) hsq
    (hlinear.of_mulEquiv q.symm)

/-- The same three-prime kernel on the literal point-centralizer action
used in 5.1.23. Relative containment comes from 5.1.14(2). -/
theorem linear_cubic_point_action_kernel_three_prime
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {C : Subgroup G} {z : G} (d : CubicEscape.LocalData T H C z) :
    let i := inclusion (point_centralizer_le_residual_normalizer
      h.simpleQTKE hH.1.1 hK hnf d.point_mem d.point_ne)
    Nat.Coprime 3 (Nat.card ((linearResidualAction H).comp i).ker) := by
  dsimp only
  let i := inclusion (point_centralizer_le_residual_normalizer
    h.simpleQTKE hH.1.1 hK hnf d.point_mem d.point_ne)
  let f : ((linearResidualAction H).comp i).ker →* (linearResidualAction H).ker :=
    { toFun := fun x => ⟨i x, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : (linearResidualAction H).ker => ((a : normalizer
      (residual H : Set G)) : G)) he
  exact (linear_residual_action_kernel_three_prime h hH hK hlinear).coprime_dvd_right
    (card_dvd_of_injective f hf)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
