module
public import CFSG.Quasithin.ChapterB.Section02.Baumann.ActionQuotient
public import Theory.ElementaryAbelian.BinaryRankDifference
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# Automorphic copies in the absence of strong offenders

Apply the no-strong-offender bound to an automorphic copy of the elementary
module and to the inverse copy. Transport of relative centralizer indices
makes these bounds opposite, hence equal. Every moving copy is consequently
an offender in the literal centralizer quotient, without any hypothesis that
it has maximum elementary order.

The unitary Baumann consumer uses this to identify every moving normalizer
conjugate with the unique point-radical offender. Source: Aschbacher--Smith
B.1.4(6), B.4.6(13), and the symmetry step of 13.3.10(2), printed p.888.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.BaumannArgument
variable {G H : Type*} [Group G] [Finite G] [Group H]

private theorem fixedCodim_log_index (V A : Subgroup G) [IsElementaryAbelian 2 V] :
    fixedCodim V A = Nat.log 2 ((centralizer (A : Set G)).relIndex V) := by
  rw [fixedCodim,log_card_sub_log_card_eq_log_relIndex V _ inf_le_left,inf_relIndex_left]

private theorem noStrong_index_le (V A : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (hno : NoStrongOffenders V ⊤) :
    Nat.log 2 ((centralizer (V : Set G)).relIndex A) ≤
      Nat.log 2 ((centralizer (A : Set G)).relIndex V) := by
  rw [←actionMap_ker V,relIndex_ker,←fixedCodim_log_index]
  by_cases hz : A.map (actionMap V) = ⊥
  · simp [hz]
  · exact hno A le_top (IsElementaryAbelian.map (actionMap V)) hz

/-- In the absence of strong offenders, an automorphic copy has the same
moving index in both directions. No maximum-elementary assumption is needed. -/
theorem automorphic_image_index_eq (V : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V] (hno : NoStrongOffenders V ⊤) (a : MulAut G) :
    Nat.log 2 ((centralizer (V.map a.toMonoidHom : Set G)).relIndex V) =
      Nat.log 2 ((centralizer (V : Set G)).relIndex (V.map a.toMonoidHom)) := by
  let A := V.map a.toMonoidHom
  let Ai := V.map a.symm.toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map a.toMonoidHom
  let : IsElementaryAbelian 2 Ai := IsElementaryAbelian.map a.symm.toMonoidHom
  have hAi : Ai.map a.toMonoidHom = V := by
    rw [map_map]
    have ha : a.toMonoidHom.comp a.symm.toMonoidHom = MonoidHom.id G := by
      ext g
      exact a.apply_symm_apply g
    rw [ha,Subgroup.map_id]
  have h := noStrong_index_le V Ai hno
  have hleft := relIndex_map_map_of_injective (f := a.toMonoidHom)
    (centralizer (V : Set G)) Ai a.injective
  have hright := relIndex_map_map_of_injective (f := a.toMonoidHom)
    (centralizer (Ai : Set G)) V a.injective
  rw [Theory.GroupTheory.map_centralizer_equiv,hAi] at hleft
  rw [Theory.GroupTheory.map_centralizer_equiv] at hright
  change (centralizer (A : Set G)).relIndex V = _ at hleft
  change (centralizer (Ai.map a.toMonoidHom : Set G)).relIndex A = _ at hright
  rw [hAi] at hright
  rw [←hleft,←hright] at h
  exact le_antisymm h (noStrong_index_le V A hno)

/-- Every moving automorphic copy is a genuine offender in the literal
centralizer quotient action. -/
theorem automorphic_image_isOffender (V : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V] (hno : NoStrongOffenders V ⊤)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G)) (a : MulAut G)
    (hne : ¬ V.map a.toMonoidHom ≤ centralizer (V : Set G)) :
    BinaryOffender.IsOffender (NormalElementaryQuotient.representation V q hq hker)
      ((V.map a.toMonoidHom).map q) := by
  let A := V.map a.toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map a.toMonoidHom
  refine ⟨⟨?_,IsElementaryAbelian.map q⟩,?_⟩
  · intro hz
    exact hne (((map_eq_bot_iff A).mp hz).trans_eq hker)
  · rw [←fixedCodim_eq_centralizer_quotient V q hq hker,
      fixedCodim_log_index,automorphic_image_index_eq V hno a,
      ←hker,relIndex_ker]
    exact le_rfl
end CFSG.Quasithin.ChapterB.BaumannArgument
