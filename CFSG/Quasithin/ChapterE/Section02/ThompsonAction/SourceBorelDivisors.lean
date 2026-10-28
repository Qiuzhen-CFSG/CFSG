module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleBaumann
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedAlphaCard
public import Theory.SpecificGroups.SL2.NormalLayerBorelDivisors
/-!
# Borel divisors for the actual single and paired source markers

The genuine single source has a normal generalized Fitting SL2 layer, and the paired
source marks the normal offender group by SL2 squared. Their actual layer
Sylow normalizers contribute q(q-1) and (q-1)^2 to every maximal subgroup
containing all proper overgroups of the prescribed Sylow. The full ambient
quotient can retain semilinear automorphisms or a factor exchanger.

Source: Aschbacher--Smith E.2.3 and 10.2.3(4), printed p.746.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
theorem quasisimple_linear_borel_card_dvd_of_proper_overgroups
    (T : Sylow 2 G)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (s : MovedSection ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (F : BinaryField)
    (hnatural : IsLinearNatural (s.action.comp (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))).subtype) F 2)
    (M : Subgroup G)
    (hM : ∀ J : Subgroup G, (T : Subgroup G) ≤ J → J ≠ ⊤ → J ≤ M) :
    Nat.card F.Carrier * (Nat.card F.Carrier - 1) ∣ Nat.card M := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let A := generalizedFitting Y
  let := offenderSubgroup_normal α
  obtain ⟨e⟩ := hnatural
  let L := A.map Y.subtype
  let : L.Normal := by change (A.map Y.subtype).Normal; infer_instance
  let eg := (A.equivMapOfInjective Y.subtype Y.subtype_injective).symm.trans e.groupEquiv
  exact Matrix.SpecialLinearGroup.normal_layer_borel_card_dvd_of_proper_overgroups
    T q hq L eg M hM

theorem paired_linear_borel_odd_square_dvd_of_proper_overgroups
    (T : Sylow 2 G)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    (M : Subgroup G)
    (hM : ∀ J : Subgroup G, (T : Subgroup G) ≤ J → J ≠ ⊤ → J ≤ M) :
    (Nat.card F.Carrier - 1)^2 ∣ Nat.card M := by
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  exact Matrix.SpecialLinearGroup.normal_pair_borel_odd_square_dvd_of_proper_overgroups
    T q hq Y c.action.groupEquiv M hM
end CFSG.Quasithin.ChapterE.ThompsonAction
