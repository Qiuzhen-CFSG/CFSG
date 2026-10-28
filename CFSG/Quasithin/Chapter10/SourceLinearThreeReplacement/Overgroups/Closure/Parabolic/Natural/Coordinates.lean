module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.Coordinates
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.Model

/-!
# Canonical coordinates on the original two moved eight-groups

Multiplication identifies the disjoint commuting factors with the original
full module. The first marking is precisely the survivor's supplied natural
coordinate map; the second is its transport through the specified exchanger.
Consequently the original diagonal involution has two nonzero coordinates.
No choice of an unrelated abstract module action enters this construction.

Source: Aschbacher--Smith 10.1.1(3) and 10.2.11, pp.741,753.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
open Chapter3.Section02 Geometry.Escape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  (s : SourceLinearThreeSurvivor T D)

private def pairFunction : (Eight × Eight) ≃* Space where
  toFun v i := if i = 1 then v.1 else v.2
  invFun v := (v 1, v (Multiplicative.ofAdd 1))
  left_inv v := by simp
  right_inv v := by
    funext i
    have hi : ∀ i : Bit, i = 1 ∨ i = Multiplicative.ofAdd 1 := by decide
    rcases hi i with rfl | rfl <;>
      simp [show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 from by decide]
  map_mul' v w := by
    funext i
    by_cases hi : i = 1 <;> simp [hi]

private theorem factors_commute :
    ⁅D.fullModule,L⁆ ≤ centralizer
      (((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) : Set G) := by
  let _ : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  intro a ha b hb
  exact congrArg Subtype.val (mul_comm
    (⟨b,survivor_partner_le s hb⟩ : D.fullModule) ⟨a,survivor_moved_le s ha⟩)

/-- Multiplication of the actual factors, with its literal ambient formula. -/
def factorProduct
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    (⁅D.fullModule,L⁆ : Subgroup G) ×
      ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) ≃* D.fullModule :=
  (Classical.choose (exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    ⁅D.fullModule,L⁆ ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)
    (survivor_pair_disjoint s hz) (factors_commute s))).trans
      (MulEquiv.subgroupCongr s.generated.symm)

theorem factorProduct_apply
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (a : (⁅D.fullModule,L⁆ : Subgroup G))
    (b : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)) :
    (factorProduct s hz (a,b) : G) = (a : G) * b :=
  Classical.choose_spec (exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    ⁅D.fullModule,L⁆ ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)
    (survivor_pair_disjoint s hz) (factors_commute s)) a b

/-- Transport of the original coordinates through the specified exchange. -/
def partnerCoordinates
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) ≃* Eight :=
  ((MulAut.conj s.exchange).subgroupMap ⁅D.fullModule,L⁆).symm.trans
    (movedCoordinates s hz)

theorem partnerCoordinates_conj
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (a : (⁅D.fullModule,L⁆ : Subgroup G)) :
    partnerCoordinates s hz ((MulAut.conj s.exchange).subgroupMap ⁅D.fullModule,L⁆ a) =
      s.natural.coordinates a := by
  change movedCoordinates s hz
    (((MulAut.conj s.exchange).subgroupMap ⁅D.fullModule,L⁆).symm
      (((MulAut.conj s.exchange).subgroupMap ⁅D.fullModule,L⁆) a)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- Canonical full-module coordinates on the two original exchanged factors. -/
def fullCoordinates
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    D.fullModule ≃* Space :=
  (factorProduct s hz).symm.trans
    (((movedCoordinates s hz).prodCongr (partnerCoordinates s hz)).trans pairFunction)

theorem fullCoordinates_mul
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (a : (⁅D.fullModule,L⁆ : Subgroup G))
    (b : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)) (i : Bit) :
    fullCoordinates s hz
      ⟨(a : G) * b, D.fullModule.mul_mem (survivor_moved_le s a.property)
        (survivor_partner_le s b.property)⟩ i =
      if i = 1 then s.natural.coordinates a else partnerCoordinates s hz b := by
  have he : (⟨(a : G) * b, D.fullModule.mul_mem (survivor_moved_le s a.property)
      (survivor_partner_le s b.property)⟩ : D.fullModule) = factorProduct s hz (a,b) :=
    Subtype.ext (factorProduct_apply s hz a b).symm
  rw [he]
  change pairFunction (((movedCoordinates s hz).prodCongr (partnerCoordinates s hz))
    ((factorProduct s hz).symm (factorProduct s hz (a,b)))) i = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The source diagonal has two nonidentity coordinates in this exact marking. -/
theorem diagonal_coordinates_ne_one
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    {a b : G} (ha : a ∈ ⁅D.fullModule,L⁆)
    (hb : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (i : Bit) :
    fullCoordinates s hz
      ⟨a*b, D.fullModule.mul_mem (survivor_moved_le s ha)
        (survivor_partner_le s hb)⟩ i ≠ 1 := by
  rw [fullCoordinates_mul s hz ⟨a,ha⟩ ⟨b,hb⟩]
  split_ifs
  · intro he
    have he' : movedCoordinates s hz ⟨a,ha⟩ = 1 := he
    exact ha1 (congrArg Subtype.val ((movedCoordinates s hz).map_eq_one_iff.mp he'))
  · intro he
    exact hb1 (congrArg Subtype.val ((partnerCoordinates s hz).map_eq_one_iff.mp he))

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
