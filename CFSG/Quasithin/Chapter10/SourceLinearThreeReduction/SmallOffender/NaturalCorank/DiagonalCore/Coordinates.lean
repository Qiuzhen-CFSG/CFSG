module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.DiagonalCore.Pair
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.Model

/-!
# Coordinates on the earlier natural pair

Vanishing of the full fixed part makes the supplied moved-section coordinates
injective. Transport through the specified exchanger identifies the second
factor, and multiplication identifies their product with the full module.
The original component therefore acts on exactly the first coordinate.

The adapted proofs below come from the indicated modules under
`SourceLinearThreeReplacement/`; their survivor parameters have been replaced
by the earlier pair, retaining all literal subgroup maps and coordinates.
Source: Aschbacher--Smith 10.1.1(3) and 10.2.11, printed pp.741,753.
-/

public noncomputable section
-- Adapted from Geometry/Escape/Coordinates.lean.
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.Escape
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  (s : SourceLinearThreePair T D)

include s

/-- The specified exchange gives the literal two-component orbit. -/
theorem orbit_eq_pair :
    localOrbit T L = L ⊔ L.map (MulAut.conj s.exchange).toMonoidHom := by
  apply le_antisymm
  · apply iSup_le
    intro t
    rcases source_nonnormal_maximal_pair D (pair_nonnormal s)
      s.exchange_mem s.exchange_moves t (le_normalizer_componentOrbit L T t.property)
      with h | h
    · exact h.le.trans le_sup_left
    · exact h.le.trans le_sup_right
  · refine sup_le (le_componentOrbit L T) ?_
    exact le_iSup (fun t : (T : Subgroup G) =>
      L.map (MulAut.conj (t : G)).toMonoidHom) ⟨s.exchange,s.exchange_mem⟩

/-- The first moved factor centralizes the exchanged component. -/
theorem moved_centralizes_partner_component :
    ⁅D.fullModule,L⁆ ≤ centralizer
      (L.map (MulAut.conj s.exchange).toMonoidHom : Set G) := by
  have hback : L.map (MulAut.conj s.exchange⁻¹).toMonoidHom =
      L.map (MulAut.conj s.exchange).toMonoidHom := by
    rcases source_nonnormal_maximal_pair D (pair_nonnormal s)
      s.exchange_mem s.exchange_moves s.exchange⁻¹
      (le_normalizer_componentOrbit L T ((T : Subgroup G).inv_mem s.exchange_mem))
      with h | h
    · exact (s.exchange_moves (by simpa only [inv_inv] using
        (normalizer (L : Set G)).inv_mem (mem_normalizer_iff_map_conj_eq.mpr h))).elim
    · exact h
  intro a ha
  rw [← hback]
  rintro _ ⟨l,hl,rfl⟩
  have hh := congrArg (MulAut.conj s.exchange⁻¹)
    (s.crossed (mem_map_of_mem (MulAut.conj s.exchange).toMonoidHom ha) l hl)
  simpa [MulAut.conj_apply, mul_assoc] using hh

/-- The section denominator vanishes with the full fixed part. -/
theorem moved_fixed_eq_bot
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) = ⊥ := by
  apply bot_unique
  intro x hx
  apply hz.le
  refine ⟨pair_moved_le s hx.1,?_⟩
  rw [orbit_eq_pair s]
  exact le_centralizer_iff.mpr (sup_le
    (le_centralizer_iff.mp (zpowers_le.mpr hx.2))
    (le_centralizer_iff.mp (zpowers_le.mpr (moved_centralizes_partner_component s hx.1))))
      (mem_zpowers x)

/-- The natural pair coordinates identify the original moved factor with the natural space. -/
@[expose] def movedCoordinates
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ↥(⁅D.fullModule,L⁆ : Subgroup G) ≃* Multiplicative (Fin 3 → ZMod 2) :=
  MulEquiv.ofBijective s.natural.coordinates ⟨(MonoidHom.ker_eq_bot_iff _).mp
    (by rw [s.natural.kernel_eq, moved_fixed_eq_bot s hz, bot_subgroupOf]),s.natural.onto⟩

/-- The original natural moved factor has order eight. -/
theorem moved_card
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    Nat.card (⁅D.fullModule,L⁆ : Subgroup G) = 8 := by
  have hc := s.natural.card_section
  rw [moved_fixed_eq_bot s hz, card_bot] at hc
  norm_num [Nat.card_fun, Nat.card_fin, Nat.card_zmod] at hc ⊢
  exact hc

/-- Both exchanged factors contribute: the full module has order sixty-four. -/
theorem full_card
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    Nat.card D.fullModule = 64 := by
  let A := ⁅D.fullModule,L⁆
  let B := A.map (MulAut.conj s.exchange).toMonoidHom
  let : IsElementaryAbelian 2 D.fullModule := s.full_eq_local.symm ▸ D.module_elementary
  have hc : A ≤ centralizer (B : Set G) := by
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm
      (⟨b,pair_partner_le s hb⟩ : D.fullModule) ⟨a,pair_moved_le s ha⟩)
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B
    (pair_pair_disjoint s hz) hc
  have hB : Nat.card B = Nat.card A := card_map_of_injective (MulAut.conj s.exchange).injective
  have hV : Nat.card D.fullModule = Nat.card A * Nat.card B := by
    rw [s.generated]
    exact (Nat.card_congr e.toEquiv).symm.trans (Nat.card_prod A B)
  rw [hV, hB, show Nat.card A = 8 from moved_card s hz]

/-- The maximal local group also permutes the exchanged moved factor. -/
theorem partner_pair (g : G) (hg : g ∈ D.maximalLocal) :
    ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom).map
        (MulAut.conj g).toMonoidHom = ⁅D.fullModule,L⁆ ∨
    ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom).map
        (MulAut.conj g).toMonoidHom =
      (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom := by
  have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj s.exchange).toMonoidHom =
      (MulAut.conj (g * s.exchange)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [map_map, he]
  exact pair_moved_pair s _
    (D.maximalLocal.mul_mem hg (le_normalizer_componentOrbit L T s.exchange_mem))

/-- The equivalence uses the pair's specified coordinates without changing the action. -/
theorem movedCoordinates_apply
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (a : ↥(⁅D.fullModule,L⁆ : Subgroup G)) :
    movedCoordinates s hz a = s.natural.coordinates a := rfl

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.Escape

-- Adapted from Overgroups/Closure/Parabolic/Natural/Coordinates.lean.
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Overgroups.Closure.Parabolic.Natural
open CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
open Chapter3.Section02 Geometry.Escape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  (s : SourceLinearThreePair T D)

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
    (⟨b,pair_partner_le s hb⟩ : D.fullModule) ⟨a,pair_moved_le s ha⟩)

/-- Multiplication of the actual factors, with its literal ambient formula. -/
def factorProduct
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    (⁅D.fullModule,L⁆ : Subgroup G) ×
      ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) ≃* D.fullModule :=
  (Classical.choose (exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    ⁅D.fullModule,L⁆ ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)
    (pair_pair_disjoint s hz) (factors_commute s))).trans
      (MulEquiv.subgroupCongr s.generated.symm)

theorem factorProduct_apply
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (a : (⁅D.fullModule,L⁆ : Subgroup G))
    (b : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)) :
    (factorProduct s hz (a,b) : G) = (a : G) * b :=
  Classical.choose_spec (exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    ⁅D.fullModule,L⁆ ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)
    (pair_pair_disjoint s hz) (factors_commute s)) a b

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
      ⟨(a : G) * b, D.fullModule.mul_mem (pair_moved_le s a.property)
        (pair_partner_le s b.property)⟩ i =
      if i = 1 then s.natural.coordinates a else partnerCoordinates s hz b := by
  have he : (⟨(a : G) * b, D.fullModule.mul_mem (pair_moved_le s a.property)
      (pair_partner_le s b.property)⟩ : D.fullModule) = factorProduct s hz (a,b) :=
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
      ⟨a*b, D.fullModule.mul_mem (pair_moved_le s ha)
        (pair_partner_le s hb)⟩ i ≠ 1 := by
  rw [fullCoordinates_mul s hz ⟨a,ha⟩ ⟨b,hb⟩]
  split_ifs
  · intro he
    have he' : movedCoordinates s hz ⟨a,ha⟩ = 1 := he
    exact ha1 (congrArg Subtype.val ((movedCoordinates s hz).map_eq_one_iff.mp he'))
  · intro he
    exact hb1 (congrArg Subtype.val ((partnerCoordinates s hz).map_eq_one_iff.mp he))

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Overgroups.Closure.Parabolic.Natural

-- Adapted from Overgroups/Closure/Parabolic/Natural/Inputs.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Overgroups.Closure.Parabolic.Natural
open CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original conjugation action, restricted to L₀T. -/
@[expose] def joinAction (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    localJoin T L →* MulAut D.fullModule :=
  D.fullModule.normalizerMonoidHom.comp (inclusion
    ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)).trans
      D.maximalLocal_normalizes_fullModule))

theorem joinAction_apply (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (g : localJoin T L) (v : D.fullModule) :
    (joinAction D g v : G) = (g : G) * v * (g : G)⁻¹ := rfl

theorem joinAction_ker (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    (joinAction D).ker = (centralizer (D.fullModule : Set G)).subgroupOf (localJoin T L) := by
  ext g
  change D.fullModule.normalizerMonoidHom (inclusion _ g) = 1 ↔ _
  rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
  rfl

/-- A marking of the whole original action, before selecting any parabolic.
The coordinates are fixed by the natural pair and its specified exchanger. -/
structure ActionData {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (s : SourceLinearThreePair T D)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) where
  hom : localJoin T L →* Actor
  onto : Function.Surjective hom
  kernel_two : IsPGroup 2 hom.ker
  equivariant (g : localJoin T L) (v : D.fullModule) :
    fullCoordinates s hz (joinAction D g v) = action (hom g) (fullCoordinates s hz v)


end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Overgroups.Closure.Parabolic.Natural

-- Adapted from Overgroups/Closure/Parabolic/Natural/OriginalAction/Coordinates.lean.
open Subgroup Theory.GroupTheory
open scoped Matrix
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Overgroups.Closure.Parabolic.Natural.OriginalAction
open CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
open Chapter3.Section02 Geometry.Escape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  (s : SourceLinearThreePair T D)
  (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)

/-- Only a lift of the original action; neither its image nor its kernel is assumed. -/
structure LiftData where
  hom : localJoin T L →* Actor
  equivariant (g : localJoin T L) (v : D.fullModule) :
    fullCoordinates s hz (joinAction D g v) = action (hom g) (fullCoordinates s hz v)

/-- The inclusion of the original component in its Sylow join. -/
@[expose] def componentInclusion : L →* localJoin T L :=
  inclusion ((le_componentOrbit L T).trans le_sup_left)

/-- The prescribed component quotient, without a new choice of model. -/
@[expose] def componentHom : L →* Matrix.PSL3Two.SL :=
  s.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

theorem componentHom_surjective : Function.Surjective (componentHom s) :=
  s.quotient.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The first base factor in the literal wreath convention. -/
@[expose] def firstBase : Matrix.PSL3Two.SL →* Actor where
  toFun a := ⟨fun i => if i = 1 then a else 1, 1⟩
  map_one' := by ext i <;> simp
  map_mul' a b := by
    ext i
    · by_cases hi : i = 1 <;> simp [hi]
    · simp

theorem firstBase_action (a : Matrix.PSL3Two.SL) (v : Space) (i : Bit) :
    action (firstBase a) v i =
      if i = 1 then Multiplicative.ofAdd (a.val *ᵥ (v i).toAdd) else v i := by
  rw [action_apply]
  by_cases hi : i = 1 <;> simp [firstBase, hi]

theorem coordinates_factorProduct
    (a : (⁅D.fullModule,L⁆ : Subgroup G))
    (b : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)) (i : Bit) :
    fullCoordinates s hz (factorProduct s hz (a,b)) i =
      if i = 1 then s.natural.coordinates a else partnerCoordinates s hz b := by
  convert fullCoordinates_mul s hz a b i using 2
  exact Subtype.ext (factorProduct_apply s hz a b)

theorem component_equivariant (l : L) (v : D.fullModule) :
    fullCoordinates s hz (joinAction D (componentInclusion l) v) =
      action (firstBase (componentHom s l)) (fullCoordinates s hz v) := by
  obtain ⟨⟨a,b⟩,rfl⟩ := (factorProduct s hz).surjective v
  let a' : (⁅D.fullModule,L⁆ : Subgroup G) := ⟨(l : G) * a * (l : G)⁻¹,
    (mem_normalizer_iff.mp (s.natural.normalized l.property) a).mp a.property⟩
  have hb : (l : G) * b * (l : G)⁻¹ = b := by
    rw [s.crossed b.property l l.property, mul_inv_cancel_right]
  have he : joinAction D (componentInclusion l) (factorProduct s hz (a,b)) =
      factorProduct s hz (a',b) := by
    apply Subtype.ext
    rw [joinAction_apply, factorProduct_apply, factorProduct_apply]
    change (l : G) * ((a : G) * b) * (l : G)⁻¹ =
      ((l : G) * a * (l : G)⁻¹) * b
    calc
      _ = ((l : G) * a * (l : G)⁻¹) * ((l : G) * b * (l : G)⁻¹) := by group
      _ = _ := by rw [hb]
  have hc (x : (⁅D.fullModule,L⁆ : Subgroup G))
      (y : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom)) (i : Bit) :
      fullCoordinates s hz (factorProduct s hz (x,y)) i =
        if i = 1 then s.natural.coordinates x else partnerCoordinates s hz y := by
    convert fullCoordinates_mul s hz x y i using 2
    exact Subtype.ext (factorProduct_apply s hz x y)
  rw [he]
  funext i
  rw [firstBase_action, hc, hc]
  by_cases hi : i = 1
  · simp only [hi]
    exact congrArg Multiplicative.ofAdd (s.natural.equivariant l a)
  · simp only [hi, if_false]

/-- Faithfulness forces every lift to have the prescribed first-component marking. -/
theorem LiftData.component (f : LiftData s hz) (l : L) :
    f.hom (componentInclusion l) = firstBase (componentHom s l) := by
  apply action_injective
  apply MulEquiv.ext
  intro w
  obtain ⟨v,rfl⟩ := (fullCoordinates s hz).surjective w
  exact (f.equivariant _ v).symm.trans (component_equivariant s hz l v)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Overgroups.Closure.Parabolic.Natural.OriginalAction
