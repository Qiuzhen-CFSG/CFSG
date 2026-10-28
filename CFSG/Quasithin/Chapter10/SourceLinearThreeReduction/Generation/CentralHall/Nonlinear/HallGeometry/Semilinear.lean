module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.InvariantMarking
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.ComponentAction
public import Theory.SpecificGroups.SL2.SylowTorusAutomorphisms
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.SmallSylow

/-!
# Diagonal and field factors of the original Hall action

The original Hall subgroup preserves the actual orbit Sylow and a common
marked full torus. In that same marking its action on the two-core quotient
has two diagonal inner factors and two field factors. Torus restriction
uniquely determines the field factors, so they form a homomorphism from the
original Hall carrier. Its image has odd order. The marking retains the
literal inclusion of L and the image of T intersect L₀ throughout.

Source: Aschbacher--Smith 10.2.3, printed p.745. This proves the simultaneous
automorphism decomposition; it does not yet eliminate the field factors.
Their elimination and the module-row calculations remain with the central
Hall source assembly, qt-d-10-nona5-central-hall-orders.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02 Matrix.SpecialLinearGroup BenderSuzuki.ZD.Linear
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
include D

/-- The literal quotient action preserves the same marked orbit Sylow. -/
theorem hall_action_preserves_marked_sylow {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (SL(2,F) × SL(2,F)))
    (hS : ((T : Subgroup G).subgroupOf (localOrbit T L)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))) =
        (upperUnipotent F).prod (upperUnipotent F))
    (b : B) :
    ((upperUnipotent F).prod (upperUnipotent F)).map
      (MulAut.congr q (action D B c.hall_le b)).toMonoidHom =
        (upperUnipotent F).prod (upperUnipotent F) := by
  let R := localOrbit T L
  let f := q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  let α := MulAut.congr q (action D B c.hall_le b)
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    rw [←hS] at hx ⊢
    obtain ⟨y,hy,rfl⟩ := hx
    let bM : D.maximalLocal := ⟨(b:G),c.hall_le b.property⟩
    let y' := R.normalizerMonoidHom bM y
    have hy' : y' ∈ (T : Subgroup G).subgroupOf R := by
      have hb := hall_normalizes_orbit_sylow D c e (mem_map_of_mem H.subtype b.property)
      change (b:G) ∈ normalizer (((T : Subgroup G) ⊓ R : Subgroup G) : Set G) at hb
      exact ((mem_normalizer_iff.mp hb y).mp ⟨hy,y.property⟩).1
    refine ⟨y',hy',?_⟩
    change q (QuotientGroup.mk' (pCore 2 R) y') =
      q (action D B c.hall_le b (q.symm (q (QuotientGroup.mk' (pCore 2 R) y))))
    rw [q.symm_apply_apply]
    change q (QuotientGroup.mk' (pCore 2 R) y') =
      q (quotientAut (pCore 2 R) _ _)
    rw [quotientAut_apply_mk]
    rfl
  · rw [card_map_of_injective α.injective]

/-- A common marking gives diagonal inner factors for every original Hall actor. -/
theorem exists_hall_diagonal_field_marking {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hF : 2 < Nat.card F) :
    ∃ (e' : (L ⧸ pCore 2 L) ≃* SL(2,F))
      (q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (SL(2,F) × SL(2,F))),
      (∀ l : L, q (QuotientGroup.mk' (pCore 2 (localOrbit T L))
        ⟨l,le_componentOrbit L T l.property⟩) =
          (e' (QuotientGroup.mk' (pCore 2 L) l),1)) ∧
      ((T : Subgroup G).subgroupOf (localOrbit T L)).map
        (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))) =
          (upperUnipotent F).prod (upperUnipotent F) ∧
      ∀ b : B, ∃ (d : Fˣ × Fˣ) (σ τ : F ≃+* F),
        MulAut.congr q (action D B c.hall_le b) =
          (MulAut.conj (diag2 (d.1:F) d.1.ne_zero) * sl2FieldAut σ).prodCongr
            (MulAut.conj (diag2 (d.2:F) d.2.ne_zero) * sl2FieldAut τ) := by
  obtain ⟨e',q,hcomp,hS,hD⟩ := exists_hall_stable_pair_torus D c e
  refine ⟨e',q,hcomp,hS,fun b => ?_⟩
  let α := MulAut.congr q (action D B c.hall_le b)
  let a := MulAut.congr e' (componentAction D c b)
  have ha : ∀ x, α (x,1) = (a x,1) := by
    intro x
    obtain ⟨l,rfl⟩ := (e'.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) x
    have hh := componentAction_first D c e' q hcomp b l
    change q (action D B c.hall_le b
      (q.symm (e' (QuotientGroup.mk' (pCore 2 L) l),1))) = _
    rw [←hcomp,q.symm_apply_apply]
    change q (action D B c.hall_le b _) =
      (e' (componentAction D c b (e'.symm (e' (QuotientGroup.mk' (pCore 2 L) l)))),1)
    rw [e'.symm_apply_apply]
    exact hh
  exact pair_sylow_torus_preserving_semilinear hF α a ha
    (hall_action_preserves_marked_sylow D c e' q hS b) (hD b)


/-- The actual component rules out the two-element coefficient field. -/
theorem source_sl2_field_card_gt_two
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) : 2 < Nat.card F := by
  let := D.quasisimple
  let : IsQuasisimple SL(2,F) := IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup (SL(2,F) ⧸ center SL(2,F)) := IsQuasisimple.simple
  let : IsSimpleGroup SL(2,F) :=
    ((QuotientGroup.quotientMulEquivOfEq
      (Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot (F := F))).trans
        QuotientGroup.quotientBot).symm.isSimpleGroup
  have h := Chapter1.Section02.IndexTwo.two_lt_card_sylow_of_simple_perfect
    (upperUnipotentSylow F 2)
  exact (card_upperUnipotent F) ▸ h

/-- The field factors form an actual odd-order image of the original Hall
carrier. One marking retains both the original component and Sylow. -/
theorem exists_hall_diagonal_field_action {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    ∃ (e' : (L ⧸ pCore 2 L) ≃* SL(2,F))
      (q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (SL(2,F) × SL(2,F)))
      (φ : B →* ((F ≃+* F) × (F ≃+* F))),
      (∀ l : L, q (QuotientGroup.mk' (pCore 2 (localOrbit T L))
        ⟨l,le_componentOrbit L T l.property⟩) =
          (e' (QuotientGroup.mk' (pCore 2 L) l),1)) ∧
      ((T : Subgroup G).subgroupOf (localOrbit T L)).map
        (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))) =
          (upperUnipotent F).prod (upperUnipotent F) ∧
      Odd (Nat.card φ.range) ∧
      (∀ (b : B) (z : Fˣ × Fˣ),
        q (action D B c.hall_le b (q.symm
          (diag2 (z.1:F) z.1.ne_zero,diag2 (z.2:F) z.2.ne_zero))) =
            (diag2 ((φ b).1 (z.1:F)) ((map_ne_zero (φ b).1).2 z.1.ne_zero),
             diag2 ((φ b).2 (z.2:F)) ((map_ne_zero (φ b).2).2 z.2.ne_zero))) ∧
      ∀ b : B, ∃ d : Fˣ × Fˣ,
        MulAut.congr q (action D B c.hall_le b) =
          (MulAut.conj (diag2 (d.1:F) d.1.ne_zero) * sl2FieldAut (φ b).1).prodCongr
            (MulAut.conj (diag2 (d.2:F) d.2.ne_zero) * sl2FieldAut (φ b).2) := by
  obtain ⟨e',q,hcomp,hS,hd⟩ := exists_hall_diagonal_field_marking D c e
    (source_sl2_field_card_gt_two D e)
  let ρ := (MulAut.congr q).toMonoidHom.comp (action D B c.hall_le)
  obtain ⟨φ,hφ,hdiag⟩ := exists_pair_diagonal_field_hom ρ hd
  exact ⟨e',q,φ,hcomp,hS,(hall_odd D c).of_dvd_nat (card_range_dvd φ),hφ,hdiag⟩

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
