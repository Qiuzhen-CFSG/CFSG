module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Basic
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Product

/-!
# The original Hall action on the first component

Odd order prevents exchange of the two components, as proved in Basic.
This permits restriction of normalizer conjugation to L/O₂(L). Every
product marking that respects the original inclusion intertwines this
restricted action with the original action on L₀/O₂(L₀).
Source: Aschbacher--Smith, the automorphism step in 10.2.3, p.745.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} (c : Context D H B)

/-- Restriction of literal conjugation to the original component quotient. -/
def componentAction : B →* MulAut (L ⧸ pCore 2 L) :=
  (normalizerPCoreQuotientAction L).comp
    ((H.subtype.comp B.subtype).codRestrict (normalizer (L : Set G))
      (fun b => hall_normalizes_component D c
        (mem_map_of_mem H.subtype b.property)))

/-- Any compatible product marking intertwines the first component actions. -/
theorem componentAction_first
    {S : Type*} [Group S] (e : (L ⧸ pCore 2 L) ≃* S)
    (q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (S × S))
    (hq : ∀ l : L, q (QuotientGroup.mk' (pCore 2 (localOrbit T L))
      ⟨l,le_componentOrbit L T l.property⟩) =
        (e (QuotientGroup.mk' (pCore 2 L) l), 1))
    (b : B) (l : L) :
    q (action D B c.hall_le b
      (QuotientGroup.mk' (pCore 2 (localOrbit T L))
        ⟨l,le_componentOrbit L T l.property⟩)) =
      (e (componentAction D c b (QuotientGroup.mk' (pCore 2 L) l)), 1) := by
  change q (quotientAut (pCore 2 (localOrbit T L)) _ _) =
    (e (quotientAut (pCore 2 L) _ _), 1)
  rw [quotientAut_apply_mk, quotientAut_apply_mk]
  exact hq ((L.normalizerMonoidHom
    ⟨b.val.val, hall_normalizes_component D c
      (mem_map_of_mem H.subtype b.property)⟩) l)

/-- The actual binary component supplies the product marking and its literal
Hall-action compatibility together, without an independently assumed quotient. -/
theorem exists_marked_sl2_pair_action
    {F : Type*} [Field F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃*
        (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F),
      (∀ l : L, q (QuotientGroup.mk' (pCore 2 (localOrbit T L))
        ⟨l,le_componentOrbit L T l.property⟩) =
          (e (QuotientGroup.mk' (pCore 2 L) l), 1)) ∧
      ∀ (b : B) (l : L), q (action D B c.hall_le b
        (QuotientGroup.mk' (pCore 2 (localOrbit T L))
          ⟨l,le_componentOrbit L T l.property⟩)) =
        (e (componentAction D c b (QuotientGroup.mk' (pCore 2 L) l)), 1) := by
  obtain ⟨q,hq⟩ := marked_sl2_pair_quotient D e c.nonnormal
  exact ⟨q,hq,componentAction_first D c e q hq⟩

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
