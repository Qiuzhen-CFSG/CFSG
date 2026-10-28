module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRecognitionSymplectic
public import Theory.SpecificGroups.SL2.FieldCardinality

/-!
# Recovering the original field in the ordinary symplectic row

The full-Sylow placement theorem identifies the original L with the plane
local subgroup of any genuine nonbinary symplectic quotient model. Its
literal two-core quotient is SL₂ over the containing field. Comparing this
quotient with the given PSL₂(2ⁿ), using characteristic two and the strictly
increasing SL₂ order formula, recovers the original field cardinality.

The final theorem applies this comparison to the actual projective
symplectic row and constructs the whole marking: component, original L,
Sylow intersection and full module. No agreement of field parameters is
assumed. Selection of a symplectic row from the original C.2.8 hypotheses
remains with qt-d-1222-rankone-ordinary-symplectic-marking; this conditional
application does not assert that remaining exhaustion.

Source: Aschbacher--Smith C.3.1(1), printed pp.149--150, and the opening
rank-one comparison in 4.3.6, printed p.614.
-/

public section
open Subgroup Theory.GroupTheory ClassicalGroup
open Theory.SpecificGroups.SymplecticFour
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The unchanged original local quotient determines the containing
symplectic field, without any prior relation between the two exponents. -/
theorem ordinary_symplectic_field_card (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {n : ℕ} (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (e : (c.K ⧸ center c.K) ≃* Sp F) : Nat.card F = 2 ^ n := by
  obtain ⟨b,hb⟩ := c.ordinary_symplectic_plane_model D ho hF hm e
  let a : L ≃* planeLocal (F := F) := c.ordinaryLocalEquiv.symm.trans
    ((b.subgroupMap c.ordinaryLocal).trans (MulEquiv.subgroupCongr hb))
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let q : (L ⧸ pCore 2 L) ≃* SL(2,F) := aq.trans (planeLocalCoreQuotientEquiv hF hm)
  obtain ⟨E,_,_,hE,⟨r⟩⟩ := hpsl
  let : CharP E 2 := EvenProjective.charTwo_of_card hE
  exact (Matrix.SL2.field_card_eq_of_equiv
    (q.symm.trans (r.trans (Theory.PSL2.sl2QuotientEquiv E).symm))).trans hE

/-- Literal application to an actual nonbinary symplectic quotient row.
The source field, local and Sylow markings and full-module equality are
all derived; only selection of the containing symplectic row remains. -/
theorem ordinarySymplecticMarking_of_symplectic_row (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {m : ℕ} (hm : 1 < m) (hrow : IsPSp (c.K ⧸ center c.K) 2 (2 ^ m)) :
    Nonempty (OrdinarySymplecticMarking c n) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hrow
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  let a : (c.K ⧸ center c.K) ≃* Sp F := e.trans (EvenProjective.equiv (F := F)).symm
  exact c.ordinarySymplecticMarking_of_quotient_model D ho
    (c.ordinary_symplectic_field_card D ho hpsl hF hm a) hn a

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceConfiguration
