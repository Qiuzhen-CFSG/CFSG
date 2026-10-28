module

public import Theory.GroupTheory.QuotientDisplacementCardinality

namespace Subgroup

universe u

/-- Restrict quotient displacement to an ambient subgroup in which `D` is normal,
then transport the quotient cardinalities back to the original group. -/
public theorem quotient_card_le_of_conjugate_intersection_subgroupOf
    {G : Type u} [Group G] [Finite G]
    (H D X B Y P Q R : Subgroup G) [(D.subgroupOf H).Normal]
    (hDH : D ≤ H) (hXH : X ≤ H) (hBH : B ≤ H)
    (_hYH : Y ≤ H) (_hPH : P ≤ H) (_hQH : Q ≤ H) (hRH : R ≤ H)
    (hDX : D ≤ X) (hDB : D ≤ B) (hXP : X ≤ P) (hXQ : X ≤ Q)
    (hBY : B ≤ Y) (hDY : D ≤ Y) (hbound : ⁅Q, R⁆ ≤ B)
    (actor : G) (hactor : actor ∈ R)
    (hintersection : P ⊓ P.map (MulAut.conj actor).toMonoidHom ≤ D) :
    Nat.card (X ⧸ D.subgroupOf X) ≤
      Nat.card ((B ⊔ D : Subgroup G) ⧸ D.subgroupOf (B ⊔ D)) := by
  let localActor : H := ⟨actor, hRH hactor⟩
  have hlocalBound : ⁅Q.subgroupOf H, R.subgroupOf H⁆ ≤ B.subgroupOf H := by
    apply commutator_le.mpr
    intro first hfirst second hsecond
    exact hbound (commutator_mem_commutator hfirst hsecond)
  have hlocalIntersection :
      P.subgroupOf H ⊓ (P.subgroupOf H).map (MulAut.conj localActor).toMonoidHom ≤
        D.subgroupOf H := by
    intro element helement
    obtain ⟨preimage, hpreimage, heq⟩ := mem_map.mp helement.2
    apply hintersection
    exact ⟨helement.1, mem_map.mpr
      ⟨(preimage : G), hpreimage, congrArg Subtype.val heq⟩⟩
  have hlocal := quotient_card_le_of_conjugate_intersection
    (D.subgroupOf H) (X.subgroupOf H) (B.subgroupOf H) (Y.subgroupOf H)
    (P.subgroupOf H) (Q.subgroupOf H) (R.subgroupOf H)
    (fun _ hmem => hDX hmem) (fun _ hmem => hDB hmem)
    (fun _ hmem => hXP hmem) (fun _ hmem => hXQ hmem)
    (fun _ hmem => hBY hmem) (fun _ hmem => hDY hmem)
    hlocalBound localActor hactor hlocalIntersection
  change (D.subgroupOf H).relIndex (X.subgroupOf H) ≤
    (D.subgroupOf H).relIndex (B.subgroupOf H ⊔ D.subgroupOf H) at hlocal
  rw [← subgroupOf_sup hBH hDH, relIndex_subgroupOf hXH,
    relIndex_subgroupOf (sup_le hBH hDH)] at hlocal
  exact hlocal

end Subgroup
