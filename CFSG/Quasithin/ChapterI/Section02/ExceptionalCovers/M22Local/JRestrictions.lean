module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.JRestrictions.Geometry
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.JRestrictions.Transport
public import Theory.Mathieu.M22.CentralQuarticFrattini

/-!
# Native incidence and the central squares of arbitrary source J-subgroups

Every S₅/E₁₆ subgroup is recognized as an actual pair stabilizer. The
geometry retains its distinct kernel and an incident hexad kernel. For a
cyclic center of order four, factoring its square subgroup proves that the
Frattini subgroup of the actual lifted two-core is precisely that embedded
order-two subgroup.

Source: Aschbacher–Smith I.2.2(6a), printed pp.410 and 412. The central
residual placement and central-product recognition are separate obligations;
neither follows from the incidence or Frattini assertion alone.
-/

public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open scoped Pointwise
variable {K : Type*} [Group K] [Finite K]

/-- The quartic source core has the square subgroup of the actual center
as its Frattini subgroup, with both subgroup embeddings displayed. -/
theorem sourceJ_quartic_frattini [IsCyclic (center K)]
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4)
    (H : Subgroup M22) (hH : IsSourceJ H) :
    ((frattini (pCore 2 (preimage e H))).map (pCore 2 (preimage e H)).subtype).map
      (preimage e H).subtype = centerSquares K := by
  let J := preimage e H
  let Q := pCore 2 J
  have hZp : IsPGroup 2 (center K) := IsPGroup.of_card (n := 2) (by simpa using hZ)
  have hZQ : center K ≤ Q.map J.subtype := by
    rw [← preimage_twoCore e hZp H]
    exact center_le_preimage e _
  let := (sourceJ_twoCore H hH).1
  rw [map_map]
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    rw [(pCore_isPGroup (p := 2) (G := J)).frattini_eq_closure_squares]
    apply (closure_le _).mpr
    rintro _ ⟨x, rfl⟩
    apply square_mem_centerSquares e hZ
    have hx : localProjection e H x.val ∈ pCore 2 H := by
      exact (localProjection_comap_twoCore e hZp H).ge x.property
    exact congrArg Subtype.val
      (elemPow_eq_one_of_isElementaryAbelian (localProjection e H x.val) hx)
  · intro x hx
    obtain ⟨z, rfl⟩ := (mem_centerSquares_iff K x).mp hx
    obtain ⟨zJ, hzQ, hz⟩ := hZQ z.property
    let w : Q := ⟨zJ, hzQ⟩
    let : Fact (IsPGroup 2 Q) := ⟨pCore_isPGroup⟩
    refine ⟨w ^ 2, pth_power_mem_frattini_of_isPGroup (p := 2) w, ?_⟩
    exact congrArg (fun a : K => a ^ 2) hz

/-- The Frattini subgroup in the preceding equality has order exactly two. -/
theorem sourceJ_quartic_frattini_card [IsCyclic (center K)]
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4)
    (H : Subgroup M22) (hH : IsSourceJ H) :
    Nat.card (frattini (pCore 2 (preimage e H))) = 2 := by
  have hc := congrArg (fun A : Subgroup K => Nat.card A)
    (sourceJ_quartic_frattini e hZ H hH)
  rw [card_map_of_injective (preimage e H).subtype_injective,
    card_map_of_injective (pCore 2 (preimage e H)).subtype_injective,
    centerSquares_card hZ] at hc
  exact hc

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
