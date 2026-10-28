module

public import Theory.AlgebraicGroup.Borel.Conjugation
public import Theory.AlgebraicGroup.Borel.Existence

/-!
This module contains the Borel-conjugacy proof of clause (b) after the
source theorem was moved out of its original file.  It is kept separate
because `Borel.Conjugation` imports the original `Tori.Maximal` module,
whereas the implementation defines the same interface separately.

The source-facing theorem `theorem_1_4_3_b` is intentionally retained with
its placeholder; this shifted theorem is the implementation that can be
checked once the Borel-conjugacy result is available.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem maximalTorus_borelContainment_shifted
    {G : Variety k} [AlgebraicGroup G] :
    ∀ T : ClosedSubgroup G, IsMaximalTorus T →
      ∃ B : ClosedSubgroup G,
        IsBorelSubgroup B ∧ IsTorusMaximalIn T B := by
  intro T hT
  have hTconnVar : Variety.IsConnected T.carrierVariety := hT.1.isConnected
  let : ConnectedSpace (Variety.Point T.carrierVariety) :=
    connectedSpace_iff_univ.mpr hTconnVar
  have hTconn : _root_.IsConnected (T : Set (Variety.Point G)) := by
    change _root_.IsConnected (T.toSubgroup : Set (Variety.Point G))
    rw [← T.range_inclusion]
    exact isConnected_range T.inclusion.toVariety.continuous
  have hTcomm' : IsMulCommutative (Variety.Point T.carrierVariety) :=
    hT.1.isMulCommutative
  rw [isMulCommutative_iff] at hTcomm'
  have hTcomm : ∀ a b : Variety.Point T.carrierVariety, a * b = b * a := hTcomm'
  have hTsolv : Group.IsSolvable (Variety.Point T.carrierVariety) :=
    Group.isSolvable_of_comm hTcomm
  obtain ⟨B, hB, hTB⟩ := exists_borelSubgroup_containing_connected_solvable
    T hTconn hTsolv
  refine ⟨B, hB, hT.1, hTB, ?_⟩
  intro S hS _hSB hTS
  exact hT.2 S hS hTS

/--
Shifted implementation of Theorem 1.4.3(b).  Its only non-local input is the
source Borel-pair theorem `theorem_1_6_4`; the original source declaration is
left untouched and marked as shifted in `Tori/Maximal.lean`.
-/
public theorem theorem_1_4_3_b_shifted
    {G : Variety k} [AlgebraicGroup G] {T₁ T₂ : ClosedSubgroup G}
    (hT₁ : IsMaximalTorus T₁) (hT₂ : IsMaximalTorus T₂) :
    ∃ g : Variety.Point G, T₂ = T₁.conjugate g := by
  obtain ⟨B₁, hB₁, hBT₁⟩ := maximalTorus_borelContainment_shifted T₁ hT₁
  obtain ⟨B₂, hB₂, hBT₂⟩ := maximalTorus_borelContainment_shifted T₂ hT₂
  obtain ⟨_hM₁, _hM₂, ⟨g, _hBg, hTg⟩⟩ :=
    theorem_1_6_4 hB₁ hB₂ hBT₁ hBT₂
  exact ⟨g, hTg⟩

end Theory.AlgebraicGroup
