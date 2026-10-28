module

public import Stellmacher.SectionNine.NineSevenGoldschmidtAlgebra
public import Stellmacher.SectionNine.NineSevenShiftedIntersections

namespace Stellmacher.SectionNine

public theorem goldschmidt_plane_generator
    {G : Type*} [Group G] [Finite G]
    (large plane : Subgroup G) (hlarge : Nat.card large = 8)
    (hplane : Nat.card plane = 4) (hle : plane ≤ large)
    (generator : G) (hgenerator : generator ∈ large) (houtside : generator ∉ plane) :
    large = plane ⊔ Subgroup.zpowers generator := by
  let joined := plane ⊔ Subgroup.zpowers generator
  have hjoined : joined ≤ large := sup_le hle (Subgroup.zpowers_le.mpr hgenerator)
  have hplaneJoined : plane ≤ joined := le_sup_left
  have hne : plane ≠ joined := by
    intro heq
    exact houtside (heq ▸ (show generator ∈ joined from
      (show Subgroup.zpowers generator ≤ joined from le_sup_right)
        (Subgroup.mem_zpowers generator)))
  have hcardgt : 4 < Nat.card joined := by
    have hcardle := Subgroup.card_le_of_le hplaneJoined
    have hcardne : Nat.card plane ≠ Nat.card joined := fun heq =>
      hne (Subgroup.eq_of_le_of_card_ge hplaneJoined heq.symm.le)
    omega
  have hcardle : Nat.card joined ≤ 8 := by
    simpa only [hlarge] using Subgroup.card_le_of_le hjoined
  obtain ⟨factor, hfactor⟩ := Subgroup.card_dvd_of_le hjoined
  rw [hlarge] at hfactor
  have hfactorOne : factor = 1 := by nlinarith
  apply (Subgroup.eq_of_le_of_card_ge hjoined ?_).symm
  rw [hlarge, hfactor, hfactorOne, mul_one]

end Stellmacher.SectionNine

