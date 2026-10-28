module

public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks
public import CFSG.Quasithin.ChapterI.Section04To05.SmallSylow

/-!
# The complete small-Sylow source input in the small-block recognition argument

Both clauses of I.4.3 discharge the entire earlier-source record used in
the S₄ paragraph of 2.4.26. The application preserves
the original selected Sylow, maximal two-local subgroup and nonempty delta
family, so the existing exclusions apply to the same actual model maps.

Source: Aschbacher–Smith I.4.3, pp.416–417, and 2.4.26, printed p.543.
-/

public section
namespace CFSG.Quasithin.Chapter2.SmallBlocks
variable {G : Type*} [Group G] [Finite G]

/-- The earlier-source record with its full dihedral clause discharged.
Only the exact semidihedral clause of I.4.3 remains explicit. -/
theorem earlierSmallSylowSource_of_semidihedral
    (hs : (∀ N : Subgroup G, N.index ≠ 2) → IsEvenCharacteristic G →
      ∀ T : Sylow 2 G, Stellmacher.IsSemidihedralGroup T →
        ClassicalGroup.IsPSL G 3 3 ∨ Nonempty (G ≃* Sporadic.Mathieu.M11)) :
    EarlierSmallSylowSource G :=
  ⟨ChapterI.lemma_I_4_3_1, hs⟩

/-- The original small-block recognition deduction now needs only the
semidihedral half of I.4.3 from the independent local-recognition argument. -/
theorem source_small_sylow_recognition_of_semidihedral
    {K : GroupClass} (hG : IsSimpleQTKE K G)
    (hs : (∀ N : Subgroup G, N.index ≠ 2) → IsEvenCharacteristic G →
      ∀ T : Sylow 2 G, Stellmacher.IsSemidihedralGroup T →
        ClassicalGroup.IsPSL G 3 3 ∨ Nonempty (G ≃* Sporadic.Mathieu.M11))
    (T : Sylow 2 G) (M : Subgroup G) (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hSylow : Stellmacher.IsDihedralGroup T ∨ Stellmacher.IsSemidihedralGroup T) :
    IsTheorem241Model G :=
  source_small_sylow_recognition hG (earlierSmallSylowSource_of_semidihedral hs)
    T M hM hu hdelta hSylow

/-- Both original I.4.3 clauses, with every earlier-source premise discharged. -/
theorem earlierSmallSylowSource : EarlierSmallSylowSource G :=
  ⟨ChapterI.lemma_I_4_3_1, ChapterI.lemma_I_4_3_2⟩

/-- The actual small-block consumer with I.4.3 fully supplied. -/
theorem source_small_sylow_recognition_complete
    {K : GroupClass} (hG : IsSimpleQTKE K G)
    (T : Sylow 2 G) (M : Subgroup G) (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hSylow : Stellmacher.IsDihedralGroup T ∨ Stellmacher.IsSemidihedralGroup T) :
    IsTheorem241Model G :=
  source_small_sylow_recognition hG earlierSmallSylowSource T M hM hu hdelta hSylow

end CFSG.Quasithin.Chapter2.SmallBlocks
