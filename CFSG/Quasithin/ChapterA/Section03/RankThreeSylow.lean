module

public import CFSG.Quasithin.ChapterA.Section03.RankThreeInvolutions
public import Theory.GroupTheory.SingleInvolutionClassSylow
public import ABG.ChapterII.Section2.FullSylowShapes
public import ABG.ChapterII.Section1.SylowShapeRankCenter

/-!
# Sylow two-subgroups of SL₃(p) and SU₃(p)

For every odd prime p and every Sylow two-subgroup T of the actual SL₃(p)
or SU₃(p), T has a genuine semidihedral or wreathed presentation. Its
center is cyclic and its elementary abelian two-rank is exactly two: an
actual elementary four-subgroup exists and every elementary abelian
two-subgroup has order at most four. This includes p = 3.

The one-class involution theorem makes every involution centralizer have
odd index. The full centralizer isomorphisms with GL₂(p) and GU₂(p) therefore
transport their Sylow presentations to T. The unitary model is the identity
Hermitian form over GF(p²), with conjugation x ↦ x^p, as in
`RankThreeInvolutions`. The rank and center assertions then follow from the
explicit two-group presentations.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.3.21(b) and the following paragraph, printed p. 55 (PDF p. 66).
-/

public section
namespace CFSG.Quasithin.ChapterA.Section03

/-- Every involution centralizer in SL₃(p) has odd index. -/
theorem sl3_involutionCentralizer_odd_index (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (z : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) (hz : orderOf z = 2) :
    Odd (Subgroup.centralizer ({z} : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)))).index :=
  Subgroup.odd_index_centralizer_of_one_involution_class z hz
    (fun w hw => sl3_involutions_isConj p hp w z hw hz)

/-- Every involution centralizer in the actual SU₃(p) has odd index. -/
theorem su3_involutionCentralizer_odd_index (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (z : RankThreeSU p) (hz : orderOf z = 2) :
    Odd (Subgroup.centralizer ({z} : Set (RankThreeSU p))).index :=
  Subgroup.odd_index_centralizer_of_one_involution_class z hz
    (fun w hw => su3_involutions_isConj p hp w z hw hz)

/-- Each SL₃(p) Sylow two-subgroup is genuinely isomorphic to any GL₂(p) Sylow two-subgroup. -/
theorem sl3_sylow_equiv_GL2 (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (T : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)))
    (P : Sylow 2 (GL (Fin 2) (ZMod p))) : Nonempty (T ≃* P) := by
  obtain ⟨z, hz, _⟩ := sl3_involution_structure p hp
  exact Subgroup.sylow_equiv_of_odd_index _ (sl3_involutionCentralizer_odd_index p hp z hz)
    (sl3_involutionCentralizerEquiv p hp z hz) T P

/-- Each SU₃(p) Sylow two-subgroup is genuinely isomorphic to any GU₂(p) Sylow two-subgroup. -/
theorem su3_sylow_equiv_GU2 (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (T : Sylow 2 (RankThreeSU p)) (P : Sylow 2 (ABG.GU2 p 1 (by decide))) :
    Nonempty (T ≃* P) := by
  obtain ⟨z, hz, _⟩ := su3_involution_structure p hp
  exact Subgroup.sylow_equiv_of_odd_index _ (su3_involutionCentralizer_odd_index p hp z hz)
    (su3_involutionCentralizerEquiv p hp z hz) T P

/-- A.3.21(b), linear case: the actual semidihedral or wreathed presentation. -/
theorem sl3_sylow_shape (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (T : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) (ZMod p))) :
    Stellmacher.IsSemidihedralGroup T ∨ ABG.IsWreathedGroup T := by
  let P : Sylow 2 (GL (Fin 2) (ZMod p)) := Classical.choice inferInstance
  obtain ⟨e⟩ := sl3_sylow_equiv_GL2 p hp T P
  have hfield : Odd (Nat.card (ZMod p)) := by simpa only [Nat.card_eq_fintype_card, ZMod.card] using hp
  rcases ABG.full_GL2_sylow_shape (ZMod p) hfield P with h | ⟨n, h⟩
  · exact Or.inl (ABG.semidihedral_equiv e.symm h)
  · exact Or.inr ⟨n, ABG.wreathed_equiv e.symm h⟩

/-- A.3.21(b), unitary case over GF(p²): the actual semidihedral or wreathed presentation. -/
theorem su3_sylow_shape (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (T : Sylow 2 (RankThreeSU p)) :
    Stellmacher.IsSemidihedralGroup T ∨ ABG.IsWreathedGroup T := by
  let P : Sylow 2 (ABG.GU2 p 1 (by decide)) := Classical.choice inferInstance
  obtain ⟨e⟩ := su3_sylow_equiv_GU2 p hp T P
  rcases ABG.full_GU2_sylow_shape p 1 hp (by decide) P with h | ⟨n, h⟩
  · exact Or.inl (ABG.semidihedral_equiv e.symm h)
  · exact Or.inr ⟨n, ABG.wreathed_equiv e.symm h⟩

/-- A.3.21(b) for SL₃(p), including exact elementary two-rank and the cyclic center used next. -/
theorem sl3_sylow_structure (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (T : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) (ZMod p))) :
    (Stellmacher.IsSemidihedralGroup T ∨ ABG.IsWreathedGroup T) ∧
    (∃ E : Subgroup T, IsElementaryAbelian 2 E ∧ Nat.card E = 4) ∧
    (∀ E : Subgroup T, IsElementaryAbelian 2 E → Nat.card E ≤ 4) ∧
    IsCyclic (Subgroup.center T) := by
  have h := sl3_sylow_shape p hp T
  exact ⟨h, ABG.rank_two_and_cyclic_center_of_sylow_shape h⟩

/-- A.3.21(b) for SU₃(p), including exact elementary two-rank and the cyclic center used next. -/
theorem su3_sylow_structure (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (T : Sylow 2 (RankThreeSU p)) :
    (Stellmacher.IsSemidihedralGroup T ∨ ABG.IsWreathedGroup T) ∧
    (∃ E : Subgroup T, IsElementaryAbelian 2 E ∧ Nat.card E = 4) ∧
    (∀ E : Subgroup T, IsElementaryAbelian 2 E → Nat.card E ≤ 4) ∧
    IsCyclic (Subgroup.center T) := by
  have h := su3_sylow_shape p hp T
  exact ⟨h, ABG.rank_two_and_cyclic_center_of_sylow_shape h⟩

/-- The center of every Sylow two-subgroup of SL₃(p) is cyclic. -/
theorem sl3_sylow_center_cyclic (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (T : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) (ZMod p))) :
    IsCyclic (Subgroup.center T) := (sl3_sylow_structure p hp T).2.2.2

/-- The center of every Sylow two-subgroup of SU₃(p) is cyclic. -/
theorem su3_sylow_center_cyclic (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (T : Sylow 2 (RankThreeSU p)) :
    IsCyclic (Subgroup.center T) := (su3_sylow_structure p hp T).2.2.2

end CFSG.Quasithin.ChapterA.Section03
end
