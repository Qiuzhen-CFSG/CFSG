module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Basic
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Unitary

/-!
# Actual fixed groups of outer involutions in the simple models

The three independent automorphism theorems apply after transport through
the supplied group equivalence. Suzuki has no outer involutions. The linear
case has square field order and fixed group over the square-root field;
the unitary case fixes PSL₂ over the stored Hermitian fixed field.

These are the model alternatives of GLS, Volume 4, Chapter 4, Lemma 3.4(c)
used in Chapter 2, Proposition 16.5. Fixing a specified root subgroup,
and the action on a marked torus, require further geometry.
-/

namespace BenderSuzuki.ZD.RankOneModelGeometry
open _root_.BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G]

/-- Arbitrary outer involutions of the recognized simple model have the
actual fixed groups in the source, retaining both unitary field orders. -/
public theorem outer_involutory_fixed_groups {n : ℕ} (hn : 2 ≤ n)
    (hG : IsSimpleBenderGroupAtExponent n G) (a : MulAut G) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ g : G, a = MulAut.conj g) :
    (Nonempty (G ≃* PSL2BinaryMatrixGroup n) ∧
      ∃ m : ℕ, 0 < m ∧ n = 2 * m ∧
        Nonempty (a.fixedSubgroup ≃* PSL2BinaryMatrixGroup m)) ∨
    (∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
      J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
      Nat.card E = (2 ^ n) ^ 2 ∧ Nat.card {x : E // J.conj x = x} = 2 ^ n ∧
      Nonempty (G ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∧
      Nonempty (a.fixedSubgroup ≃* PSL2MatrixGroup (FixedBy.subfield E J.conj))) := by
  rcases hG with hlinear | hsuzuki | hunitary
  · obtain ⟨e⟩ := hlinear
    have ha' : (MulAut.congr e a) ^ 2 = 1 := by rw [← map_pow, ha, map_one]
    have ho' : ¬ ∃ g, MulAut.congr e a = MulAut.conj g := fun h =>
      houter ((MulAut.congr_inner_iff e a).mp h)
    obtain ⟨m, hm, hnm, ⟨f⟩⟩ := Linear.outer_fixed_model hn (MulAut.congr e a) ha' ho'
    exact Or.inl ⟨⟨e⟩, m, hm, hnm, ⟨(MulAut.fixedSubgroupCongr e a).trans f⟩⟩
  · obtain ⟨m, hnm, ⟨e⟩⟩ := hsuzuki
    have hm : 1 ≤ m := by omega
    have ha' : (MulAut.congr e a) ^ 2 = 1 := by rw [← map_pow, ha, map_one]
    obtain ⟨g, hg, _⟩ := suzuki_involutoryAut_inner_and_twoRank m hm (MulAut.congr e a) ha'
    exact False.elim (houter ((MulAut.congr_inner_iff e a).mp ⟨g, hg⟩))
  · obtain ⟨E, hfield, hfinite, J, hJ, hcard, hfixed, ⟨e⟩⟩ := hunitary
    let : Field E := hfield
    let : Finite E := hfinite
    have ha' : (MulAut.congr e a) ^ 2 = 1 := by rw [← map_pow, ha, map_one]
    have ho' : ¬ ∃ g, MulAut.congr e a = MulAut.conj g := fun h =>
      houter ((MulAut.congr_inner_iff e a).mp h)
    obtain ⟨f⟩ := UnitaryAutomorphisms.outer_fixedSubgroup_equiv
      J hn hJ hcard hfixed (MulAut.congr e a) ha' ho'
    exact Or.inr ⟨E, hfield, hfinite, J, hJ, hcard, hfixed, ⟨e⟩,
      ⟨(MulAut.fixedSubgroupCongr e a).trans f⟩⟩

end BenderSuzuki.ZD.RankOneModelGeometry
