module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Unitary.Outer
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Unitary.Semilinearity
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Unitary.LinearInvolutions

/-!
# The ambient normalizer inputs for the natural SU₃ branch

The actual coefficient homomorphism and linear-involution theorem construct
the semilinear control used by the ratio calculation. The same coefficient
acts on the marked SU₃ matrices and their column module. For an involution
outside the layer it is exactly Hermitian conjugation, and its fixed
codimension is 3s. All formulas retain the full special unitary group.

Source: Aschbacher–Smith, K.3.3, printed p.456 (1 March 2004 manuscript).
-/

public section
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryModel
open BenderSuzuki.MatrixGroups Matrix Representation.BinaryOffender
variable {G V F : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
  {J : HermitianForm 3 F} {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  (M : UnitaryModel J ρ L)

/-- Both normalizer premises of the ratio calculation follow from the genuine
natural identification. The compatible group formula uses the same coefficient. -/
theorem exists_semilinearControl (h : SourceHypotheses ρ L)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x : F, J.conj x = x ^ (2 ^ s)) :
    let : L.Normal := h.layer_normal
    ∃ C : UnitarySemilinearControl M, ∀ g : G,
      ∃ u : J.unitarySubgroup, ∀ l : L,
        (M.groupEquiv (MulAut.conjNormal g l)).val =
          u.val * GeneralLinearGroup.map (C.coefficient g).toRingHom
            (M.groupEquiv l).val * u.val⁻¹ := by
  let : L.Normal := h.layer_normal
  obtain ⟨π, hπ, hgroup⟩ := M.exists_coefficientAction h hJ hs hcard hconj
  refine ⟨{
    coefficient := π
    semilinear := hπ
    linear_involution := ?_ }, hgroup⟩
  intro t ht htπ
  apply M.linear_involution_mem h hJ hs hcard hconj ht
  intro c v
  simpa only [htπ, RingAut.one_apply] using hπ t c v

/-- On both the original module and the full marked layer, an outer involution
has the nontrivial quadratic-field coefficient. It moves exactly 3s dimensions. -/
theorem outer_involution_action (h : SourceHypotheses ρ L)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x : F, J.conj x = x ^ (2 ^ s))
    {t : G} (ht : t ^ 2 = 1) (htL : t ∉ L) :
    let : L.Normal := h.layer_normal
    (∀ (c : F) (v : Fin 3 → F),
      M.coordinateAction t (c • v) = c ^ (2 ^ s) • M.coordinateAction t v) ∧
    (∃ u : J.unitarySubgroup, ∀ l : L,
      (M.groupEquiv (MulAut.conjNormal t l)).val =
        u.val * GeneralLinearGroup.map J.conj.toRingHom (M.groupEquiv l).val * u.val⁻¹) ∧
    fixedCodim ρ (Subgroup.zpowers t) = 3 * s := by
  let : L.Normal := h.layer_normal
  obtain ⟨C, hgroup⟩ := M.exists_semilinearControl h hJ hs hcard hconj
  refine ⟨C.outer_semilinear hs hcard hconj ht htL, ?_,
    C.outer_fixedCodim hcard ht htL⟩
  simpa only [C.outer_coefficient_eq_conj hs hcard hconj ht htL] using hgroup t

end CFSG.Quasithin.ChapterK.RankOne.UnitaryModel
