module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.InductionContracts

/-!
# Commuting dihedral actors on a classified space

Every reflection is an involution and every rotation is a product of two
reflections. Thus the classified-involution-centralizer input kills an
entire commuting dihedral action, including its odd-order rotations.
When used on a subspace, the caller must establish invariance before
forming these restricted representations.

Source: the complementary-actor argument in Aschbacher--Smith G.9.2,
printed p.353.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep

universe v

/-- Pointwise fixation by commuting reflections extends to the whole
dihedral group. No assertion of invariance is implicit in this lemma. -/
theorem dihedral_fixes_classified
    (centralizer : ClassifiedInvolutionCentralizerTheorem.{0,v})
    {G : Type} [Group G] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) G W) (H : Subgroup G) (exceptional : Prop)
    (d : ClassifiedDecomposition σ H exceptional)
    (hf : Function.Injective (σ.comp H.subtype))
    {p : ℕ} (τ : Representation (ZMod 2) (DihedralGroup p) W)
    (hc : ∀ x (g : H), Commute (τ x) (σ g)) : ∀ x, τ x = 1 := by
  have href (k : ZMod p) : τ (DihedralGroup.sr k) = 1 := by
    apply centralizer G W σ H exceptional d hf _ _ (hc _)
    rw [← map_mul, DihedralGroup.sr_mul_self, map_one]
  intro x
  cases x with
  | sr k => exact href k
  | r k =>
    have he : DihedralGroup.r k = DihedralGroup.sr 0 * DihedralGroup.sr k := by simp
    rw [he, map_mul, href, href, one_mul]

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep
