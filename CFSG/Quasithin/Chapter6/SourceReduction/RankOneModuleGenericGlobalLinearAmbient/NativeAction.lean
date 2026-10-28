module
public import CFSG.Quasithin.Chapter5.Section03LinearSource.MarkedAction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearCompletion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalNormalizerAction

/-!
# The actual common normalizer acting on PSL₃

The source local conditions and the trivial ambient centralizer of the factor
join make conjugation on the native amalgam faithful. The all-field native
lift extends that same action to PSL₃(F), preserving both endpoint maps and
the entire Borel. The original comparison supplies the unchanged exponent.
Both orientations and field four are included; no recognition of the unknown
factor join or ambient-generation premise enters this construction.

Source: Aschbacher–Smith 5.3.1–2, printed pp.658–659 of `refs/quasithin.pdf`.
The full endpoint realization is assembled in FullNormalizer.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Chapter5.Section03LinearSource Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include d h hH hp hm hF he hmax


/-- The original maximal row supplies all intrinsic local conditions, including q=4. -/
theorem Preparation.linear_normalizer_local_conditions :
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) := by
  have hc : ConcreteAmalgamComparison
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) := .linear F m hm hF he
  exact d.normalizer_local_conditions h hH hmax rfl
    (d.common_sylow_of_comparison h hH.1.1.2 hp hc)
    (d.parabolic_sylow_core_eq_of_comparison h hH.1.1.2 hp hc)

theorem Preparation.linear_common_normalizer_eq :
    normalizer (sourceS L H : Set G) = normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
  have hs : sourceS L H = (T : Subgroup G) ⊓ L :=
    (inf_eq_left.mpr (d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he 0)).symm.trans d.left_intersection
  rw [hs]
  exact (d.linear_normalizer_local_conditions h hH hp F hm hF he hmax).normalizer_eq_middle

/-- Faithfulness on the two actual parabolics, before any ambient recognition. -/
theorem Preparation.linear_source_middle_action_injective
    (hS : normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ≤ normalizer (sourceS L H : Set G)) :
    Function.Injective (LinearCompletion.sourceMiddleAction L (residual H) (sourceS L H) hS) := by
  let ρ := LinearCompletion.sourceMiddleAction L (residual H) (sourceS L H) hS
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  apply ρ.ker_eq_bot_iff.mp
  apply bot_unique
  intro g hg
  have heq : ρ g = 1 := hg
  have hcP : g.val ∈ centralizer (P 0 : Set G) ∧ g.val ∈ centralizer (P 1 : Set G) := by
    constructor
    · intro x hx
      have hh := congrArg (fun a => ((a.left ⟨x,hx⟩ : P 0) : G)) heq
      change g.val*x*g.val⁻¹=x at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro x hx
      have hh := congrArg (fun a => ((a.right ⟨x,hx⟩ : P 1) : G)) heq
      change g.val*x*g.val⁻¹=x at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hc : L ⊔ residual H ≤ centralizer ({g.val} : Set G) := by
    refine sup_le ?_ ?_
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (hcP.1 x ((le_sup_left.trans le_sup_left : L ≤ P 0) hx))
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (hcP.2 x ((le_sup_left.trans le_sup_left : residual H ≤ P 1) hx))
  have hgC : g.val ∈ centralizer ((L ⊔ residual H : Subgroup G) : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hc hx)
  rw [normalizer_pair_centralizer_eq_bot (d.linear_normalizer_local_conditions h hH hp F hm hF he hmax)] at hgC
  exact Subtype.ext (mem_bot.mp hgC)

/-- A faithful native action preserves both marked endpoints and the entire overlap. -/
theorem Preparation.linear_native_middle_action :
    m = n ∧
      (Nonempty (MarkedAction
        (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0)
        (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1)
        (normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
        (pointParabolic F) (lineParabolic F)) ∨
       Nonempty (MarkedAction
        (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0)
        (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1)
        (normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
        (lineParabolic F) (pointParabolic F))) := by
  have hmn := (d.linear_amalgam_blocks h hH.1.1.2 hp F hm hF he).1
  have hm' : 1 < m := hmn ▸ h.exponent
  have hS := (d.linear_common_normalizer_eq h hH hp F hm hF he hmax).ge
  have hinj := d.linear_source_middle_action_injective h hH hp F hm hF he hmax hS
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  have hf := d.hypothesisF11 h hH.1.1.2
  have hPM : P 0 ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show L ≤ P 0 from le_sup_left.trans le_sup_left)).mp
      (hf.local_normal_in_parabolic 0)
  have hQM : P 1 ≤ normalizer (residual H : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show residual H ≤ P 1 from le_sup_left.trans le_sup_left)).mp
      (hf.local_normal_in_parabolic 1)
  have hCD := le_inf (inf_le_left.trans hPM) (inf_le_right.trans hQM)
  refine ⟨hmn,?_⟩
  rcases he with he | he <;> obtain ⟨e⟩ := he
  · let ρ := LinearCompletion.nativeMiddleAction L (residual H) (sourceS L H) hS e hF hm'
    have hρ : Function.Injective ρ := by
      apply ρ.ker_eq_bot_iff.mp
      rw [LinearCompletion.nativeMiddleAction_ker]
      exact (MonoidHom.ker_eq_bot_iff _).mpr hinj
    refine Or.inl ⟨{
      left := e.left
      right := e.right
      middle := e.middle.trans (MulEquiv.subgroupCongr (ChapterF.GreenBook.LieModels.LinearThree.parabolic_intersection F).symm)
      left_middle := fun b => congrArg Subtype.val (e.left_commutes b)
      right_middle := fun b => congrArg Subtype.val (e.right_commutes b)
      middle_le := hCD
      action := ρ
      faithful := hρ
      left_action := ?_
      right_action := ?_ }⟩
    · intro g x
      let y := (LinearCompletion.sourceMiddleAction L (residual H) (sourceS L H) hS g).left x
      refine ⟨y.property,?_⟩
      exact (LinearCompletion.nativeMiddleAction_equations L (residual H) (sourceS L H) hS e hF hm' g).1 x |>.symm
    · intro g x
      let y := (LinearCompletion.sourceMiddleAction L (residual H) (sourceS L H) hS g).right x
      refine ⟨y.property,?_⟩
      exact (LinearCompletion.nativeMiddleAction_equations L (residual H) (sourceS L H) hS e hF hm' g).2.2 x |>.symm
  · let ρ := LinearCompletion.nativeMiddleReverseAction L (residual H) (sourceS L H) hS e hF hm'
    have hρ : Function.Injective ρ := by
      apply ρ.ker_eq_bot_iff.mp
      rw [LinearCompletion.nativeMiddleReverseAction_ker]
      exact (MonoidHom.ker_eq_bot_iff _).mpr hinj
    refine Or.inr ⟨{
      left := e.left
      right := e.right
      middle := e.middle.trans (MulEquiv.subgroupCongr ((inf_comm _ _).trans (ChapterF.GreenBook.LieModels.LinearThree.parabolic_intersection F)).symm)
      left_middle := fun b => congrArg Subtype.val (e.left_commutes b)
      right_middle := fun b => congrArg Subtype.val (e.right_commutes b)
      middle_le := hCD
      action := ρ
      faithful := hρ
      left_action := ?_
      right_action := ?_ }⟩
    · intro g x
      let y := (LinearCompletion.sourceMiddleAction L (residual H) (sourceS L H) hS g).left x
      refine ⟨y.property,?_⟩
      exact (LinearCompletion.nativeMiddleReverseAction_equations L (residual H) (sourceS L H) hS e hF hm' g).1 x |>.symm
    · intro g x
      let y := (LinearCompletion.sourceMiddleAction L (residual H) (sourceS L H) hS g).right x
      refine ⟨y.property,?_⟩
      exact (LinearCompletion.nativeMiddleReverseAction_equations L (residual H) (sourceS L H) hS e hF hm' g).2.2 x |>.symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
