module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.Sylow
public import Theory.GroupTheory.Amalgam.SplitExtension
public import Theory.SpecificGroups.ReeF4.SourceCompletion.ParabolicCenters

/-!
# Faithful native parabolic actions of the full original Ree normalizers

The full common normalizer is N_G(T). It normalizes the two original
Borels and their whole join. Each full factor normalizer is the product of
its factor and that common normalizer, so it normalizes the corresponding
source parabolic. Conversely the parabolic's characteristic solvable residual
is the original factor, giving equality of their full ambient normalizers.

Both native full parabolics are centerless. Characteristic two in the full
source normalizer puts every element centralizing its parabolic in its
two-core, hence in the parabolic; centerlessness then kills it. Conjugation
therefore gives faithful actions of the full normalizers on the source
parabolics. Transport through the actual compatible comparison gives native
parabolic actions. The whole normalizer intersection acts faithfully on the
native amalgam, with both squares and the literal middle action retained.

These actions provide the local input to source 5.3.2. An action on the
complete native Ree group still requires extending the compatible amalgam
action. No such extension, ambient order bound or recognition is asserted.
Source: Aschbacher–Smith 5.3.1–2 and F.4.3, printed pp.658–659,274
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem centralizer_eq_bot_of_core (P M : Subgroup G)
    (hn : normalizer (P : Set G) ≤ M)
    (hc : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hQP : (pCore 2 M).map M.subtype ≤ P) (hz : center P = ⊥) :
    centralizer (P : Set G) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hxM := hn (Subgroup.centralizer_le_normalizer _ hx)
  let y : M := ⟨x,hxM⟩
  have hyC : y ∈ centralizer (pCore 2 M : Set M) := by
    intro u hu
    exact Subtype.ext (hx u (hQP ⟨u,hu,rfl⟩))
  have hxP : x ∈ P := hQP ⟨y,hc hyC,rfl⟩
  have hxZ : (⟨x,hxP⟩ : P) ∈ center P :=
    mem_center_iff.mpr (fun z => Subtype.ext (hx z z.property))
  have hx1 := mem_bot.mp (hz ▸ hxZ)
  exact mem_bot.mpr (congrArg Subtype.val hx1)


omit [Finite G] in
private theorem normalizer_action_injective {M P : Subgroup G}
    (hn : M ≤ normalizer (P : Set G)) (hc : centralizer (P : Set G) = ⊥) :
    Function.Injective (P.normalizerMonoidHom.comp (inclusion hn)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro x hx
  have hk : inclusion hn x ∈ P.normalizerMonoidHom.ker := hx
  rw [normalizerMonoidHom_ker] at hk
  change x.val ∈ centralizer (P : Set G) at hk
  rw [hc] at hk
  exact mem_bot.mpr (Subtype.ext (mem_bot.mp hk))

variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ)
  (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))
include d h hH hp he

/-- The full factor and parabolic normalizers agree; their whole intersection
preserves the original common Borel. -/
theorem Preparation.ree_full_normalizers_preserve_parabolics :
    (∀ i : Fin 2, normalizer (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i : Set G) =
      normalizer (![L,residual H] i : Set G)) ∧
    normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ≤
      normalizer (ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) : Set G) := by
  obtain ⟨hST,hTL,hTK,_⟩ := d.ree_full_sylow h hH hp m he
  have hl := d.ree_normalizer_local_conditions h hH hp m he
  let I := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  have hIN : I = normalizer ((T : Subgroup G) : Set G) := by
    have hn := hl.normalizer_eq_middle
    rw [inf_eq_left.mpr hTL] at hn
    exact hn.symm
  have hIF (i : Fin 2) : I ≤ normalizer (![L,residual H] i : Set G) := by
    fin_cases i
    · exact inf_le_left
    · exact inf_le_right
  have hTI (i : Fin 2) : (T : Subgroup G) ≤ ![L,residual H] i := by
    fin_cases i
    · exact hTL
    · exact hTK
  have hIb (i : Fin 2) : I ≤
      normalizer (ChapterF.Source.borel (![L,residual H] i) (sourceS L H) : Set G) := by
    change I ≤ normalizer ((![L,residual H] i ⊓
      normalizer ((sourceS L H ⊓ ![L,residual H] i : Subgroup G) : Set G) : Subgroup G) : Set G)
    rw [hST,inf_eq_left.mpr (hTI i)]
    exact (le_inf (hIF i) (hIN ▸ (normalizer ((T : Subgroup G) : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hIS : I ≤ normalizer (sourceS L H : Set G) := by rw [hST,←hIN]
  have hIB : I ≤ normalizer (ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) : Set G) := by
    exact (le_inf ((le_inf (hIb 0) (hIb 1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)) hIS).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  refine ⟨?_,hIB⟩
  intro i
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i
  have hLP : ![L,residual H] i ≤ P := le_sup_left.trans le_sup_left
  have hIP : I ≤ normalizer (P : Set G) := by
    dsimp [P]
    rw [ChapterF.Source.parabolic_eq_sup_commonBorel]
    exact (le_inf (hIF i) hIB).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  apply le_antisymm
  · have hn := normalizer_le_normalizer_characteristic_image P (solvableResidual P)
    rw [d.parabolic_residuals h hH.1.1.2 hp i] at hn
    exact hn
  · have hprod : ∀ x ∈ normalizer (![L,residual H] i : Set G),
        ∃ l ∈ ![L,residual H] i, ∃ b ∈ I, x = l*b := by
      fin_cases i
      · exact hl.factor_left
      · exact hl.factor_right
    intro x hx
    obtain ⟨l,hl,b,hb,rfl⟩ := hprod x hx
    exact (normalizer (P : Set G)).mul_mem (P.le_normalizer (hLP hl)) (hIP hb)

/-- Each original full parabolic has trivial centralizer in the whole ambient group. -/
theorem Preparation.ree_parabolic_centralizers_eq_bot :
    ∀ i : Fin 2,
      centralizer (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i : Set G) = ⊥ := by
  have hn := (d.ree_full_normalizers_preserve_parabolics h hH hp m he).1
  have hl := d.ree_normalizer_local_conditions h hH hp m he
  rcases he with he | he
  · exact (d.not_ree_unreversed h hH.1.1.2 hp m he).elim
  obtain ⟨e⟩ := he
  have hm := d.ree_parameter_positive h hp m 0 .linear e.left
  have hc (i : Fin 2) : center (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i) = ⊥ := by
    let s : ReeF4.LargeLocalSeeds.Side := if i = 0 then .linear else .suzuki
    have heq : Nonempty (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ≃*
        ReeF4.Parabolics.parabolic m s) := by
      fin_cases i
      · exact ⟨e.left⟩
      · exact ⟨e.right⟩
    obtain ⟨a⟩ := heq
    apply le_bot_iff.mp
    intro x hx
    have hy := (centerCongr a ⟨x,hx⟩).property
    change a x ∈ center (ReeF4.Parabolics.parabolic m s) at hy
    rw [ReeF4.SourceCompletion.parabolic_center_eq_bot hm s] at hy
    exact mem_bot.mpr (a.map_eq_one_iff.mp (mem_bot.mp hy))
  intro i
  have hf : centralizer (pCore 2 (normalizer (![L,residual H] i : Set G)) :
      Set (normalizer (![L,residual H] i : Set G))) ≤
        pCore 2 (normalizer (![L,residual H] i : Set G)) := by
    apply (ChapterA.generalizedFitting_eq_pCore_iff 2).mp
    fin_cases i
    · exact hl.fitting_left
    · exact hl.fitting_right
  have hQ : (pCore 2 (normalizer (![L,residual H] i : Set G))).map
      (normalizer (![L,residual H] i : Set G)).subtype =
        (![L,residual H] i).pCoreIn 2 := by
    fin_cases i
    · exact hl.twoCore_left
    · exact hl.twoCore_right
  apply centralizer_eq_bot_of_core _ _ (hn i).le hf _ (hc i)
  rw [hQ]
  exact (pCoreIn_le 2 _).trans (le_sup_left.trans le_sup_left)

/-- Faithful full-normalizer actions on the native parabolics, with the entire
intersection acting compatibly on the native amalgam. The displayed equations
preserve the original conjugation and its actual comparison marking. -/
theorem Preparation.ree_compatible_parabolic_actions :
    ∃ e : RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse,
    ∃ (l : normalizer (L : Set G) →* MulAut (ReeF4.Parabolics.parabolic m .linear))
      (r : normalizer (residual H : Set G) →* MulAut (ReeF4.Parabolics.parabolic m .suzuki))
      (a : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G) →*
        RankTwoAmalgam.Iso (ReeFour.amalgam m).reverse (ReeFour.amalgam m).reverse),
      Function.Injective l ∧ Function.Injective r ∧ Function.Injective a ∧
      (∀ g x, (e.left.symm (l g (e.left x)) : G) = (g : G)*(x : G)*(g : G)⁻¹) ∧
      (∀ g x, (e.right.symm (r g (e.right x)) : G) = (g : G)*(x : G)*(g : G)⁻¹) ∧
      (∀ g, (a g).left = l (inclusion inf_le_left g)) ∧
      (∀ g, (a g).right = r (inclusion inf_le_right g)) ∧
      (∀ g x, (e.middle.symm ((a g).middle (e.middle x)) : G) =
        (g : G)*(x : G)*(g : G)⁻¹) := by
  have hn := (d.ree_full_normalizers_preserve_parabolics h hH hp m he).1
  have hc := d.ree_parabolic_centralizers_eq_bot h hH hp m he
  rcases he with he | he
  · exact (d.not_ree_unreversed h hH.1.1.2 hp m he).elim
  obtain ⟨e⟩ := he
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let Q := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let I := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  have hP : normalizer (L : Set G) ≤ normalizer (P : Set G) := (hn 0).ge
  have hQ : normalizer (residual H : Set G) ≤ normalizer (Q : Set G) := (hn 1).ge
  let l₀ := P.normalizerMonoidHom.comp (inclusion hP)
  let r₀ := Q.normalizerMonoidHom.comp (inclusion hQ)
  let l := (MulAut.congr e.left).toMonoidHom.comp l₀
  let r := (MulAut.congr e.right).toMonoidHom.comp r₀
  let a₀ := RankTwoAmalgam.conjugationAction P Q I
    (inf_le_left.trans hP) (inf_le_right.trans hQ)
  let a := (RankTwoAmalgam.automorphismConjEquiv e).toMonoidHom.comp a₀
  have hl : Function.Injective l :=
    (MulAut.congr e.left).injective.comp (normalizer_action_injective hP (hc 0))
  have hr : Function.Injective r :=
    (MulAut.congr e.right).injective.comp (normalizer_action_injective hQ (hc 1))
  have hal (g : I) : (a g).left = l (inclusion inf_le_left g) := rfl
  have har (g : I) : (a g).right = r (inclusion inf_le_right g) := rfl
  have ha : Function.Injective a := by
    intro x y hxy
    apply inclusion_injective (show I ≤ normalizer (L : Set G) from inf_le_left)
    apply hl
    exact (hal x).symm.trans ((congrArg (fun b => b.left) hxy).trans (hal y))
  refine ⟨e,l,r,a,hl,hr,ha,?_,?_,hal,har,?_⟩
  · intro g x
    change (e.left.symm (e.left (l₀ g (e.left.symm (e.left x)))) : G) = _
    simp only [e.left.symm_apply_apply]
    rfl
  · intro g x
    change (e.right.symm (e.right (r₀ g (e.right.symm (e.right x)))) : G) = _
    simp only [e.right.symm_apply_apply]
    rfl
  · intro g x
    change (e.middle.symm (e.middle ((a₀ g).middle (e.middle.symm (e.middle x)))) : G) = _
    simp only [e.middle.symm_apply_apply]
    rfl

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
