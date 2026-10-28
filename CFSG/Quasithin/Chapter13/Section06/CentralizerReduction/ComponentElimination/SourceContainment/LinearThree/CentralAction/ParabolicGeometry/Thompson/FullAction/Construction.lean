module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Applicability.Preparation
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.GroupTheory.PResidual.NormalSubgroup
/-!
# The literal full action in doubled coordinates

Normality of K+ makes [W_K,K] invariant under the full plus actor. The
conjugation action descends through the actual centralizer quotient and is
transported through the given doubled marking. Its restriction is precisely
the diagonal natural action, and its range normalizes that diagonal group.
No faithfulness on U_K or radical identification is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.6.20, printed p.931.
-/

@[expose] public section
open Subgroup Representation BinaryLinearThree
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.FullAction
open ComponentSelection ModuleAlternatives Representation.BinaryOffender
variable {G : Type*} [_root_.Group G] [Finite G]
    {K L T : Subgroup G} {z v : G}
variable (e : EarlierData K L T z v)

include e in
/-- The full actor preserves its component commutator module. -/
theorem normalizes_UK : plusActor K L T v ≤ normalizer (UK K L T z v : Set G) := by
  let := wk_elementary K L T z v e.selected.1.1 e.tvSylow e.seedOmega e.characteristicTwo
  let := plusImage_K_normal K L T z v e.normalizeL e.fixSeed e.selected e.normalizeK
  let ρ := wkRepresentation K L T z v e.normalizeL e.fixSeed
  have hstab : (⊤ : Subgroup (Gplus K L T z v e.normalizeL e.fixSeed)) ≤
      subspaceStabilizer ρ (ukSubspace K L T z v) := by
    rw [← moved_eq_ukSubspace K L T z v e.normalizeL e.fixSeed]
    exact subspaceCommutator_invariant_normalizer ρ (by intro a _ w; exact iff_of_true (by trivial) (by trivial))
      le_normalizer_of_normal
  apply le_normalizer_iff.mpr
  intro a ha u hu
  let w : Additive (WK K L T z v) := Additive.ofMul
    ⟨u, UK_le_WK K L T z v e.normalizeL e.fixSeed hu⟩
  have hw := (hstab (mem_top (plusMk K L T z v e.normalizeL e.fixSeed ⟨a, ha⟩)) w).mpr hu
  exact hw

noncomputable def ukAut : Gplus K L T z v e.normalizeL e.fixSeed →* MulAut (UK K L T z v) :=
  (plusMk K L T z v e.normalizeL e.fixSeed).liftOfSurjective
    (plusMk_surjective K L T z v e.normalizeL e.fixSeed)
    ⟨conjugationAction _ _ (normalizes_UK e), by
      rw [plusMk_ker, conjugationAction_ker]
      exact comap_mono (centralizer_le (UK_le_WK K L T z v e.normalizeL e.fixSeed))⟩

theorem ukAut_mk (a : plusActor K L T v) :
    ukAut e (plusMk K L T z v e.normalizeL e.fixSeed a) =
      conjugationAction _ _ (normalizes_UK e) a := by
  unfold ukAut
  rw [MonoidHom.liftOfRightInverse_comp_apply]

variable (d : DoubledCoordinates K L T z v e.selected.1.1 e.normalizeL e.fixSeed)

noncomputable def representation : Representation (ZMod 2)
    (Gplus K L T z v e.normalizeL e.fixSeed) (Vector × Vector) where
  toFun g := (AddMonoidHom.toMultiplicative.symm ((d.moduleEquiv.symm.trans (ukAut e g)).trans d.moduleEquiv).toMonoidHom).toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro w
    change (d.moduleEquiv (ukAut e 1 (d.moduleEquiv.symm (Multiplicative.ofAdd w)))).toAdd = w
    rw [map_one]
    exact congrArg Multiplicative.toAdd (d.moduleEquiv.apply_symm_apply _)
  map_mul' g h := by
    apply LinearMap.ext
    intro w
    change (d.moduleEquiv (ukAut e (g * h) (d.moduleEquiv.symm (Multiplicative.ofAdd w)))).toAdd = _
    rw [map_mul]
    change (d.moduleEquiv (ukAut e g (ukAut e h (d.moduleEquiv.symm (Multiplicative.ofAdd w))))).toAdd =
      (d.moduleEquiv (ukAut e g (d.moduleEquiv.symm (d.moduleEquiv (ukAut e h (d.moduleEquiv.symm (Multiplicative.ofAdd w))))))).toAdd
    rw [d.moduleEquiv.symm_apply_apply]

noncomputable def action : Gplus K L T z v e.normalizeL e.fixSeed →*
    (Module.End (ZMod 2) (Vector × Vector))ˣ := (representation e d).asGroupHom

theorem equivariant (a : plusActor K L T v) (u : UK K L T z v) :
    d.moduleEquiv (conjugationAction _ _ (normalizes_UK e) a u) =
      Multiplicative.ofAdd ((action e d (plusMk K L T z v e.normalizeL e.fixSeed a) :
        Module.End (ZMod 2) (Vector × Vector)) (d.moduleEquiv u).toAdd) := by
  change _ = d.moduleEquiv (ukAut e (plusMk K L T z v e.normalizeL e.fixSeed a)
    (d.moduleEquiv.symm (d.moduleEquiv u)))
  rw [d.moduleEquiv.symm_apply_apply, ukAut_mk]

theorem on_component :
    (action e d).comp (modelEmbedding d) = (W.prod W).asGroupHom := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply LinearMap.ext
  intro w
  obtain ⟨k, rfl⟩ := d.actionMap_surjective g
  let u := d.moduleEquiv.symm (Multiplicative.ofAdd w)
  have hu : (d.moduleEquiv u).toAdd = w := congrArg Multiplicative.toAdd (d.moduleEquiv.apply_symm_apply _)
  rw [← hu]
  rw [MonoidHom.comp_apply, modelEmbedding_actionMap]
  exact congrArg Multiplicative.toAdd ((equivariant e d
    (inclusion (K_le_plusActor K L T v) k) u).symm.trans (d.equivariant k u))


omit [Finite G] in
/-- The original three source factors generate the full plus group. -/
theorem plus_generates :
    plusImage K L T z v e.normalizeL e.fixSeed K ⊔
      plusImage K L T z v e.normalizeL e.fixSeed (Lv L v) ⊔
      plusImage K L T z v e.normalizeL e.fixSeed (Tv T v) = ⊤ := by
  let A := plusActor K L T v
  have hi : K.subgroupOf A ⊔ (Lv L v).subgroupOf A ⊔ (Tv T v).subgroupOf A = ⊤ := by
    apply map_injective A.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_sup, map_subgroupOf_eq_of_le (K_le_plusActor K L T v),
      map_subgroupOf_eq_of_le (show Lv L v ≤ A from le_sup_right.trans le_sup_left),
      map_subgroupOf_eq_of_le (show Tv T v ≤ A from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
    exact (congrArg (fun B => B ⊔ Lv L v ⊔ Tv T v)
      (Kminus_eq_of_invariant K T v e.normalizeK)).symm
  have hm := congrArg (map (plusMk K L T z v e.normalizeL e.fixSeed)) hi
  simpa only [plusImage, A, Subgroup.map_sup, map_top_of_surjective _
    (plusMk_surjective K L T z v e.normalizeL e.fixSeed)] using hm

omit [Finite G] in
/-- Centrality makes the residual image normal in the entire plus group. -/
theorem residual_normal
    (hc : ⁅plusImage K L T z v e.normalizeL e.fixSeed K,
      plusImage K L T z v e.normalizeL e.fixSeed (Lv L v)⁆ = ⊥) :
    (plusImage K L T z v e.normalizeL e.fixSeed (Lv L v)).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← plus_generates e]
  refine sup_le (sup_le
    ((commutator_eq_bot_iff_le_centralizer.mp hc).trans (Subgroup.centralizer_le_normalizer _))
    (plusImage K L T z v e.normalizeL e.fixSeed (Lv L v)).le_normalizer) ?_
  apply le_trans (map_mono (f := plusMk K L T z v e.normalizeL e.fixSeed) ?_)
    (((Lv L v).subgroupOf (plusActor K L T v)).le_normalizer_map _)
  rw [← subgroupOf_normalizer_eq (show Lv L v ≤ plusActor K L T v from le_sup_right.trans le_sup_left)]
  exact comap_mono e.normalizeL

/-- The doubled diagonal action is faithful. -/
theorem diagonal_injective : Function.Injective (W.prod W).asGroupHom := by
  intro a b h
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext w
  exact congrArg Prod.fst (LinearMap.congr_fun (congrArg Units.val h) (w, 0))

/-- The full action agrees with the supplied actor marking on K+. -/
theorem action_component (k : plusImage K L T z v e.normalizeL e.fixSeed K) :
    action e d k = (W.prod W).asGroupHom (d.actor k) := by
  have h := DFunLike.congr_fun (on_component e d) (d.actor k)
  simpa only [MonoidHom.comp_apply, modelEmbedding, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, coe_subtype] using h

theorem faithful_component : Function.Injective
    ((action e d).comp (plusImage K L T z v e.normalizeL e.fixSeed K).subtype) := by
  intro a b h
  apply d.actor.injective
  apply diagonal_injective
  exact (action_component e d a).symm.trans (h.trans (action_component e d b))

/-- The range of the full action normalizes the literal diagonal component. -/
theorem normalizes_diagonal : (action e d).range ≤
    normalizer ((W.prod W).asGroupHom.range : Set (Module.End (ZMod 2) (Vector × Vector))ˣ) := by
  let C := plusImage K L T z v e.normalizeL e.fixSeed K
  let := plusImage_K_normal K L T z v e.normalizeL e.fixSeed e.selected e.normalizeK
  have he : C.map (action e d) = (W.prod W).asGroupHom.range := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨d.actor ⟨k, hk⟩, (action_component e d ⟨k, hk⟩).symm⟩
    · rintro ⟨g, rfl⟩
      refine ⟨d.actor.symm g, (d.actor.symm g).property, ?_⟩
      rw [action_component, d.actor.apply_symm_apply]
  rw [← he]
  rintro _ ⟨a, rfl⟩
  exact C.le_normalizer_map (action e d)
    ⟨a, (le_normalizer_of_normal (show a ∈ (⊤ : Subgroup _) from mem_top a)), rfl⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Thompson.FullAction
