module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceGraphActor
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceGraphDescent
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.AmbientLocalCores

/-!
# A root-plane frame for the original cubic

The selected cubic lies in the original component and normalizes the original
root, so it normalizes the literal secondary subgroup. In the common model
frame it preserves the secondary local and its characteristic two-core, the
root plane. The exact cubic projection kernel separates every nonidentity
cubic element from the projective special-linear component.

The full quotient marking is chosen before constructing the projective
extension. Thus root-plane preservation, the component projection square and
the subsequent Frattini marking all use the same coordinates.
Source: Aschbacher--Smith, original 4.3.14--16 and the conclusion of 4.3.2,
printed pp.617--619; B.4.14, printed p.98.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
open Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}
namespace SecondaryActionData

omit [Finite G] in
/-- An original component element preserving the root preserves the secondary image. -/
theorem original_preserves_secondary_image (s : SecondaryActionData c n)
    (x : rootNormalizer c) (hx : (x : G) ∈ K c) :
    (secondaryImage s).map (MulAut.conj (s.action x)).toMonoidHom = secondaryImage s := by
  have hn : (x : G) ∈ normalizer (secondary c : Set G) :=
    original_normalizes_secondary (zpowers_le.mpr hx)
      (zpowers_le.mpr x.property) (mem_zpowers (x : G))
  have hn' : x ∈ normalizer ((secondary c).subgroupOf (rootNormalizer c) :
      Set (rootNormalizer c)) := by
    apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp hn (y : G)
  exact mem_normalizer_iff_map_conj_eq.mp
    (((secondary c).subgroupOf (rootNormalizer c)).le_normalizer_map s.action
      (mem_map_of_mem s.action hn'))

private theorem frame_map_actor {A B : Type*} [Group A] [Group B]
    (H : Subgroup A) (a : MulAut A) (e : A ≃* B) :
    (H.map a.toMonoidHom).map e.toMonoidHom =
      (H.map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom := by
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.congr_apply]

/-- One full quotient marking makes every original root-normalizing actor preserve a root plane. -/
theorem exists_original_root_plane_marking (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V) (hg : ActionGeneration s)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2^f)
    (mark : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F)) :
    ∃ (a : MulAut PSL(3,F)) (b : Bool),
      ∀ (x : rootNormalizer c), (x : G) ∈ K c →
        (rootPlane F b).map ((MulAut.congr (mark.trans a)) (s.action x)).toMonoidHom =
          rootPlane F b := by
  obtain ⟨e,he⟩ := exists_inner_marking s mark
  obtain ⟨a,b,_,hB⟩ := root_local_frame s D hg hf hF e
  refine ⟨a,b,?_⟩
  intro x hx
  let B := ((secondaryImage s).subgroupOf (componentImage s)).map e.toMonoidHom
  let z := (MulAut.congr mark) (s.action x)
  have hBz : B.map z.toMonoidHom = B :=
    model_image_preserves s mark e he (secondaryImage s)
      (secondaryImage_le_componentImage s) (s.action x)
      (original_preserves_secondary_image s x hx)
  have hBa : B.map a.toMonoidHom = localFactor F b := by
    rw [Subgroup.map_map]
    exact hB
  have hlocal : (localFactor F b).map (MulAut.congr a z).toMonoidHom = localFactor F b := by
    rw [←hBa,←frame_map_actor,hBz]
  have hroot : (rootPlane F b).map (MulAut.congr a z).toMonoidHom = rootPlane F b := by
    rw [←AmbientLocalCores.local_core_eq_rootPlane F (by omega : 0 < f) hF b,
      map_pCoreIn_of_injective 2 _ _ (MulAut.congr a z).injective,hlocal]
  exact hroot

end SecondaryActionData
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 G} {L V : Subgroup G} {c : SourceConfiguration T L}

/-- The original cubic subgroup included in its extension with the selected component. -/
def cubicSourceInclusion (s : SecondaryActionData c 2) (X : Subgroup G)
    (hXr : X ≤ rootNormalizer c) : X →* cubicExtension s X :=
  (inclusion (show X.subgroupOf (rootNormalizer c) ≤ cubicExtension s X from le_sup_right)).comp
    (subgroupOfEquivOfLe hXr).symm.toMonoidHom

omit [Finite G] [Finite F] [CharP F 2] in
/-- The exact projection kernel makes every nonidentity source cubic actor outer. -/
theorem source_cubic_projection_outer (s : SecondaryActionData c 2)
    (mark : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F))
    (X : Subgroup G) (hXr : X ≤ rootNormalizer c)
    (hdisj : X ⊓ s.component.map (rootNormalizer c).subtype = ⊥)
    (φ : cubicExtension s X →* ProjGenLinGroup (Fin 3) F)
    (hker : φ.ker = (pCore 2 s.component).map (cubicComponentInclusion s X))
    (hsquare : ∀ b : s.component, φ (cubicComponentInclusion s X b) =
      ProjectiveSpecialLinearGroup.toPGL (mark (QuotientGroup.mk' (pCore 2 s.component) b)))
    (x : X) (hx : x ≠ 1) :
    (pglEquivInnerDiagonal F (φ (cubicSourceInclusion s X hXr x))).val ∉
      MulAut.innerSubgroup PSL(3,F) := by
  rintro ⟨z,hz⟩
  obtain ⟨q,rfl⟩ := mark.surjective z
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 s.component) q
  have he : φ (cubicSourceInclusion s X hXr x) = φ (cubicComponentInclusion s X b) := by
    apply (pglEquivInnerDiagonal F).injective
    apply Subtype.ext
    rw [hsquare,pglEquiv_component]
    exact hz.symm
  have hk : cubicSourceInclusion s X hXr x / cubicComponentInclusion s X b ∈
      (pCore 2 s.component).map (cubicComponentInclusion s X) := by
    rw [←hker]
    exact φ.div_mem_ker_iff.mpr he
  obtain ⟨k,_,hk⟩ := hk
  have heq : cubicSourceInclusion s X hXr x = cubicComponentInclusion s X (k*b) := by
    rw [map_mul,hk,div_mul_cancel]
  have hxc : (x : G) ∈ s.component.map (rootNormalizer c).subtype := by
    refine ⟨(k*b : s.component).val,(k*b).property,?_⟩
    exact (congrArg (fun y : cubicExtension s X => ((y : rootNormalizer c) : G)) heq).symm
  apply hx
  apply Subtype.ext
  exact mem_bot.mp (hdisj.le ⟨x.property,hxc⟩)

/-- The source cubic and its exact projective extension preserve one marked root plane. -/
theorem exists_source_cubic_root_frame (d : MSData c 2)
    (s : SecondaryActionData c 2) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hg : EndgameSieve.SecondaryActionData.ActionGeneration s)
    (hF : Nat.card F = 4)
    (mark : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F)) :
    ∃ (mark' : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F)) (b : Bool)
      (X : Subgroup G) (hXr : X ≤ rootNormalizer c),
      Nat.card X = 3 ∧ X ≤ (K c).coreCenterIn 2 ∧
      Q c ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧
      ⁅secondary c,X⁆ ≤ (secondary c).pCoreIn 2 ∧
      ∃ φ : cubicExtension s X →* ProjGenLinGroup (Fin 3) F,
        Function.Surjective φ ∧
        φ.ker = (pCore 2 s.component).map (cubicComponentInclusion s X) ∧
        (∀ k : s.component, φ (cubicComponentInclusion s X k) =
          ProjectiveSpecialLinearGroup.toPGL
            (mark' (QuotientGroup.mk' (pCore 2 s.component) k))) ∧
        ∀ x : X,
          (φ (cubicSourceInclusion s X hXr x)) ^ 3 = 1 ∧
          (rootPlane F b).map
              (pglEquivInnerDiagonal F (φ (cubicSourceInclusion s X hXr x))).val.toMonoidHom =
            rootPlane F b ∧
          (x ≠ 1 → (pglEquivInnerDiagonal F (φ (cubicSourceInclusion s X hXr x))).val ∉
            MulAut.innerSubgroup PSL(3,F)) := by
  obtain ⟨a,b,hframe⟩ := EndgameSieve.SecondaryActionData.exists_original_root_plane_marking
    s D hg (by decide : 1 < 2) (show Nat.card F = 2^2 from hF) mark
  let mark' := mark.trans a
  obtain ⟨X,hX,hXK,hXr,hdisj,hfix,hcomm,_,φ,hφ,hker,_,hsquare,_⟩ :=
    exists_source_cubic_extension d s D h hF mark'
  refine ⟨mark',b,X,hXr,hX,hXK,hfix,hcomm,φ,hφ,hker,hsquare,?_⟩
  intro x
  refine ⟨?_,?_,source_cubic_projection_outer s mark' X hXr hdisj φ hker hsquare x⟩
  · have hx3 : x ^ 3 = (1 : X) := by
      simpa only [hX] using (pow_card_eq_one' (x := x))
    have hx3' : (cubicSourceInclusion s X hXr x) ^ 3 =
        (1 : cubicExtension s X) := by
      rw [← map_pow, hx3, map_one]
    rw [← map_pow, hx3', map_one]
  · rw [←cubic_extension_actor s mark' X φ hsquare]
    exact hframe (cubicSourceInclusion s X hXr x)
      (coreCenterIn_le 2 (K c) (hXK x.property))

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
