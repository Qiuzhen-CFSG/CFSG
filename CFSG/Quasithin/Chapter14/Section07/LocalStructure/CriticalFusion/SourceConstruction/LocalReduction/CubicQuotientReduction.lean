module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicMovingPlane
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SeedSeparation
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt

/-!
# Failed plane lifting through an arbitrary proper invariant quotient

Take the original U/V₁ conjugation section and any equivariant linear map
with proper kernel. If a two-perfect actor Y normalizes the seed and fixes
the image of V₂, seed separation puts its plane displacement in V₁. Thus Y
normalizes, and hence centralizes, V₂. Consequently a failed lift gives an
actual actor outside N_G(L), using the original structural normalizer identity.
The escape conclusion also has a same-G,T many-overgroup specialization.

For a T-normalized cubic actor, the failed lift feeds the moving-plane
completion with its original subgroup maps. We obtain the exact solvable
kernel, the two-reduced Goldschmidt quotient and either solvability of the
completion or an actual faithful A₅/L₃(2) component. This proves the initial
reduction in the contrary case of 14.7.2(3), not the full lifting theorem;
its remaining component exclusions and solvable endgame are still required.

Source: Aschbacher–Smith, 14.7.2(1),(3), printed p.1043, using the
14.5.3–8 construction, printed pp.1013–1015, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

open Representation in
/-- Seed separation lifts fixation through an arbitrary proper invariant quotient
for an actor that normalizes the original seed. -/
theorem quotient_plane_fixed_of_seed_normalized
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    {W X : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) F.H W} {σ : Representation (ZMod 2) F.H X}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap σ) (hp : p.toLinearMap.ker ≠ ⊤)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYV : Y ≤ normalizer (V : Set G))
    (hfix : ∀ y (hy : y ∈ Y) (v : F.U), (v : G) ∈ F.Vi 2 →
      σ ⟨y,hYH hy⟩ (p (c.coordinates v).toAdd) = p (c.coordinates v).toAdd) :
    ⁅F.Vi 2,Y⁆ = ⊥ := by
  have hs := seed_intersection h c p.toLinearMap.ker (by
    intro g w hw
    change p (ρ g w) = 0
    rw [p.isIntertwining, show p w = 0 from hw, map_zero]) hp
  apply moving_plane_centralized_of_normalized Y hYH hYp
  apply le_normalizer_iff_commutator_le_right.mpr
  apply le_trans ?_ (F.monotone (by decide : 1 ≤ 2))
  apply commutator_le.mpr
  intro y hy v hv
  let u : F.U := ⟨v, le_conjugateSpanBy V F.H (F.le_seed 2 hv)⟩
  let yu : F.U := ⟨y*v*y⁻¹,(mem_normalizer_iff.mp (c.normalized (hYH hy)) v).mp u.property⟩
  have hyu : (yu : G) ∈ V := (mem_normalizer_iff.mp (hYV hy) v).mp (F.le_seed 2 hv)
  have hb : ((yu*u⁻¹ : F.U) : G) ∈ V := V.mul_mem hyu (V.inv_mem (F.le_seed 2 hv))
  apply (hs (yu*u⁻¹) hb).mp
  change p ((c.coordinates (yu*u⁻¹)).toAdd) = 0
  rw [map_mul,map_inv,toAdd_mul,toAdd_inv,←sub_eq_add_neg]
  rw [map_sub, show (c.coordinates yu).toAdd = ρ ⟨y,hYH hy⟩ (c.coordinates u).toAdd
    from c.equivariant ⟨y,hYH hy⟩ u, p.isIntertwining,hfix y hy u hv,sub_self]

open Representation in
/-- A failure of the original quotient lift is an actual escaping actor.
The kernel is only required to be proper and invariant. -/
theorem quotient_plane_moving_actor_escapes_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    {W X : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) F.H W} {σ : Representation (ZMod 2) F.H X}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap σ) (hp : p.toLinearMap.ker ≠ ⊤)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hfix : ∀ y (hy : y ∈ Y) (v : F.U), (v : G) ∈ F.Vi 2 →
      σ ⟨y,hYH hy⟩ (p (c.coordinates v).toAdd) = p (c.coordinates v).toAdd)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) : ¬ Y ≤ normalizer (L : Set G) := by
  intro hYL
  have hne : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    simp [he] at hc
  have he := structural.intersection_normalizer h.source h.chosen hne (F.le_seed 1)
    (le_rfl : F.H ≤ normalizer (F.Vi 1 : Set G))
  have hYV : Y ≤ normalizer (V : Set G) := by
    have hh : Y ≤ F.H ⊓ normalizer (L : Set G) := le_inf hYH hYL
    rw [he] at hh
    exact hh.trans inf_le_right
  exact hm (quotient_plane_fixed_of_seed_normalized h c p hp Y hYH hYp hYV hfix)


open Representation Chapter14.Section04.LargerDimension.LocalAction.Components in
/-- On the literal original quotient, failed plane lifting gives an escaping
cubic completion, its exact solvable kernel and its two-reduced Goldschmidt
quotient. Its nonsolvable branch has an actual faithful A₅ or L₃(2) component,
with a normal action image and the original residual orientations. -/
theorem original_quotient_plane_lifting_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    {W X : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) F.H W} {σ : Representation (ZMod 2) F.H X}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap σ) (hp : p.toLinearMap.ker ≠ ⊤)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (hfix : ∀ y (hy : y ∈ Y) (v : F.U), (v : G) ∈ F.Vi 2 →
      σ ⟨y,hYH hy⟩ (p (c.coordinates v).toAdd) = p (c.coordinates v).toAdd)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let E := conjugateSpanBy (F.Vi 1) D
    letI : (E.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (E.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    ¬ Y ≤ normalizer (L : Set G) ∧
      ((F.P L).subgroupOf D ⊓ C = pCore 2 D ∧
       (Y ⊔ (T : Subgroup G)).subgroupOf D ⊓ C = pCore 2 D ∧
       Group.IsSolvable C) ∧
      (((F.P L).subgroupOf D).map q ⊓ ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q =
        ((T : Subgroup G).subgroupOf D).map q ∧
       ChapterF.IsGoldschmidtTriple ((F.P L).subgroupOf D |>.map q)
        ((Y ⊔ (T : Subgroup G)).subgroupOf D |>.map q) ∧
       pCore 2 (D ⧸ C) = ⊥) ∧
      (Group.IsSolvable D ∨ ∃ J : Subgroup G, J ≤ D ∧
        (J.subgroupOf D).IsCComponent ∧ J ∈ Chapter1.LStar G (T : Subgroup G) ∧
        ChapterA.Section04.IsFaithfulSignalizerType J ∧
        (J.subgroupOf (J ⊔ (T : Subgroup G))).Normal ∧
        (Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∨
         Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.PSL)) ∧
        (J.subgroupOf D).Normal ∧
        IsComponent (D ⧸ C) ((J.subgroupOf D).map q) ∧
        ((J.subgroupOf D).map q).Normal ∧
        ((((F.Li L 2).subgroupOf D).map q ≤ (J.subgroupOf D).map q ∧
          (J.subgroupOf D).map q ⊔ ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q = ⊤) ∨
         ((Y.subgroupOf D).map q ≤ (J.subgroupOf D).map q ∧
          (J.subgroupOf D).map q ⊔ ((F.P L).subgroupOf D).map q = ⊤))) := by
  refine ⟨quotient_plane_moving_actor_escapes_at h (structural G T) c p hp Y hYH hYp hfix hm,
    cubic_generated_action_kernel_of_moving_plane h hab structural previous Y hYH hm hYp hYT he,
    cubic_generated_action_triple_of_moving_plane h hab structural previous Y hYH hm hYp hYT he,?_⟩
  by_cases hs : Group.IsSolvable (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G)
  · exact Or.inl hs
  · obtain ⟨J,hJD,hJ,hJL,hJf,hn,hmodel⟩ := cubic_generated_nonsolvable_component_of_moving_plane
      h hab structural previous faithful Y hYH hm hYp hYT he hs
    exact Or.inr ⟨J,hJD,hJ,hJL,hJf,hn,hmodel,
      cubic_generated_component_action_reduction_of_moving_plane
        h hab structural previous faithful Y hYH hm hYp hYT he (J.subgroupOf _) hJ⟩

open Representation in
/-- The escape step for the actual many-overgroup consumer needs only
structural input at the same G,T. -/
theorem quotient_plane_moving_actor_escapes_of_many_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    {W X : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) F.H W} {σ : Representation (ZMod 2) F.H X}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap σ) (hp : p.toLinearMap.ker ≠ ⊤)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hfix : ∀ y (hy : y ∈ Y) (v : F.U), (v : G) ∈ F.Vi 2 →
      σ ⟨y,hYH hy⟩ (p (c.coordinates v).toAdd) = p (c.coordinates v).toAdd)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) : ¬ Y ≤ normalizer (L : Set G) :=
  quotient_plane_moving_actor_escapes_at h (structural hmany) c p hp Y hYH hYp hfix hm

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
