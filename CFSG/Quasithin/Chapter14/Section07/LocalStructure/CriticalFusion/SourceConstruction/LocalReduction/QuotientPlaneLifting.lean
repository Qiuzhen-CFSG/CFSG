module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicMovingEndgame
public import Theory.Representation.SubspaceQuotient
public import Theory.Representation.BinaryConjugationSection.ImageDimensions

/-!
# Cubic orbits and fixation in proper quotients of the original section

A T-normalized two-perfect cubic actor fixing the plane image in any proper
invariant quotient of the original U/V₁ section centralizes the actual flag
plane. If it moved that plane, seed separation would force it outside N_G(L),
contradicting the moving-plane endgame.

The same endgame puts every cubic plane orbit inside the seed: an escaping
actor fixes the plane, while a contained actor normalizes the seed. Seed
separation then bounds the dimension of its image in every proper quotient
between one and two. Both source applications construct the literal projection
onto the quotient by a proper subrepresentation. They retain the universal
earlier inputs required by the endgame; the guarded same-G,T application
and the remaining model exclusions are separate obligations.

Source: Aschbacher–Smith, 14.5.3(1), printed p.1013, and 14.7.2(2),(3),
printed p.1043, with the completion
argument of 14.5.9–13, printed pp.1015–1017, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Fixation in a proper quotient lifts to centralization of the original plane.
The section, quotient map and actor are the original ones. -/
theorem original_quotient_plane_fixed
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
      σ ⟨y,hYH hy⟩ (p (c.coordinates v).toAdd) = p (c.coordinates v).toAdd) :
    ⁅F.Vi 2,Y⁆ = ⊥ := by
  by_contra hm
  exact original_quotient_plane_lifting_cyclic_overlap_impossible h hab structural previous
    faithful c p hp Y hYH hYp hYT he hfix hm

/-- Source 14.7.2(3) at the original point normalizer, for the actual quotient
by any proper invariant subspace of the literal section. -/
theorem original_invariant_quotient_plane_fixed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (I : Subrepresentation ρ) (hI : I.toSubmodule ≠ ⊤)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (hfix : ∀ y (hy : y ∈ Y) (v : F.U), (v : G) ∈ F.Vi 2 →
      I.quotientRepresentation ⟨y,hYH hy⟩ (I.toSubmodule.mkQ (c.coordinates v).toAdd) =
        I.toSubmodule.mkQ (c.coordinates v).toAdd) :
    ⁅F.Vi 2,Y⁆ = ⊥ := by
  let p : ρ.IntertwiningMap I.quotientRepresentation := {
    toLinearMap := I.toSubmodule.mkQ
    isIntertwining' := fun _ => rfl }
  have hp : p.toLinearMap.ker ≠ ⊤ := by
    change I.toSubmodule.mkQ.ker ≠ ⊤
    rwa [Submodule.ker_mkQ]
  exact original_quotient_plane_fixed h hab structural previous faithful c p hp
    Y hYH hYp hYT he hfix

/-- The source alternative 14.5.3(1), for the same original cubic actor. -/
theorem original_cubic_actor_contained_or_plane_fixed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    Y ≤ normalizer (L : Set G) ∨ ⁅F.Vi 2,Y⁆ = ⊥ := by
  by_cases hout : Y ≤ normalizer (L : Set G)
  · exact Or.inl hout
  right
  by_contra hm
  exact cubic_moving_plane_impossible h hab structural previous faithful
    Y hYH hm hYp hYT hout he

/-- The entire original cubic orbit of the plane stays inside the seed.
An escaping actor fixes the plane; a contained actor normalizes the seed. -/
theorem original_cubic_plane_span_le_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    conjugateSpanBy (F.Vi 2) Y ≤ V := by
  rcases original_cubic_actor_contained_or_plane_fixed h hab structural previous faithful
    Y hYH hYp hYT he with hYL | hc
  · have hne : F.Vi 1 ≠ ⊥ := by
      intro hz
      have hh := F.card 1 (by decide)
      simp [hz] at hh
    have hs : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T :=
      structural G T
    have hnorm := hs.intersection_normalizer h.source h.chosen
      hne (F.le_seed 1) (le_rfl : F.H ≤ normalizer (F.Vi 1 : Set G))
    have hYV : Y ≤ normalizer (V : Set G) := by
      have hh : Y ≤ F.H ⊓ normalizer (L : Set G) := le_inf hYH hYL
      rw [hnorm] at hh
      exact hh.trans inf_le_right
    exact conjugateSpanBy_le (F.le_seed 2) hYV
  · have hYC : Y ≤ centralizer (F.Vi 2 : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
    exact (conjugateSpanBy_le le_rfl
      (hYC.trans (Subgroup.centralizer_le_normalizer _))).trans (F.le_seed 2)

/-- Source 14.7.2(2): the literal cubic orbit image has dimension one or two
in every proper invariant quotient of the original section. -/
theorem original_quotient_cubic_plane_span_dimension
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
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let E := (c.imageSpace (conjugateSpanBy (F.Vi 2) Y)).map p.toLinearMap
    Module.finrank (ZMod 2) E = 1 ∨ Module.finrank (ZMod 2) E = 2 := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (c.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let E := (c.imageSpace (conjugateSpanBy (F.Vi 2) Y)).map p.toLinearMap
  have hindex : (F.Vi 1).relIndex V = 4 := by
    have hh := relIndex_mul_card_of_le (F.le_seed 1)
    have hcard : Nat.card V = 8 := by
      simpa only [F.last,Nat.reducePow] using F.card 3 (by decide)
    rw [F.card 1 (by decide),hcard] at hh
    norm_num at hh ⊢
    omega
  have hdim : Module.finrank (ZMod 2) (c.imageSpace V) = 2 :=
    c.imageSpace_finrank_of_index V (le_conjugateSpanBy V F.H) 2 hindex
  have hupper : Module.finrank (ZMod 2) E ≤ 2 :=
    (Submodule.finrank_map_le p.toLinearMap _).trans
      ((Submodule.finrank_mono (c.imageSpace_mono
        (original_cubic_plane_span_le_seed h hab structural previous faithful
          Y hYH hYp hYT he))).trans_eq hdim)
  have hnot : ¬ F.Vi 2 ≤ F.Vi 1 := by
    intro hle
    have hh := card_le_of_le hle
    rw [F.card 2 (by decide),F.card 1 (by decide)] at hh
    norm_num at hh
  obtain ⟨v,hv,hvZ⟩ := SetLike.not_le_iff_exists.mp hnot
  let vU : F.U := ⟨v,(le_conjugateSpanBy V F.H) (F.le_seed 2 hv)⟩
  have hsep := seed_intersection h c p.toLinearMap.ker (by
    intro g w hw
    change p (ρ g w) = 0
    rw [p.isIntertwining,show p w = 0 from hw,map_zero]) hp
  have hv0 : p (c.coordinates vU).toAdd ≠ 0 := by
    intro hz
    exact hvZ ((hsep vU (F.le_seed 2 hv)).mp hz)
  have hvE : p (c.coordinates vU).toAdd ∈ E :=
    ⟨_,(c.mem_imageSpace_iff _ _).mpr
      ⟨vU,le_conjugateSpanBy _ _ hv,rfl⟩,rfl⟩
  have hpos : 0 < Module.finrank (ZMod 2) E :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨_,hvE⟩,
      fun hz => hv0 (congrArg Subtype.val hz)⟩
  change Module.finrank (ZMod 2) E = 1 ∨ Module.finrank (ZMod 2) E = 2
  omega

/-- The canonical invariant-quotient application of 14.7.2(2), with the
same plane, actor, and quotient projection. -/
theorem original_invariant_quotient_cubic_plane_span_dimension
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (I : Subrepresentation ρ) (hI : I.toSubmodule ≠ ⊤)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let E := (c.imageSpace (conjugateSpanBy (F.Vi 2) Y)).map I.toSubmodule.mkQ
    Module.finrank (ZMod 2) E = 1 ∨ Module.finrank (ZMod 2) E = 2 := by
  let p : ρ.IntertwiningMap I.quotientRepresentation := {
    toLinearMap := I.toSubmodule.mkQ
    isIntertwining' := fun _ => rfl }
  have hp : p.toLinearMap.ker ≠ ⊤ := by
    change I.toSubmodule.mkQ.ker ≠ ⊤
    rwa [Submodule.ker_mkQ]
  exact original_quotient_cubic_plane_span_dimension h hab structural previous faithful
    c p hp Y hYH hYp hYT he

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
