module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometrySylow
public import CFSG.Quasithin.ChapterE.Section03.WeakClosure.ConjugateSpan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.WeakClosure.Generation

/-!
# Solvable overgroups in the field-centralizer branch

Uniqueness over the original module centralizer transfers to every Sylow
of C_G(B). The weak-closure bounds at R = C_P(U) then control N_G(W₀(R,B))
and C_G(C₁(R,B)). The actual rank-one E-generation theorem for a solvable
overgroup of R forces it into M. This is the solvable-radical exclusion
used in the local-component argument of 6.1.14(5).

Source: Aschbacher–Smith, 6.1.14(5), printed p.671; E.1.13 and E.3.19.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The module centralizer in an ambient Sylow is Sylow in C_G(B). -/
theorem field_sylow_kernel (P : Sylow 2 G) (B : Subgroup G)
    (hPB : (P : Subgroup G) ≤ normalizer (B : Set G)) :
    ∃ S : Sylow 2 (centralizer (B : Set G)),
      (S : Subgroup (centralizer (B : Set G))).map (centralizer (B : Set G)).subtype =
        (P : Subgroup G) ⊓ centralizer (B : Set G) := by
  let N := normalizer (B : Set G)
  let C := (centralizer (B : Set G)).subgroupOf N
  obtain ⟨S, hS⟩ := (P.subtype hPB).exists_subgroupOf_eq_of_normal C
  let e : C ≃* centralizer (B : Set G) :=
    subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer (B : Set G))
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((S : Subgroup C).map e.toMonoidHom).map _ = _
  rw [hS]
  ext x
  constructor
  · rintro ⟨c, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨hs, s.property⟩
  · rintro ⟨hxP, hxC⟩
    let s : C := ⟨⟨x, Subgroup.centralizer_le_normalizer (B : Set G) hxC⟩, hxC⟩
    exact ⟨e s, ⟨s, hxP, rfl⟩, rfl⟩

/-- Uniqueness over the module centralizer transports to any of its Sylows. -/
theorem field_kernel_invariant_normalizer
    {κ : GroupClass.{u}} {T : Sylow 2 G} {M B : Subgroup G}
    (hE : ChapterE.Section06.HypothesisE61 κ T M B)
    (Q X : Subgroup G)
    (hQ : ∃ S : Sylow 2 (centralizer (B : Set G)),
      (S : Subgroup (centralizer (B : Set G))).map (centralizer (B : Set G)).subtype = Q)
    (hX : IsPGroup 2 X) (hXne : X ≠ ⊥)
    (hnX : normalizer (Q : Set G) ≤ normalizer (X : Set G)) :
    normalizer (X : Set G) ≤ M := by
  let Q₀ := ChapterE.Section06.sylowCentralizer (T : Subgroup G) B
  obtain ⟨R, hR⟩ := hE.sylow_centralizer
  change _ = Q₀ at hR
  obtain ⟨S, hS⟩ := hQ
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (centralizer (B : Set G)) R S
  have he : Q₀.map (MulAut.conj (c : G)).toMonoidHom = Q := by
    rw [← hR, ← hS, ← hc]
    ext x
    constructor
    · rintro ⟨y, ⟨r, hr, rfl⟩, rfl⟩
      exact ⟨c * r * c⁻¹, ⟨r, hr, rfl⟩, rfl⟩
    · rintro ⟨s, ⟨r, hr, heq⟩, rfl⟩
      refine ⟨(r : G), ⟨r, hr, rfl⟩, ?_⟩
      exact congrArg Subtype.val heq
  let f := (MulAut.conj (c : G)).toMonoidHom
  let Y := X.comap f
  have hY : IsPGroup 2 Y := hX.comap_of_injective f (MulAut.conj (c : G)).injective
  have hYne : Y ≠ ⊥ := by
    intro hz
    have hy : Y.map f = X := map_comap_eq_self_of_surjective (MulAut.conj (c : G)).surjective X
    rw [hz, Subgroup.map_bot] at hy
    exact hXne hy.symm
  have hnY : normalizer (Q₀ : Set G) ≤ normalizer (Y : Set G) := by
    have hq : (normalizer (Q₀ : Set G)).map f = normalizer (Q : Set G) := by
      rw [map_equiv_normalizer_eq, he]
    have hh := map_le_iff_le_comap.mp (hq.le.trans hnX)
    exact fun x hx => le_normalizer_comap f (hh hx)
  have hNY : normalizer (Y : Set G) ≤ M :=
    normalizer_le_of_unique_maximalTwoLocal hE.unique hY hYne (inf_le_right.trans hnY)
  have hh := map_mono (f := f) hNY
  rw [map_equiv_normalizer_eq, map_comap_eq_self_of_surjective
    (MulAut.conj (c : G)).surjective] at hh
  exact hh.trans (le_of_eq (mem_normalizer_iff_map_conj_eq.mp
    (M.le_normalizer (hE.centralizer_le c.property))))

/-- The weak bounds at the field-centralizer Sylow control solvable
subgroups containing it, the radical-exclusion step of 6.1.14(5). -/
theorem field_solvable_overgroup_le
    {κ : GroupClass.{u}} {T : Sylow 2 G} {M B R Q X : Subgroup G}
    [IsElementaryAbelian 2 B] [Group.IsSolvable X]
    (hE : ChapterE.Section06.HypothesisE61 κ T M B)
    (hQ : ∃ S : Sylow 2 (centralizer (B : Set G)),
      (S : Subgroup (centralizer (B : Set G))).map (centralizer (B : Set G)).subtype = Q)
    (hBR : B ≤ R) (hQR : Q ≤ R)
    (hR : IsPGroup 2 R) (hweak : W B R 0 ≤ Q)
    (hone : W B R 1 ≤ centralizer (B : Set G))
    (hs : (1 : ℕ∞) < ChapterE.globalS B)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = R) : X ≤ M := by
  have hN : normalizer (W B R 0 : Set G) ≤ M := by
    apply field_kernel_invariant_normalizer hE Q _ hQ
      (hR.to_le (W_le _ _ _))
    · intro he
      exact hE.nontrivial (bot_unique ((self_le_W_zero hBR).trans he.le))
    · change normalizer (Q : Set G) ≤ normalizer (ChapterE.indexedWeakClosure B R 0 : Set G)
      rw [← ChapterE.weakClosure_eq_of_le_of_closure_le B Q R 0 hQR hweak]
      exact ChapterE.normalizer_le_weakClosure_normalizer B Q 0
  have hC : centralizer (C B R 1 : Set G) ≤ M := by
    apply (centralizer_le (show B ≤ C B R 1 from ?_)).trans hE.centralizer_le
    exact le_inf hBR (le_centralizer_iff.mp hone)
  have hh := ChapterE.RankOneWeakClosure.generation_of_isEGenerated
    (V := B) S (ChapterE.isEGenerated_one_of_solvable S) hs
  rw [hS] at hh
  rw [hh]
  exact sup_le (inf_le_right.trans hC) (inf_le_right.trans hN)
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
