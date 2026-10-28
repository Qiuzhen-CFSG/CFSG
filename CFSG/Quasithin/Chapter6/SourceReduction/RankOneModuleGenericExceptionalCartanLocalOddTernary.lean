module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalNormalJankoExclusion
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityOddModels
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison

/-!
# The original residual in normal odd ternary Cartan containers

Every full-Sylow overgroup in odd PSL₃ or PSU₃ has at most one
C-component: two distinct components would give a section of two-rank
at least four, while all sections of the actual odd ternary carriers
have two-rank at most three. Uniqueness lifts through the central
projective maps and through the containing component's original two-core.
Consequently the original full Sylow fixes the original seed, and its
entire Sylow orbit is just the literal residual O²(H).

The final theorem applies this to the original normal-container sieve,
including SL₃ and SU₃ with their central kernels retained. All preceding
exclusions remain present. This removes the moved-seed branch in these
four families; it does not exclude their normal residual embeddings or
construct the final escaping inverted cubic.

Source: Aschbacher--Smith A.3.12(9), 1.2.8 and 5.1.12--13,
printed pp.47--48,506--507,635--637 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

private theorem odd_ternary_unique {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL Q 3 p ∨ ClassicalGroup.IsPSU Q 3 p ∨
      IsSL Q 3 p ∨ IsSU Q 3 p) : SylowOvergroupComponentUnique Q := by
  rcases hm with hm | hm | hm | hm
  · exact Chapter1.Section02.MovedMaximality.odd_ternary_sylow_overgroup_component_unique
      hp ho false hm
  · exact Chapter1.Section02.MovedMaximality.odd_ternary_sylow_overgroup_component_unique
      hp ho true hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let f := (Matrix.PSL3.projection F).comp e.toMonoidHom
    have hf : Function.Surjective f := (Matrix.PSL3.projection_surjective F).comp e.surjective
    have hk : f.ker ≤ center Q := by
      intro x hx
      have hx' : e x ∈ center SL(3,F) := by
        rwa [←Matrix.PSL3.projection_ker]
      exact mem_center_iff.mpr (fun y => e.injective (by
        simpa only [map_mul,MulEquiv.coe_toMonoidHom] using mem_center_iff.mp hx' (e y)))
    let : Group.IsSolvable f.ker := Group.isSolvable_of_comm (fun x y =>
      Subtype.ext (mem_center_iff.mp (hk y.property) x))
    exact SylowOvergroupComponentUnique.of_surjective f hf
      (Chapter1.Section02.MovedMaximality.odd_ternary_sylow_overgroup_component_unique
        hp ho false ⟨F,inferInstance,inferInstance,hF,⟨MulEquiv.refl _⟩⟩)
  · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
    let f := J.specialToProjective.comp e.toMonoidHom
    have hf : Function.Surjective f := J.specialToProjective_surjective.comp e.surjective
    let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective f hf
    have hk : f.ker ≤ center Q := by
      intro x hx
      have hx' := J.specialToProjective_ker_le_center hx
      exact mem_center_iff.mpr (fun y => e.injective (by
        simpa only [map_mul,MulEquiv.coe_toMonoidHom] using mem_center_iff.mp hx' (e y)))
    let : Group.IsSolvable f.ker := Group.isSolvable_of_comm (fun x y =>
      Subtype.ext (mem_center_iff.mp (hk y.property) x))
    exact SylowOvergroupComponentUnique.of_surjective f hf
      (Chapter1.Section02.MovedMaximality.odd_ternary_sylow_overgroup_component_unique
        hp ho true ⟨F,inferInstance,inferInstance,J,hF,hc,⟨MulEquiv.refl _⟩⟩)

private theorem seed_eq_residual_of_normal_unique_container
    {T : Sylow 2 G} {K H Y : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hHY : H ≤ Y)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (C : Subgroup Y) [C.Normal] (hKC : K ≤ C.map Y.subtype)
    (hu : SylowOvergroupComponentUnique (C ⧸ pCore 2 C)) : K = residual H := by
  have hKY : K ≤ Y := hKC.trans (map_subtype_le C)
  have hTY := hTH.trans hHY
  let S := T.subtype hTY
  have hlocal : K.subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTY hKY).mp ⟨hKY,hK⟩
  have hKC' : K.subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hKC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  let : Group.IsNilpotent (pCore 2 C) := pCore_isNilpotent
  let : Group.IsSolvable (QuotientGroup.mk' (pCore 2 C)).ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  have huC := hu.of_surjective (QuotientGroup.mk' (pCore 2 C))
    (QuotientGroup.mk'_surjective _)
  have hn := SylowOvergroupComponentUnique.normalizes_local_component S hlocal.1
    (inferInstance : C.Normal).isSubnormal hKC' le_normalizer_of_normal huC
  have hnG : (T : Subgroup G) ≤ normalizer (K : Set G) := by
    rw [←subgroupOf_normalizer_eq hKY] at hn
    exact fun t ht => hn (show (⟨t,hTY ht⟩ : Y) ∈ S from ht)
  exact (le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hnG)
    (le_componentOrbit K _)).symm.trans horbit

/-- In every normal odd ternary containing row, the original seed is the
whole original two-residual. No chosen-module or field-degree assumption is added. -/
theorem seed_eq_residual_of_normal_odd_ternary_container
    {T : Sylow 2 G} {K H Y : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hHY : H ≤ Y)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (C : Subgroup Y) [C.Normal] (hKC : K ≤ C.map Y.subtype)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
      ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
      IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p) :
    K = residual H :=
  seed_eq_residual_of_normal_unique_container hTH hHY hK horbit C hKC
    (odd_ternary_unique hp ho hm)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
/-- The original normal-container sieve retains every preceding exclusion
and identifies the whole residual in each of the four odd ternary families. -/
theorem localCartan_escape_seed_oddTernary_residual_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        C.Normal ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
            ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
            IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p) →
          K = residual H) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ⟩ :=
    localCartan_escape_seed_noJanko_reduction h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,?_⟩
  let := hCn
  intro p hp ho hm
  exact LocalSieve.seed_eq_residual_of_normal_odd_ternary_container
    hH.1.1.2 hY.2 hKL hR C hKC hp ho hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
