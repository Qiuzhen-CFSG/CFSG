module
public import CFSG.Quasithin.Chapter13.Section07.sourceL1CubicQuotient
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.LocalExclusion
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.Theta
public import Theory.GroupTheory.PrimeOrderClosure
public import Theory.GroupTheory.PResidual.NormalSubgroup.TwoGroupKernel
public import Theory.GroupTheory.PResidual.CommutatorImage
public import Theory.Quasithin.CoprimeRank
public import Theory.Alternating.PrimeRank
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowGeometry

/-!
# Local rank and normalizer escape in the original noncontained branch

The actual point residual maps onto the four-letter A₄ through the LT
2-core. This gives its exact three-part and three-rank. The Sylow flag
marks its image together with the actual image of T; the canonical A₄
commutator calculation and two-perfect lifting prove L₁=[L₁,T].
The genuine earlier theta identity then gives three-rank one for H∩M,
so an H-normalizer with larger three-rank escapes M.

Source: Aschbacher–Smith, 13.7.3(9), 13.7.9(2), and the first paragraph
of 13.7.19, printed pp.936, 940–941, and 944–945.
-/

public section
open Subgroup BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion NaturalAction
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem source_local_threePart
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    3 ^ (Nat.card (sourceOne L T V₁)).factorization 3 = 3 := by
  obtain ⟨f,hf,hker⟩ := source_local_residual_surjection d h hU hV
  have hp : IsPGroup 2 f.ker := by
    rw [hker]
    exact (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).comap_subtype
  have hc : Nat.card ((⊤ : Subgroup (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁).map f) = 12 := by
    rw [←MonoidHom.range_eq_map, f.range_eq_top_of_surjective hf, card_top,
      nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hh := threePart_map_of_twoGroup_kernel f hp ⊤
  rw [hc, card_top, PlusAction.source_local_residual_eq d h] at hh
  have h12 : (12 : ℕ).factorization 3 = 1 := by
    have he : 12 = 2 ^ 2 * 3 := by decide
    rw [he, Nat.factorization_mul (by decide) (by decide),
      Nat.factorization_pow, Finsupp.add_apply]
    simp [Nat.Prime.factorization, Nat.prime_two, Nat.prime_three]
  rw [h12] at hh
  norm_num at hh
  exact hh.symm

theorem source_local_threeRank
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    primeRank 3 (sourceOne L T V₁) = 1 := by
  obtain ⟨f,hf,hker⟩ := source_local_residual_surjection d h hU hV
  have hp : IsPGroup 2 f.ker := by
    rw [hker]
    exact (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).comap_subtype
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hh := primeRank_eq_of_surjective_of_coprime 3 f hf (by
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n)
  rw [PlusAction.source_local_residual_eq d h,
    GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 4 3 (by decide) (by decide)] at hh
  exact hh

theorem source_overlap_threeRank
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    primeRank 3 (H ⊓ M : Subgroup G) = 1 := by
  rw [←primeRank_primeOrderClosure 3 (H ⊓ M : Subgroup G),
    ModelExclusions.theta_intersection d h1221 hH]
  exact source_local_threeRank d h hU hV

theorem source_normalizer_escape_of_threeRank
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (R₁ : Subgroup G)
    (hr : 1 < primeRank 3 (H ⊓ normalizer (R₁ : Set G) : Subgroup G)) :
    ¬ H ⊓ normalizer (R₁ : Set G) ≤ M := by
  intro hm
  have hh := primeRank_mono 3 (le_inf inf_le_left hm)
  rw [source_overlap_threeRank d h1221 hH h hU hV] at hh
  exact (Nat.not_lt_of_ge hh) hr

theorem source_local_eq_commutator_sylow
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    sourceOne L T V₁ = ⁅sourceOne L T V₁, (T : Subgroup G)⁆ := by
  let X := L ⊔ (T : Subgroup G)
  let J := sourceOne L T V₁
  let f := permutation d
  let U := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).mapSurjective
    (nonabelian_permutation_surjective d h hU hV)
  have hUimage : (U : Subgroup S) = ((T : Subgroup G).subgroupOf X).map f := by
    rw [Sylow.coe_mapSurjective, Sylow.coe_subtype]
  obtain ⟨g,hg,hflag⟩ := sylow_flag U
  have hline : image d V₁ = move g canonicalLine := by
    apply (hflag (image d V₁) ?_).1
    · exact image_dim d V₁ (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) 1 d.line_card
    · intro x hx
      exact (mem_stabilizer_iff_map _ _).mp (image_stable d V₁ d.line_stable (hUimage ▸ hx))
  have hJX : J ≤ X := (one_le L T V₁).trans inf_le_left
  have hJimage : (J.subgroupOf X).map f = K.map (MulAut.conj g).toMonoidHom := by
    dsimp only [J, X, f]
    rw [←PlusAction.source_local_residual_eq d h, source_local_residual_image d h hU hV]
    have hs : Representation.BinaryOffender.subspaceStabilizer
        (naturalRepresentation (Fin 6)) (image d V₁) = H1.map (MulAut.conj g).toMonoidHom := by
      change flagStabilizer (image d V₁) = _
      rw [hline, flagStabilizer_move, flagStabilizer_line]
    calc
      _ = (pResidual 2 (H1.map (MulAut.conj g).toMonoidHom)).map
          (H1.map (MulAut.conj g).toMonoidHom).subtype :=
        congrArg (fun A : Subgroup S => (pResidual 2 A).map A.subtype) hs
      _ = _ := by rw [←map_embedded_pResidual, residual_H1]
  have hc : ⁅K, (canonicalSylow : Subgroup S)⁆ = K := by
    apply commutator_eq_K_of_between K _ le_rfl K_le_H1
    · rw [canonicalSylow_coe]
      exact le_inf (D0_le_L1.trans inf_le_left) (D0_le_L2.trans inf_le_left)
    · rw [canonicalSylow_coe]
      exact inf_le_left
  have hi : (J.subgroupOf X).map f =
      ⁅(J.subgroupOf X).map f, ((T : Subgroup G).subgroupOf X).map f⁆ := by
    rw [hJimage, ←hUimage, ←hg, ←canonicalSylow_coe, ←map_commutator, hc]
  have hp : IsPPerfect 2 (J.subgroupOf X) :=
    (residual_isPPerfect (parabolic L T V₁)).of_surjective
      (subgroupOfEquivOfLe hJX).symm.toMonoidHom (subgroupOfEquivOfLe hJX).symm.surjective
  have hn : (T : Subgroup G).subgroupOf X ≤ normalizer (J.subgroupOf X : Set X) := by
    rw [←subgroupOf_normalizer_eq hJX]
    exact comap_mono (T_normalizes_one L T V₁ d.line_stable)
  have hk : IsPGroup 2 f.ker := by
    rw [nonabelian_permutation_kernel d h hU hV]
    exact pCore_isPGroup
  have he := eq_commutator_of_isPPerfect_of_map_eq (J.subgroupOf X)
    ((T : Subgroup G).subgroupOf X) hp hn f hk hi
  have he' := congrArg (map X.subtype) he
  rwa [map_commutator, map_subgroupOf_eq_of_le hJX,
    map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)] at he'

/-- The literal R₁=O₂(L₁T) normalizer escapes M when its three-rank exceeds one. -/
theorem source_local_normalizer_escape
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hr : 1 < primeRank 3 (H ⊓ normalizer
      ((sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) : Subgroup G)) :
    ¬ H ⊓ normalizer ((sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤ M :=
  source_normalizer_escape_of_threeRank d h1221 hH h hU hV _ hr

/-- Actual F.9 source application supplying the local inputs of 13.7.19. -/
theorem source_13_7_19_local_inputs
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    F.L₁ = ⁅F.L₁, (T : Subgroup G)⁆ ∧
    3 ^ (Nat.card F.L₁).factorization 3 = 3 ∧
    primeRank 3 (H ⊓ M : Subgroup G) = 1 ∧
    (1 < primeRank 3 (H ⊓ normalizer
        ((F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) : Subgroup G) →
      ¬ H ⊓ normalizer ((F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤ M) := by
  dsimp only
  rw [PlusAction.source_local_residual_eq d h]
  exact ⟨source_local_eq_commutator_sylow d h hU hV,
    source_local_threePart d h hU hV,
    source_overlap_threeRank d h1221 hH h hU hV,
    source_local_normalizer_escape d h1221 hH h hU hV⟩

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
