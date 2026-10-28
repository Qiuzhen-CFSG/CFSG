module
public import Theory.GroupAction.ElementaryEightPointResidual.KernelContainment
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.UniqueLocalResidualKernel
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.PResidual.PrimeToPerfect
public import Theory.GroupTheory.ElementaryEightParabolicRecognition
public import Theory.GroupTheory.ConjugateSpanNormalizer

/-!
# Normalizer control from a full elementary cover

Transport the full covering kernel into the ambient group and use the
index-two Sylow comparison to retain it inside the original factor normalizer.
The resulting Sylow factorization transfers normalization of a prime-to-five
residual from the index-two subgroup to the entire Sylow subgroup. Uniqueness
among maximal two-local overgroups then controls its full normalizer through
a nontrivial characteristic two-core.

Finally, a full elementary action recovers its module as the orbit span of
any nontrivial seed. Normalizing the seed and covering actor preserves that
module. These are the normalizer steps of Aschbacher–Smith 14.7.6,
printed p.1045, refs/quasithin.pdf; all kernels and ambient maps are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.GroupAction.ElementaryEightPointResidual
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual two-core of the normal covering component lies in the
original index-two factor normalizer; its Sylow intersection supplies the
other coset of the compatible ambient Sylow. -/
theorem common_eight_component_core_containment
    (S TA : Sylow 2 G) (R C : Subgroup G) [IsElementaryAbelian 2 C]
    (hRS : R ≤ S) (hi : R.relIndex (S : Subgroup G) = 2)
    (hRTA : R ≤ TA) (hTAC : (TA : Subgroup G) ≤ normalizer (C : Set G))
    (hc : Nat.card C = 8)
    (D : Subgroup (normalizer (C : Set G))) [D.Normal]
    (hD : D.map C.normalizerMonoidHom = ⊤)
    (hk : (C.normalizerMonoidHom.comp D.subtype).ker = pCore 2 D)
    (B : Subgroup (MulAut C)) (hB : Nat.card B = 12)
    (himage : conjugationImage (R ⊓ D.map (normalizer (C : Set G)).subtype) C ≤ B) :
    let DA := D.map (normalizer (C : Set G)).subtype
    DA.pCoreIn 2 ≤ R ∧ R ⊔ ((TA : Subgroup G) ⊓ DA) = (TA : Subgroup G) := by
  let N := normalizer (C : Set G)
  let P := TA.subtype hTAC
  let R0 := R.subgroupOf N
  have hRN : R ≤ N := hRTA.trans hTAC
  have hP : (P : Subgroup N).map N.subtype = (TA : Subgroup G) :=
    map_subgroupOf_eq_of_le hTAC
  have hRP : R0 ≤ P := fun _ hx => hRTA hx
  have hiA : R.relIndex (TA : Subgroup G) = 2 := by
    have hs := relIndex_mul_relIndex (⊥ : Subgroup G) R (S : Subgroup G) bot_le hRS
    have ht := relIndex_mul_relIndex (⊥ : Subgroup G) R (TA : Subgroup G) bot_le hRTA
    rw [relIndex_bot_left,relIndex_bot_left,hi] at hs
    rw [relIndex_bot_left,relIndex_bot_left] at ht
    have he : Nat.card S = Nat.card TA := by rw [S.card_eq_multiplicity,TA.card_eq_multiplicity]
    rw [he] at hs
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (ht.trans hs.symm)
  have hiP : R0.relIndex (P : Subgroup N) = 2 := by
    change (R.subgroupOf N).relIndex ((TA : Subgroup G).subgroupOf N) = 2
    rw [relIndex_subgroupOf hTAC,hiA]
  have him : (R0 ⊓ D).map C.normalizerMonoidHom ≤ B := by
    have he : (R0 ⊓ D).map C.normalizerMonoidHom =
        conjugationImage (R ⊓ D.map N.subtype) C := by
      rw [conjugationImage_eq_map_of_le _ _ (inf_le_left.trans hRN)]
      change _ = ((R ⊓ D.map N.subtype).comap N.subtype).map _
      rw [comap_inf,comap_map_eq_self_of_injective N.subtype_injective]
      rfl
    exact he.symm ▸ himage
  obtain ⟨hcore,hgen⟩ := normal_cover_kernel_le_of_index_two hc C.normalizerMonoidHom D hD hk
    P R0 hRP hiP B hB him
  have hcG := map_mono (f := N.subtype) hcore
  rw [map_pCoreIn_of_injective 2 D N.subtype N.subtype_injective,
    map_subgroupOf_eq_of_le hRN] at hcG
  have hgG := congrArg (Subgroup.map N.subtype) hgen
  rw [Subgroup.map_sup,map_inf _ _ N.subtype N.subtype_injective,hP,
    map_subgroupOf_eq_of_le hRN] at hgG
  exact ⟨hcG,hgG⟩

/-- Retaining the full two-core makes the original five-residual normal
under both the component and the compatible Sylow. -/
theorem five_residual_normalized_of_component_core_containment
    (D R A : Subgroup G) (TA : Sylow 2 G)
    (hcore : D.pCoreIn 2 ≤ R)
    (hgen : R ⊔ ((TA : Subgroup G) ⊓ D) = (TA : Subgroup G))
    (hR : R ≤ normalizer ((primeToResidual 5 A).map A.subtype : Set G))
    (hcomm : ⁅D,(primeToResidual 5 A).map A.subtype⁆ ≤ D.pCoreIn 2) :
    D ≤ normalizer ((primeToResidual 5 A).map A.subtype : Set G) ∧
      (TA : Subgroup G) ≤ normalizer ((primeToResidual 5 A).map A.subtype : Set G) := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let K := (primeToResidual 5 A).map A.subtype
  have hp : IsPPerfect 2 K :=
    (isPPerfect_primeToResidual (G := A) 5 2 (by decide)).of_surjective
      ((primeToResidual 5 A).equivMapOfInjective A.subtype A.subtype_injective).toMonoidHom
      ((primeToResidual 5 A).equivMapOfInjective A.subtype A.subtype_injective).surjective
  have he : (pResidual 2 K).map K.subtype = K := by
    rw [(pResidual_eq_top_iff 2 K).mpr hp,←MonoidHom.range_eq_map,range_subtype]
  have hDcore : D ≤ normalizer (D.pCoreIn 2 : Set G) :=
    D.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D))
  have hn := normalizes_residual_of_commutator_le_two D R K (D.pCoreIn 2)
    hR hcore (isPGroup_pCoreIn 2 D) hDcore (by rwa [he])
  rw [he] at hn
  exact ⟨hn,hgen ▸ sup_le hR (inf_le_right.trans hn)⟩

/-- Uniqueness over D T_A controls the full normalizer of the original
other five-residual, via its nontrivial characteristic two-core. -/
theorem five_residual_normalizer_le_component_normalizer
    (D K : Subgroup G) (TA : Sylow 2 G)
    (hne : K.pCoreIn 2 ≠ ⊥)
    (hDK : D ≤ normalizer (K : Set G))
    (hTK : (TA : Subgroup G) ≤ normalizer (K : Set G))
    (hu : ∀ M : Subgroup G, IsMaximalTwoLocal M → D ⊔ (TA : Subgroup G) ≤ M →
      M = normalizer (D : Set G)) :
    normalizer (K : Set G) ≤ normalizer (D : Set G) := by
  have hn := normalizer_le_normalizer_characteristic_image K (pCore 2 K)
  exact hn.trans (normalizer_le_of_unique_maximalTwoLocal hu (isPGroup_pCoreIn 2 K) hne
    ((sup_le hDK hTK).trans hn))

end Theory.GroupAction.ElementaryEightPointResidual

namespace Theory.GroupAction.ElementaryEightPointResidual
/-- A full elementary action recovers the group from any nontrivial seed;
normalizing that seed and its covering actor therefore normalizes the group. -/
theorem normalizes_common_space_of_normalizes_point_cover
    {G : Type*} [Group G] (C Z : Subgroup G) [IsElementaryAbelian 2 C]
    (hZC : Z ≤ C) (hZ : Z ≠ ⊥)
    (D : Subgroup (normalizer (C : Set G))) (hD : D.map C.normalizerMonoidHom = ⊤) :
    normalizer (Z : Set G) ⊓ normalizer (D.map (normalizer (C : Set G)).subtype : Set G) ≤
      normalizer (C : Set G) := by
  let DA := D.map (normalizer (C : Set G)).subtype
  have hDAC : DA ≤ normalizer (C : Set G) := map_subtype_le _
  have he : conjugateSpanBy Z DA = C := by
    apply le_antisymm (conjugateSpanBy_le hZC hDAC)
    obtain ⟨z,hz,hz1⟩ := Z.bot_or_exists_ne_one.resolve_left hZ
    let zC : C := ⟨z,hZC hz⟩
    have hzC : zC ≠ 1 := fun he => hz1 (congrArg Subtype.val he)
    intro x hx
    by_cases hx1 : x = 1
    · exact hx1 ▸ one_mem _
    obtain ⟨a,ha⟩ := ElementaryEightParabolic.automorphism_transitive zC (⟨x,hx⟩ : C)
      hzC (fun he => hx1 (congrArg Subtype.val he))
    obtain ⟨d,hd,hda⟩ := hD.ge (mem_top a)
    exact subset_closure ⟨(d : G),mem_map_of_mem _ hd,z,hz,
      congrArg Subtype.val (hda.symm ▸ ha)⟩
  have hh := normalizes_conjugateSpanBy Z DA _ inf_le_left inf_le_right
  rwa [he] at hh

end Theory.GroupAction.ElementaryEightPointResidual
