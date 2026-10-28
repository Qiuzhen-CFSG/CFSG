module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.ExceptionalMarking
public import Theory.GroupTheory.ElementaryThompsonNormalizer

/-!
# Thompson normalizer generation for the original exceptional four-space

The faithful A₇ action identifies the images of J(T) and Baum(T) with the
unique best offender in the supplied Sylow subgroup. Its normalizer and
the pointwise fixer of the Sylow-fixed line generate A₇. Recovering J(T)
from the full preimage of its image lifts that equality through the
original action kernel, which is required to lie in T.

Source: Aschbacher–Smith B.4.2(7) and C.1.24, applied in 5.1.13,
printed pp.90–91,130–131,637.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
variable {G : Type*} [Group G] [Finite G]

/-- The four-dimensional right action generates the original group from its
Thompson normalizer and the centralizer of its Sylow-fixed line. -/
theorem exceptional_thompson_normalizer_generation
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* alternatingGroup (Fin 7)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (hd : Module.finrank (ZMod 2) (Additive U) = 4)
    (T : Sylow 2 G) (hUT : U ≤ T) (hkerT : q.ker ≤ T)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ q.ker) :
    normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ⊔
      centralizer (U ⊓ centralizer ((T : Subgroup G) : Set G) : Set G) = ⊤ := by
  let ρ := NormalElementaryQuotient.representation U q hq hk
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let P := T.mapSurjective (f := q) hq
  obtain ⟨A,hAP,hA,hJA,_⟩ := exceptional_thompson_baumann_images U q hq hk hd T hUT hJ
  obtain ⟨B,hBP,hB,hu,hgen⟩ :=
    Representation.BinaryAlternatingSevenControl.exists_unique_best_and_generation ρ
      (NormalElementaryQuotient.representation_injective U q hq hk) hd P
  have hAB : A = B := hu A hAP hA
  have hN : normalizer (J : Set G) = (normalizer (B : Set (alternatingGroup (Fin 7)))).comap q := by
    rw [normalizer_maxJ_eq_comap_of_ker_le (T : Subgroup G) q hkerT,hJA,hAB]
  have hC : centralizer (U ⊓ centralizer ((T : Subgroup G) : Set G) : Set G) =
      (subspaceKernel ρ (fixedSpace ρ (P : Subgroup _)) ⊤).comap q := by
    ext g
    change g ∈ centralizer (U ⊓ centralizer ((T : Subgroup G) : Set G) : Set G) ↔
      q g ∈ subspaceKernel ρ (fixedSpace ρ (P : Subgroup _)) ⊤
    constructor
    · intro hg
      refine ⟨mem_top _,?_⟩
      intro v hv
      have hvC := (NormalElementaryQuotient.mem_fixedSpace_image U q hq hk
        (T : Subgroup G) v).mp hv
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [NormalElementaryQuotient.representation_apply,←hg v.toMul ⟨v.toMul.property,hvC⟩,
        mul_inv_cancel_right]
    · intro hg u hu
      let v : Additive U := Additive.ofMul ⟨u,hu.1⟩
      have hv : v ∈ fixedSpace ρ (P : Subgroup _) :=
        (NormalElementaryQuotient.mem_fixedSpace_image U q hq hk (T : Subgroup G) v).mpr hu.2
      have he := congrArg (fun v : Additive U => (v.toMul : G)) (hg.2 v hv)
      rw [NormalElementaryQuotient.representation_apply] at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
  rw [hN,hC]
  apply top_unique
  let E := (normalizer (B : Set (alternatingGroup (Fin 7)))).comap q ⊔
    (subspaceKernel ρ (fixedSpace ρ (P : Subgroup _)) ⊤).comap q
  have hmap : E.map q = ⊤ := by
    rw [show E = _ ⊔ _ from rfl,Subgroup.map_sup,
      map_comap_eq_self_of_surjective hq,map_comap_eq_self_of_surjective hq,hgen]
  have hker : q.ker ≤ E := (ker_le_comap q _).trans le_sup_left
  have hh := congrArg (Subgroup.comap q) hmap
  rw [comap_map_eq,sup_eq_left.mpr hker,comap_top] at hh
  exact hh.ge
end CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
