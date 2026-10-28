module
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingSeven.CoreSplit
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingSevenCoordinates
public import Theory.Representation.BinaryPermutation.SevenMarkedAction

/-!
# Full-cover fixers of the ordinary A₇ block module

An automorphism fixing U(L) has displacement in C_L(U(L)) = O₂(L).
The cohomology theorem on the actual block cover makes it inner by an
element of U(L), retaining a possible central factor in the two-core.
The ambient factorization and module coordinates at a prescribed quotient
marking let consumers use the same permutation action throughout.

Source: Aschbacher--Smith C.1.13(c), applied in 15.1.25(5), printed p.1102.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L]

theorem IsAlternatingBlock.seven_automorphism_inner_of_fixing_module
    (h : IsAlternatingBlock L 7) (α : MulAut L)
    (hfix : ∀ u ∈ blockU L, α u = u) :
    ∃ u : blockU L, ∀ x, α x = (u : L)⁻¹ * x * u := by
  apply h.seven_automorphism_inner_of_core_displacement α _ hfix
  intro x
  have hd : (α x)⁻¹ * x ∈ centralizer (blockU L : Set L) := by
    intro n hn
    have hconj := hfix (x*n*x⁻¹) ((inferInstance : (blockU L).Normal).conj_mem n hn x)
    rw [map_mul,map_mul,map_inv,hfix n hn] at hconj
    calc
      n * ((α x)⁻¹ * x) = (α x)⁻¹ * (α x * n * (α x)⁻¹) * x := by group
      _ = (α x)⁻¹ * (x * n * x⁻¹) * x := by rw [hconj]
      _ = ((α x)⁻¹ * x) * n := by group
  rw [h.2.1.centralizer_blockU] at hd
  have hh := (inferInstance : (pCore 2 L).Normal).conj_mem _ ((pCore 2 L).inv_mem hd) x
  simpa only [mul_inv_rev,inv_inv,mul_inv_cancel_left] using hh

variable {G : Type*} [Group G]

theorem IsAlternatingBlock.seven_module_fixer_factorization
    {K : Subgroup G} (h : IsAlternatingBlock K 7)
    {g : G} (hg : g ∈ normalizer (K : Set G))
    (hfix : g ∈ centralizer (((blockU K).map K.subtype) : Set G)) :
    ∃ u : blockU K, ((u : K) : G) * g ∈ centralizer (K : Set G) := by
  let α := K.normalizerMonoidHom ⟨g,hg⟩
  have hf (u : K) (hu : u ∈ blockU K) : α u = u := by
    apply Subtype.ext
    change g * (u : G) * g⁻¹ = (u : G)
    rw [←hfix u (mem_map_of_mem K.subtype hu),mul_inv_cancel_right]
  obtain ⟨u,hu⟩ := h.seven_automorphism_inner_of_fixing_module α hf
  refine ⟨u,?_⟩
  intro k hk
  have he := congrArg (fun z : K => (z : G)) (hu ⟨k,hk⟩)
  change g*k*g⁻¹ = ((u : K) : G)⁻¹*k*u at he
  calc
    k * (((u : K) : G)*g) = u * (((u : K) : G)⁻¹*k*u) * g := by group
    _ = u * (g*k*g⁻¹) * g := by rw [←he]
    _ = (((u : K) : G)*g)*k := by group

end CFSG.Quasithin.ChapterC

namespace CFSG.Quasithin.ChapterC
open BinaryPermutation BinaryPermutation.SevenNormalizer BinaryPermutation.SevenMarkedAction
variable {L : Type*} [Group L]

theorem IsAlternatingBlock.seven_module_coordinates_at
    (h : IsAlternatingBlock L 7)
    (q : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7)) :
    ∃ E : blockU L ≃* Multiplicative (core (Fin 7)),
      ∀ (l : L) (u : blockU L),
        E (blockConjugate L l u) =
          coreAction (q (QuotientGroup.mk' (pCore 2 L) l)).val (E u) := by
  obtain ⟨q0,E0,f0,hq0,hE0⟩ := h.seven_automorphism_coordinates
  let a := q0.symm.trans q
  let c := permutationOfAut a
  let E := E0.trans (coreAction c)
  have ha (x : alternatingGroup (Fin 7)) : (a x).val = c * x.val * c⁻¹ := by
    exact (congrArg (fun b : MulAut (alternatingGroup (Fin 7)) => (b x).val)
      (conjugation_permutationOfAut a)).symm
  refine ⟨E,?_⟩
  intro l u
  have he0 : E0 (blockConjugate L l u) =
      coreAction (q0 (QuotientGroup.mk' (pCore 2 L) l)).val (E0 u) := by
    apply Multiplicative.toAdd.injective
    have hh := hE0 (MulAut.conj l) u
    have ha : MulAut.characteristic (blockU L) (MulAut.conj l) u = blockConjugate L l u := by
      apply Subtype.ext
      rfl
    rw [ha,hq0] at hh
    exact hh
  have heq : (q (QuotientGroup.mk' (pCore 2 L) l)).val =
      c * (q0 (QuotientGroup.mk' (pCore 2 L) l)).val * c⁻¹ := by
    simpa only [a,MulEquiv.trans_apply,q0.symm_apply_apply] using
      ha (q0 (QuotientGroup.mk' (pCore 2 L) l))
  change coreAction c (E0 (blockConjugate L l u)) =
    coreAction (q (QuotientGroup.mk' (pCore 2 L) l)).val (coreAction c (E0 u))
  rw [he0,heq,map_mul,map_mul,map_inv]
  simp only [MulAut.mul_apply,MulAut.inv_apply,MulEquiv.symm_apply_apply]

end CFSG.Quasithin.ChapterC
