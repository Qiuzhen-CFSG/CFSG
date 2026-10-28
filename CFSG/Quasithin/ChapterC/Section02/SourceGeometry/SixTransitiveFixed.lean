module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SixTransitiveMovedFixed
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.MovedNormalizerAction

/-!
# Natural A₆ fixed vectors on the actual star module

A vector fixed by a transitive two-perfect subgroup in the marked natural
A₆ moved section is fixed by the whole star component. The literal
quotient-action formula then makes the original group element centralize L.
The theorem keeps both nonsplit module attachments and the original maps.

Source: Aschbacher–Smith B.5.1,C.2.7 and15.3.21, pp.99–103,145–147,1127.
-/
set_option backward.isDefEq.respectTransparency false
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G]

/-- Fixed-vector detection on the literal star module centralizes the
original component, retaining its actual quotient and conjugation maps. -/
theorem star_alternatingSix_fixed_centralizes
    (L R : Subgroup G) :
    let C := starImage L R L
    let J := offenderSubgroup (starRepresentation L R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation L R).comp J.subtype) (C.subgroupOf J))
      (e : ActionEquiv (s.action.comp (C.subgroupOf J).subtype) (alternatingNatural 6))
      (A : Subgroup (alternatingGroup (Fin 6))) (_hA : IsPPerfect 2 A)
      (_ht : ∀ i j : Fin 6, ∃ g : A, g.val.val i = j)
      (w : Additive (starV L R))
      (_hw : ∀ a : A, ((starRepresentation L R).comp J.subtype)
        (e.groupEquiv.symm a) w = w),
      ((w.toMul : (L ⊔ R : Subgroup G)) : G) ∈ centralizer (L : Set G) := by
  intro C J hCJ s e A hA ht w hw
  have hfix := s.alternatingSix_fixed_of_transitive e A hA ht w hw
  intro l hl
  let lN : (L ⊔ R : Subgroup G) := ⟨l,(show L ≤ L ⊔ R from le_sup_left) hl⟩
  let q := QuotientGroup.mk' (starKernel L R)
  have hlC : q lN ∈ C := mem_map_of_mem q hl
  let z : C.subgroupOf J := ⟨⟨q lN,hCJ hlC⟩,hlC⟩
  have he := hfix z
  change starRepresentation L R (q lN) w = w at he
  have he' := congrArg (fun v : Additive (starV L R) =>
    (v.toMul : (L ⊔ R : Subgroup G))) he
  change ((NormalElementaryQuotient.representation (starV L R)
    (QuotientGroup.mk' (starKernel L R)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) ((QuotientGroup.mk' (starKernel L R)) lN) w).toMul :
        (L ⊔ R : Subgroup G)) = w.toMul at he'
  rw [NormalElementaryQuotient.representation_apply] at he'
  have hg := congrArg Subtype.val he'
  change l * ((w.toMul : (L ⊔ R : Subgroup G)) : G) * l⁻¹ =
    ((w.toMul : (L ⊔ R : Subgroup G)) : G) at hg
  exact mul_inv_eq_iff_eq_mul.mp hg
end CFSG.Quasithin.ChapterC.C27Source
