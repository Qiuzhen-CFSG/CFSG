module

public import CFSG.Quasithin.Chapter13.Section07.CoveredElimination
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Kernel

/-!
# The genuine symmetric quotient in the nonabelian branch

The original action contains A₆ and the transposition supplied by V_H,
so its image is all S₆. The now-proved ordinary quotient L/O₂(L) makes
the kernel a two-group. The original Sylow centralizer equality then
identifies that kernel with O₂(LT). The resulting quotient equivalence
retains its exact formula on every original LT element.

This is the ambient barred-group input used in the two-conjugate-span
calculation of13.7.10. No symmetric quotient or kernel equality is assumed.
Source: Aschbacher–Smith,13.7.3(4),(7),13.7.9–10, pp.936,940–941.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion NaturalAction
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionQuotients.FiveSeed
open Section08.TransvectionQuotients.FiveSeed.BarMarking
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem nonabelian_permutation_surjective
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    Function.Surjective (permutation d) := by
  apply MonoidHom.range_eq_top.mp
  have hd : (permutation d).range.index ∣ 2 :=
    by simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le (alternating_le_range d)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hi | hi
  · exact index_eq_one.mp hi
  have he := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi
  obtain ⟨t,ht,hA,_⟩ := nonabelian_transposition_images d h hU hV
  have hm : t ∈ ((Section08.Source.VH H V).subgroupOf (L ⊔ (T : Subgroup G))).map
      (permutation d) := hA.symm ▸ mem_zpowers t
  have hr : t ∈ (permutation d).range := map_le_range _ _ hm
  rw [he] at hr
  have hs := Equiv.Perm.mem_alternatingGroup.mp hr
  rw [ht.sign_eq] at hs
  norm_num at hs

theorem nonabelian_permutation_kernel
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    (permutation d).ker = pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
  obtain ⟨e⟩ := nonabelian_source_ordinary d h hU hV
  let α := d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L))
  have hα : Function.Surjective α := d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : (permutation d).ker = actorKernel (L ⊔ (T : Subgroup G)) V := by
    ext x
    exact permutation_eq_one_iff d x
  have hCT := centralizer_le_sylow_of_natural_action L V T d.normalizes_L
    (permutation d) hk α hα (permutation_L d) e
  ext x
  constructor
  · intro hx
    have hc : x.val ∈ centralizer (V : Set G) := (permutation_eq_one_iff d x).mp hx
    have ht : x.val ∈ (T : Subgroup G) := hCT ⟨hc,x.property⟩
    have hm : x.val ∈ (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 :=
      h.sylow_centralizer ▸ ⟨ht,hc⟩
    obtain ⟨y,hy,he⟩ := hm
    exact (Subtype.ext he : y=x) ▸ hy
  · intro hx
    apply (permutation_eq_one_iff d x).mpr
    exact d.chosen.core_centralizes (mem_map_of_mem _ hx)

noncomputable def nonabelian_quotient_equiv
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    ((L ⊔ (T : Subgroup G) : Subgroup G) ⧸ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) ≃*
      Equiv.Perm (Fin 6) :=
  (QuotientGroup.quotientMulEquivOfEq (nonabelian_permutation_kernel d h hU hV).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (permutation d)
      (nonabelian_permutation_surjective d h hU hV))

theorem nonabelian_quotient_equiv_apply
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (x : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    nonabelian_quotient_equiv d h hU hV (QuotientGroup.mk' _ x) = permutation d x := rfl

end CFSG.Quasithin.Chapter13.Section07
