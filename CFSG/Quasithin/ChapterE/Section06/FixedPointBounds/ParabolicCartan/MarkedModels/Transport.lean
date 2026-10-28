module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Inputs
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Localization

/-!
# Placement of the intrinsic Hall--Cartan witness

Restrict an E.3.37 witness to an overgroup of its odd subgroup and Sylow
subgroup, then embed it using an explicitly supplied target Sylow subgroup.
The injective map preserves orders, cyclicity and permutation. This places
the intrinsic construction in the literal M ∩ C_G(U), retaining the actual
residual embedding and original parabolic Sylow in the consumer application.

The maximal-overgroup equality and target Sylow placement are independent
premises. Neither faithfulness on V nor normalizer escape is assumed.
Source: Aschbacher--Smith, E.3.37 and E.6.27, printed pp.239 and 257.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open ChapterB
universe u v
variable {X : Type u} [Group X] [Finite X] {G : Type u} [Group G] [Finite G]

noncomputable def restrictWitness {n : ℕ} (w : NPrimeWitness X n)
    (D : Subgroup X) (hB : w.abelianGroup ≤ D) (hS : (w.sylow : Subgroup X) ≤ D) :
    NPrimeWitness D n := by
  letI := w.abelian
  letI := w.cyclic
  refine {
    abelianGroup := w.abelianGroup.subgroupOf D
    cyclicGroup := w.cyclicGroup.subgroupOf D
    sylow := w.sylow.subtype hS
    cyclic_le := comap_mono w.cyclic_le
    abelian := ?_
    odd := ?_
    cyclic := ?_
    card := ?_
    permutes := ?_ }
  · apply IsMulCommutative.of_comm
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    exact setLike_mul_comm (s := w.abelianGroup) a.property b.property
  · simpa only [Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv] using w.odd
  · exact (subgroupOfEquivOfLe (w.cyclic_le.trans hB)).isCyclic.mpr w.cyclic
  · simpa only [Nat.card_congr (subgroupOfEquivOfLe (w.cyclic_le.trans hB)).toEquiv] using w.card
  · apply Set.image_injective.mpr D.subtype_injective
    change D.subtype '' ((w.abelianGroup.subgroupOf D : Set D) *
      ((w.sylow : Subgroup X).subgroupOf D : Set D)) =
      D.subtype '' (((w.sylow : Subgroup X).subgroupOf D : Set D) *
        (w.abelianGroup.subgroupOf D : Set D))
    rw [Set.image_mul, Set.image_mul]
    change (((w.abelianGroup.subgroupOf D).map D.subtype : Subgroup X) : Set X) *
      ((((w.sylow : Subgroup X).subgroupOf D).map D.subtype : Subgroup X) : Set X) =
      ((((w.sylow : Subgroup X).subgroupOf D).map D.subtype : Subgroup X) : Set X) *
        (((w.abelianGroup.subgroupOf D).map D.subtype : Subgroup X) : Set X)
    simpa only [map_subgroupOf_eq_of_le hB, map_subgroupOf_eq_of_le hS, Sylow.coe_coe] using w.permutes

noncomputable def embedWitness {n : ℕ} (w : NPrimeWitness X n)
    (f : X →* G) (hf : Function.Injective f) (R : Sylow 2 G)
    (hR : (w.sylow : Subgroup X).map f = R) : NPrimeWitness G n := by
  letI := w.abelian
  letI := w.cyclic
  refine {
    abelianGroup := w.abelianGroup.map f
    cyclicGroup := w.cyclicGroup.map f
    sylow := R
    cyclic_le := map_mono w.cyclic_le
    abelian := inferInstance
    odd := ?_
    cyclic := isCyclic_of_surjective (f.subgroupMap w.cyclicGroup)
      (f.subgroupMap_surjective _)
    card := ?_
    permutes := ?_ }
  · simpa only [card_map_of_injective hf] using w.odd
  · simpa only [card_map_of_injective hf] using w.card
  · change (w.abelianGroup.map f : Set G) * (R : Subgroup G) =
      (R : Subgroup G) * (w.abelianGroup.map f : Set G)
    rw [← hR]
    change (f '' (w.abelianGroup : Set X)) * (f '' (w.sylow : Set X)) =
      (f '' (w.sylow : Set X)) * (f '' (w.abelianGroup : Set X))
    rw [← Set.image_mul, ← Set.image_mul, w.permutes]

noncomputable def transport {n : ℕ} {S : Sylow 2 X}
    {hP : IsMinimalParabolicOver S ⊤} (d : IntrinsicHallCartanData S hP n)
    (f : X →* G) (hf : Function.Injective f) (M U : Subgroup G)
    (hC : f.range ≤ centralizer (U : Set G))
    (hM : minimalParabolicMax S hP = M.comap f)
    (R : Sylow 2 ↥(M ⊓ centralizer (U : Set G)))
    (hR : (R : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
      (M ⊓ centralizer (U : Set G)).subtype = (S : Subgroup X).map f) :
    HallCartanData f M U S n := by
  let D := minimalParabolicMax S hP
  let L := M ⊓ centralizer (U : Set G)
  let g : D →* L := (f.comp D.subtype).codRestrict L (by
    intro x
    exact ⟨show x.val ∈ M.comap f from hM ▸ x.property, hC ⟨x, rfl⟩⟩)
  have hg : Function.Injective g := by
    intro a b hab
    exact Subtype.ext (hf (congrArg Subtype.val hab))
  have hS : (d.witness.sylow : Subgroup X) ≤ D := by
    rw [d.sylow_eq]
    exact (minimalParabolicMax_spec S hP).2
  let wD := restrictWitness d.witness D d.hall_le hS
  have hR' : (wD.sylow : Subgroup D).map g = R := by
    apply map_injective L.subtype_injective
    rw [map_map, hR]
    change (((d.witness.sylow : Subgroup X).subgroupOf D).map
      (f.comp D.subtype)) = _
    rw [← map_map, map_subgroupOf_eq_of_le hS, d.sylow_eq]
  let w := embedWitness wD g hg R hR'
  refine {
    witness := w
    hallGroup := d.witness.abelianGroup
    twoGroup := d.twoGroup
    hall_image := ?_
    sylow_image := hR.symm
    hall_le := hM ▸ d.hall_le
    hall := hM ▸ d.hall
    normalizes := d.normalizes
    frattini := d.frattini }
  change d.witness.abelianGroup.map f =
    ((d.witness.abelianGroup.subgroupOf D).map g).map L.subtype
  rw [map_map]
  change _ = (d.witness.abelianGroup.subgroupOf D).map (f.comp D.subtype)
  rw [← map_map, map_subgroupOf_eq_of_le d.hall_le]

/-- The consumer uses the same residual embedding and Sylow subgroup as
E.6.27, with only the separately owned placement premises left explicit. -/
noncomputable def transportResidual {U : Subgroup G}
    (S : Sylow 2 (centralizer (U : Set G)))
    (H : Subgroup (primeToResidual 2 (centralizer (U : Set G))))
    (hH : IsMinimalParabolicOver (residualSylow S) H) (n : ℕ)
    (d : IntrinsicHallCartanData (parabolicSylow S H hH)
      (minimalParabolic_subtype (residualSylow S) H hH) n)
    (M : Subgroup G)
    (hM : minimalParabolicMax (parabolicSylow S H hH)
      (minimalParabolic_subtype (residualSylow S) H hH) = M.comap (residualEmbedding U H))
    (R : Sylow 2 ↥(M ⊓ centralizer (U : Set G)))
    (hR : (R : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
      (M ⊓ centralizer (U : Set G)).subtype =
      (S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype) :
    HallCartanData (residualEmbedding U H) M U (parabolicSylow S H hH) n := by
  refine transport d (residualEmbedding U H) (residualEmbedding_injective U H) M U ?_ hM R ?_
  · rintro _ ⟨x, rfl⟩
    exact ((x : primeToResidual 2 (centralizer (U : Set G))) :
      centralizer (U : Set G)).property
  · rw [parabolicSylow_image]
    exact hR

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
