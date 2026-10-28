module

public import CFSG.Quasithin.Chapter13.Section07.Preliminaries
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.HyperplaneFixer
public import Theory.Representation.BinaryPermutation.Faithful
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Theory.GroupTheory.ConjugateSpanCentralizer

/-!
# The nonabelian span has its actual transposition image

The original natural action identifies its kernel with the centralizer of V.
Since V_H centralizes the seed hyperplane, the finite fixer theorem bounds
its image by a single transposition. Trivial image would make the conjugate
span abelian, so both V_H and H_C have precisely that transposition image.
Restricting to the common Sylow identifies the kernel with O₂(LT), giving
the source's two literal index-two assertions.

Source: Aschbacher–Smith, 13.7.3(4),(7) and13.7.9(1), pp.936,940–941.
-/

@[expose] public section
open Subgroup BinaryPermutation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion NaturalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- Triviality of the realized permutation is exactly original centralization. -/
theorem permutation_eq_one_iff (x : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    permutation d x = 1 ↔ (x : G) ∈ centralizer (V : Set G) := by
  constructor
  · intro hx v hv
    have he := conjugation d x (⟨v,hv⟩ : V)
    rw [hx, map_one, Module.End.one_apply] at he
    have he' := congrArg Subtype.val (d.coordinate.injective he)
    change x.val * v * x.val⁻¹ = v at he'
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  · intro hx
    apply naturalRepresentation_injective (Fin 6) (by decide)
    apply LinearMap.ext
    intro w
    obtain ⟨v, hv⟩ := d.coordinate.surjective (Multiplicative.ofAdd w)
    have hv' : (d.coordinate v).toAdd = w := hv
    rw [← hv']
    rw [← conjugation d x v, map_one, Module.End.one_apply]
    apply congrArg (fun v : V => (d.coordinate v).toAdd)
    apply Subtype.ext
    change x.val * v.val * x.val⁻¹ = v.val
    rw [← hx v.val v.property, mul_inv_cancel_right]

/-- The original point determines the unique possible nontrivial seed fixer. -/
theorem source_hyperplane_fixer : ∃ t : Equiv.Perm (Fin 6), t.IsSwap ∧
    ∀ x : (L ⊔ (T : Subgroup G) : Subgroup G),
      (x : G) ∈ centralizer (V₃ : Set G) → permutation d x = 1 ∨ permutation d x = t := by
  obtain ⟨t, ht, htf⟩ :=
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.HyperplaneFixer.exists_swap_bound_line
      (image d V₁) (image_dim d V₁ (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) 1 d.line_card)
  refine ⟨t, ht, fun x hx => htf (permutation d x) fun w hw => ?_⟩
  rw [← seed_perpendicular d] at hw
  obtain ⟨v,hv,rfl⟩ := (mem_image d V₃ w).mp hw
  rw [← conjugation d x v]
  apply congrArg (fun v : V => (d.coordinate v).toAdd)
  apply Subtype.ext
  change x.val * v.val * x.val⁻¹ = v.val
  rw [← hx v.val hv, mul_inv_cancel_right]

/-- A nonabelian original V-span has nontrivial realized action on V. -/
theorem VH_image_ne_bot
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    ((Section08.Source.VH H V).subgroupOf (L ⊔ (T : Subgroup G))).map (permutation d) ≠ ⊥ := by
  intro he
  apply hV
  apply (conjugateSpanBy_commutative_iff V H).mpr
  apply le_centralizer_iff.mp
  intro x hx
  have hxLT : x ∈ L ⊔ (T : Subgroup G) := (VH_le_core d h hU).trans (h.QH_le_T.trans le_sup_right) hx
  apply (permutation_eq_one_iff d ⟨x,hxLT⟩).mp
  have hm : permutation d ⟨x,hxLT⟩ ∈
      ((Section08.Source.VH H V).subgroupOf (L ⊔ (T : Subgroup G))).map (permutation d) :=
    mem_map_of_mem _ hx
  rw [he] at hm
  exact hm

/-- Both source images are the same actual transposition subgroup. -/
theorem nonabelian_transposition_images
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    ∃ t : Equiv.Perm (Fin 6), t.IsSwap ∧
      ((Section08.Source.VH H V).subgroupOf (L ⊔ (T : Subgroup G))).map (permutation d) = zpowers t ∧
      ((H ⊓ centralizer (Section08.Source.UH H V₃ : Set G)).subgroupOf
        (L ⊔ (T : Subgroup G))).map (permutation d) = zpowers t := by
  obtain ⟨t, ht, htf⟩ := source_hyperplane_fixer d
  let A := ((Section08.Source.VH H V).subgroupOf (L ⊔ (T : Subgroup G))).map (permutation d)
  let B := ((H ⊓ centralizer (Section08.Source.UH H V₃ : Set G)).subgroupOf
    (L ⊔ (T : Subgroup G))).map (permutation d)
  have hAB : A ≤ B := map_mono (comap_mono (VH_centralizes_UH d h hU))
  have hBb : B ≤ zpowers t := by
    rintro _ ⟨x,hx,rfl⟩
    rcases htf x ((centralizer_le (le_conjugateSpanBy V₃ H)) hx.2) with he | he
    · rw [he]; exact one_mem _
    · rw [he]; exact mem_zpowers _
  have htA : t ∈ A := by
    obtain ⟨x,hx,hx1⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr (VH_image_ne_bot d h hU hV))
    obtain ⟨a,ha,rfl⟩ := hx
    have hc : a.val ∈ centralizer (V₃ : Set G) :=
      (centralizer_le (le_conjugateSpanBy V₃ H)) ((VH_centralizes_UH d h hU) ha).2
    rcases htf a hc with he | he
    · exact False.elim (hx1 he)
    · rw [← he]; exact mem_map_of_mem _ ha
  have hA : A = zpowers t := le_antisymm (hAB.trans hBb) (zpowers_le.mpr htA)
  refine ⟨t, ht, hA, le_antisymm hBb ?_⟩
  exact (hA ▸ hAB)

/-- Restricting to the original Sylow identifies the action kernel with Q. -/
theorem core_relIndex_eq_image_card
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (A : Subgroup G) (hAT : A ≤ (T : Subgroup G)) :
    ((L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).relIndex A =
      Nat.card ((A.subgroupOf (L ⊔ (T : Subgroup G))).map (permutation d)) := by
  let P : Subgroup G := L ⊔ (T : Subgroup G)
  have hAP : A ≤ P := hAT.trans le_sup_right
  have hk : (permutation d).ker.map P.subtype = P ⊓ centralizer (V : Set G) := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property, (permutation_eq_one_iff d a).mp ha⟩
    · intro hx
      exact ⟨⟨x,hx.1⟩, (permutation_eq_one_iff d ⟨x,hx.1⟩).mpr hx.2, rfl⟩
  have hi := relIndex_map_map_of_injective (permutation d).ker (A.subgroupOf P) P.subtype_injective
  rw [map_subgroupOf_eq_of_le hAP, hk, relIndex_ker] at hi
  have hsc : (T : Subgroup G) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 := h.sylow_centralizer
  rw [← hi, ← hsc]
  rw [← inf_relIndex_left (H := A) (K := (T : Subgroup G) ⊓ centralizer (V : Set G)),
    ← inf_relIndex_left (H := A) (K := P ⊓ centralizer (V : Set G))]
  congr 1
  ext x
  exact ⟨fun hx => ⟨hx.1,hAP hx.1,hx.2.2⟩, fun hx => ⟨hx.1,hAT hx.1,hx.2.2⟩⟩

/-- The index-two conclusions in 13.7.3(7) and 13.7.9(1), on original groups. -/
theorem nonabelian_core_indices
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    ((L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).relIndex (Section08.Source.VH H V) = 2 ∧
    ((L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).relIndex
      (H ⊓ centralizer (Section08.Source.UH H V₃ : Set G)) = 2 := by
  obtain ⟨t, ht, hA, hB⟩ := nonabelian_transposition_images d h hU hV
  have hHC : H ⊓ centralizer (Section08.Source.UH H V₃ : Set G) ≤
      (T : Subgroup G) := by
    apply le_trans ?_ h.QH_le_T
    apply le_trans ?_ h.kernel_UH_eq_QH.le
    intro x hx
    exact (h.mem_kernel_iff h.UH_le_H).mpr ⟨hx.1, fun u hu => by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hx.2 u hu)]
      exact V₁.one_mem⟩
  rw [core_relIndex_eq_image_card d h (Section08.Source.VH H V) ((VH_le_core d h hU).trans h.QH_le_T),
    core_relIndex_eq_image_card d h _ hHC, hA, hB, Nat.card_zpowers, ht.orderOf]
  exact ⟨rfl,rfl⟩

end CFSG.Quasithin.Chapter13.Section07
