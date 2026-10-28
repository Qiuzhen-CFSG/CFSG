module
public import Theory.GroupTheory.AbelianSylowTransfer
public import Theory.SpecificGroups.SL2.SylowCharacteristicImage
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.Commutator.NormalSpan
public import Theory.GroupTheory.ConjugateSpanSupplement
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

open Subgroup
open scoped MatrixGroups IsMulCommutative commutatorElement
/-!
# Sylow and quotient structure of a linear normal closure

In a finite group mapping onto binary SL₂, let A lie in a Sylow T, be
invariant under N(T), and escape the kernel. Rank-one irreducibility gives
A the full Sylow image; two conjugate Sylows then show its normal closure
surjects onto SL₂. If A intersect ker(q) is normal, that intersection
centralizes the closure kernel modulo itself. Transfer on the resulting
abelian Sylow proves that A is Sylow in its normal closure.

All fields of characteristic two, including F₂, use the same proof.
The quotient map is the restriction of the original map.
Source: DGS, Groups and Graphs (1985), 6.4, printed pp.120--121.
-/

public noncomputable section
namespace Matrix.SpecialLinearGroup
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

private theorem sylow_commutative (S : Sylow 2 SL(2,F)) : IsMulCommutative S := by
  let e : Multiplicative F ≃* upperUnipotent F := MonoidHom.ofInjective (upperUnipotentHom_injective F)
  let : IsMulCommutative (upperUnipotent F) := ⟨⟨fun a b => e.symm.injective (by simp only [map_mul,mul_comm])⟩⟩
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,F) (upperUnipotentSylow F 2) S
  have he : (S : Subgroup SL(2,F)) = (upperUnipotent F).map (MulAut.conj g).toMonoidHom :=
    (congrArg (fun T : Sylow 2 SL(2,F) => T.toSubgroup) hg).symm
  change IsMulCommutative (S : Subgroup SL(2,F))
  rw [he]
  infer_instance

/-- The literal normal closure surjects under the original linear map. -/
theorem normalClosure_linear_image
    (T : Sylow 2 G) (q : G →* SL(2,F)) (hq : Function.Surjective q)
    (A : Subgroup G) (hAT : A ≤ T) (hne : ¬ A ≤ q.ker)
    (hn : normalizer (T : Set G) ≤ normalizer (A : Set G)) :
    (normalClosure (A : Set G)).map q = ⊤ := by
  have hA := normalizer_invariant_image_eq_sylow T q hq A hAT hne hn
  let X := normalClosure (A : Set G)
  let : (X.map q).Normal := (inferInstance : X.Normal).map q hq
  obtain ⟨g,_,hg⟩ := exists_residual_conjugate_sylow_image_sup_eq_top T q hq
  have hAX : (T : Subgroup G).map q ≤ X.map q := hA ▸ map_mono (show A ≤ X from le_normalClosure)
  apply top_unique
  rw [←hg]
  refine sup_le hAX ?_
  have hconj : ((T : Subgroup G).map (MulAut.conj g).toMonoidHom).map q =
      ((T : Subgroup G).map q).map (MulAut.conj (q g)).toMonoidHom := by
    rw [Subgroup.map_map,Subgroup.map_map]
    congr 1
    ext x
    simp
  rw [hconj]
  exact (map_mono hAX).trans (mem_normalizer_iff_map_conj_eq.mp
    (show q g ∈ normalizer (X.map q : Set SL(2,F)) from by rw [normalizer_eq_top]; trivial)).le

/-- Normality of the actual kernel intersection makes A Sylow in its normal closure. -/
theorem normalClosure_linear_sylow
    (T : Sylow 2 G) (q : G →* SL(2,F)) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (A : Subgroup G) (hAT : A ≤ T) (hne : ¬ A ≤ q.ker)
    (hn : normalizer (T : Set G) ≤ normalizer (A : Set G))
    (hD : (A ⊓ q.ker).Normal) :
    ∃ R : Sylow 2 (normalClosure (A : Set G)),
      (R : Subgroup (normalClosure (A : Set G))) = A.subgroupOf (normalClosure (A : Set G)) := by
  let N := q.ker
  let X := normalClosure (A : Set G)
  let D := A ⊓ N
  let := hD
  have hAX : A ≤ X := le_normalClosure
  have hNT : N ≤ (T : Subgroup G) := hk.le_sylow_of_normal T
  have hTX : A ⊔ N = T := by
    have he := congrArg (Subgroup.comap q)
      (normalizer_invariant_image_eq_sylow T q hq A hAT hne hn)
    rwa [comap_map_eq,comap_map_eq_self hNT] at he
  have hXN : X ⊔ N = ⊤ := by
    have he := congrArg (Subgroup.comap q) (normalClosure_linear_image T q hq A hAT hne hn)
    rwa [comap_map_eq,comap_top] at he
  have hNA : N ≤ normalizer (A : Set G) := hNT.trans ((T : Subgroup G).le_normalizer.trans hn)
  have hgen : normalClosure (A.subgroupOf X : Set X) = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [map_normalClosure_eq_conjugateSpanBy_range,map_subgroupOf_eq_of_le hAX,
      range_subtype,←MonoidHom.range_eq_map,range_subtype]
    have he := conjugateSpanBy_sup_of_normalizes_seed A X N hNA le_normalizer_of_normal
    rw [hXN,←normalClosure_eq_conjugateSpanBy_top] at he
    exact he.symm
  have hcomm : ⁅N,X⁆ ≤ D := by
    rw [commutator_comm]
    change ⁅normalClosure (A : Set G),N⁆ ≤ D
    rw [normalClosure_eq_conjugateSpanBy_top,
      commutator_conjugateSpanBy_of_normalized_right A ⊤ N le_top le_normalizer_of_normal]
    apply conjugateSpanBy_le _ le_normalizer_of_normal
    exact le_inf (le_normalizer_iff_commutator_le_left.mp hNA) (commutator_le_right A N)
  have hAA : ⁅A,A⁆ ≤ D := by
    apply le_inf (le_normalizer_iff_commutator_le_left.mp A.le_normalizer)
    apply (Subgroup.map_eq_bot_iff _).mp
    rw [map_commutator,normalizer_invariant_image_eq_sylow T q hq A hAT hne hn]
    let S := T.mapSurjective hq
    let := sylow_commutative S
    exact commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative S)
  obtain ⟨R,hR⟩ := T.exists_subgroupOf_eq_of_normal X
  have hAR : A.subgroupOf X ≤ (R : Subgroup X) := by
    rw [hR]
    exact fun x hx => hAT hx
  have hNR : N.subgroupOf X ≤ (R : Subgroup X) := by
    rw [hR]
    exact fun x hx => hNT hx
  have hs : A.subgroupOf X ⊔ N.subgroupOf X = R := by
    apply le_antisymm (sup_le hAR hNR)
    intro x hx
    have hxT : (x : G) ∈ A ⊔ N := hTX.symm ▸ (show (x : G) ∈ T from show x ∈ (T : Subgroup G).subgroupOf X from hR ▸ hx)
    rw [mem_sup_of_normal_right] at hxT
    obtain ⟨a,ha,n,hnN,he⟩ := hxT
    have hnX : n ∈ X := by
      have hh := X.mul_mem (X.inv_mem (hAX ha)) x.property
      rwa [←he,inv_mul_cancel_left] at hh
    exact mem_sup_of_normal_right.mpr ⟨⟨a,hAX ha⟩,ha,⟨n,hnX⟩,hnN,Subtype.ext he⟩
  have hnR : normalizer (R : Set X) ≤ normalizer (A.subgroupOf X : Set X) := by
    intro g hg
    have hRm : (R : Subgroup X).map (q.comp X.subtype) = (T : Subgroup G).map q := by
      apply le_antisymm
      · rintro y ⟨x,hx,rfl⟩
        exact mem_map_of_mem q (show (x : G) ∈ T from show x ∈ (T : Subgroup G).subgroupOf X from hR ▸ hx)
      · rw [←normalizer_invariant_image_eq_sylow T q hq A hAT hne hn]
        rintro y ⟨a,ha,rfl⟩
        exact mem_map.mpr ⟨⟨a,hAX ha⟩,hAR ha,rfl⟩
    have hgq := (R : Subgroup X).le_normalizer_map (q.comp X.subtype)
      (mem_map_of_mem (q.comp X.subtype) hg)
    rw [hRm] at hgq
    have hgT : (g : G) ∈ normalizer (T : Set G) := by
      have hh := le_normalizer_comap q hgq
      rwa [comap_map_eq_self hNT] at hh
    exact le_normalizer_comap X.subtype (hn hgT)
  have hAA' : ⁅A.subgroupOf X,A.subgroupOf X⁆ ≤ D.subgroupOf X := by
    apply (map_le_iff_le_comap).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hAX]
    exact hAA
  have hN' : ⁅N.subgroupOf X,⊤⁆ ≤ D.subgroupOf X := by
    apply (map_le_iff_le_comap).mp
    rw [map_commutator,subgroupOf_map_subtype,←MonoidHom.range_eq_map,range_subtype]
    exact (commutator_mono inf_le_left le_rfl).trans hcomm
  have he := sylow_eq_of_normal_generation_mod_central R (A.subgroupOf X) (N.subgroupOf X)
    (D.subgroupOf X) (fun _ hx => hx.1) hAR hNR hs hAA' hN' hnR hgen
  exact ⟨R,he.symm⟩
/-- The restricted original map has the intrinsic two-core as its full kernel. -/
theorem normalClosure_linear_quotient
    (T : Sylow 2 G) (q : G →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 G) (A : Subgroup G) (hAT : A ≤ T) (hne : ¬ A ≤ q.ker)
    (hn : normalizer (T : Set G) ≤ normalizer (A : Set G)) :
    Function.Surjective (q.comp (normalClosure (A : Set G)).subtype) ∧
      (q.comp (normalClosure (A : Set G)).subtype).ker =
        pCore 2 (normalClosure (A : Set G)) := by
  constructor
  · intro y
    obtain ⟨x,hx,he⟩ := (show y ∈ (normalClosure (A : Set G)).map q from
      normalClosure_linear_image T q hq A hAT hne hn ▸ mem_top y)
    exact ⟨⟨x,hx⟩,he⟩
  · rw [←MonoidHom.comap_ker,hk,←pCore_eq_comap_of_normal]
end Matrix.SpecialLinearGroup
