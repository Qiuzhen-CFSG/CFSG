module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalIndex
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections

/-!
# Sylow transport to the exceptional component quotient

The selected component K_D is subnormal in C_G(C), and adjoining its
central subgroup C preserves subnormality. Restrict the original Sylow
overgroup of C_T(C) to K_D C, then map it through the literal two-core
quotient. Intersection and quotient images cannot increase the previously
proved relative index two bound.

This supplies the actual quotient Sylow subgroup in the final model
inspection of Aschbacher--Smith 13.5.15(7), printed pp.920--921.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalQuotientSylow
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open Chapter1.Section02.IndexTwo

variable {G : Type*} [Group G] [Finite G]

private theorem quotient_sylow_index {H J A : Subgroup G}
    (hJH : J ≤ H) (hAH : A ≤ H) (hJ : (J.subgroupOf H).IsSubnormal)
    (S : Sylow 2 H) (hAS : A.subgroupOf H ≤ S)
    (hindex : (A.subgroupOf H).relIndex (S : Subgroup H) ≤ 2) :
    ∃ R : Sylow 2 (J ⧸ pCore 2 J),
      ((A ⊓ J).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ≤ R ∧
      (((A ⊓ J).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))).relIndex
        (R : Subgroup (J ⧸ pCore 2 J)) ≤ 2 := by
  let B := (S : Subgroup H).map H.subtype
  have hB : Chapter1.IsSylowIn 2 B H := ⟨S,rfl⟩
  obtain ⟨U,hU⟩ := isSylowIn_inf_of_subnormal hB hJH hJ
  have hAB : A ≤ B := by
    intro x hx
    exact mem_map_of_mem H.subtype (hAS (show (⟨x,hAH hx⟩ : H) ∈ A.subgroupOf H from hx))
  have hABindex : A.relIndex B ≤ 2 := by
    have he := relIndex_map_map_of_injective (A.subgroupOf H) (S : Subgroup H) H.subtype_injective
    rw [map_subgroupOf_eq_of_le hAH] at he
    exact he.symm ▸ hindex
  have hAU : (A ⊓ J).subgroupOf J ≤ U := by
    intro x hx
    have hm : (x : G) ∈ (U : Subgroup J).map J.subtype := hU.symm ▸ ⟨hAB hx.1,hx.2⟩
    obtain ⟨y,hy,he⟩ := hm
    exact (Subtype.ext he : y=x) ▸ hy
  have hUI : ((A ⊓ J).subgroupOf J).relIndex (U : Subgroup J) ≤ 2 := by
    have he := relIndex_map_map_of_injective ((A ⊓ J).subgroupOf J) (U : Subgroup J) J.subtype_injective
    rw [map_subgroupOf_eq_of_le inf_le_right,hU] at he
    have hint : (A ⊓ J).relIndex (B ⊓ J) = A.relIndex (B ⊓ J) := by
      rw [←inf_relIndex_right,inf_assoc,inf_left_comm J B,inf_idem,inf_relIndex_right]
    rw [←he,hint]
    exact (relIndex_le_of_le_right inf_le_left index_ne_zero_of_finite).trans hABindex
  let q := QuotientGroup.mk' (pCore 2 J)
  refine ⟨U.mapSurjective (f := q) (QuotientGroup.mk'_surjective _),map_mono hAU,?_⟩
  exact (map_relIndex_le q ((A ⊓ J).subgroupOf J) (U : Subgroup J)).trans hUI

omit [Finite G] in
/-- The central order-two factor preserves subnormality of the actual
component inside its original centralizer. -/
theorem component_central_join_subnormal {C KD : Subgroup G}
    (hc : Nat.card C = 2) (hKD : KD ≤ centralizer (C : Set G))
    (hcomp : (KD.subgroupOf (centralizer (C : Set G))).IsCComponent) :
    ((KD ⊔ C).subgroupOf (centralizer (C : Set G))).IsSubnormal := by
  let H := centralizer (C : Set G)
  let : IsCyclic C := isCyclic_of_prime_card (p := 2) hc
  have hCH : C ≤ H := C.le_centralizer
  let N := C.subgroupOf H
  let : N.Normal := normal_subgroupOf_of_le_normalizer (centralizer_le_normalizer C)
  let q := QuotientGroup.mk' N
  have hs := (hcomp.subnormal.map (QuotientGroup.mk'_surjective N)).comap q
  rw [comap_map_eq,QuotientGroup.ker_mk'] at hs
  rw [subgroupOf_sup hKD hCH]
  exact hs

/-- The original exceptional index bound descends to the actual quotient
of K_D C by its own two-core. The selected component remains literal. -/
theorem exists_exceptional_quotient_sylow
    {D : ChapterF.Section09.Setup G} {V₂ M : Subgroup G}
    (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
    (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH)
    (g : D.L) (hK : NormalBranch.K D g.val ≤ D.L)
    (hp : IsPPerfect 2 (NormalBranch.K D g.val)) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hc : Nat.card ((D.T : Subgroup G) ⊓
      centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) = 2)
    (KD : Subgroup G)
    (hKD : KD ≤ centralizer (((D.T : Subgroup G) ⊓
      centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) : Set G))
    (hcomp : (KD.subgroupOf (centralizer (((D.T : Subgroup G) ⊓
      centralizer (NormalBranch.K D g.val : Set G) : Subgroup G) : Set G))).IsCComponent) :
    let C := (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)
    let T₀ := (D.T : Subgroup G) ⊓ centralizer (C : Set G)
    let J := KD ⊔ C
    ∃ R : Sylow 2 (J ⧸ pCore 2 J),
      ((T₀ ⊓ J).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ≤ R ∧
      (((T₀ ⊓ J).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))).relIndex
        (R : Subgroup (J ⧸ pCore 2 J)) ≤ 2 := by
  dsimp only
  let C := (D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G)
  let : IsCyclic C := isCyclic_of_prime_card (p := 2) hc
  obtain ⟨S,hS,hidx⟩ := SourceExceptionalIndex.exists_exceptional_centralizer_sylow
    d h e hseed hn hU g hK hp a hi hc
  exact quotient_sylow_index (sup_le hKD C.le_centralizer) inf_le_right
    (component_central_join_subnormal hc hKD hcomp) S hS hidx

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalQuotientSylow
