module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearClosure
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ClosureCenterGeneration
public import Theory.Representation.NormalElementaryQuotient.NaturalNormalSubgroup
public import Theory.GroupTheory.PResidual.CentralCoverMovement

/-!
# The first DGS 6.5 natural-module alternative

The neighboring center lies in the actual Baumann center closure and is
normal in X. The proved linear 6.4 premises give an equivariant natural
projection whose kernel is precisely the central part. Transitivity of SL₂
on nonzero natural vectors forces the neighboring center either to be
central in X or to cover that projection. This works also over F₂.

In the noncentral alternative, p-perfect commutator idempotence removes the
central summand and bounds the core-residual commutator by Z_lambda itself.

The original completion embeddings transport the entire statement, including
the central summand. The reduced F1.11 application constructs the enlarged
linear quotient from the original local quotient marking.

Source: DGS, Groups and Graphs (1985), 6.5, printed p.121. Excluding these
alternatives, and selecting the linear model from general 6.4, remain open.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.DGS85.BaumannApplication
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The first 6.5 dichotomy for the literal neighboring center, with all Baumann premises discharged in the linear case. -/
theorem source_linear_neighbor_center_alternative (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : localEnlargement d ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (q : localEnlargement d →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    let V := conjugateSpanBy (omegaCenterIn ((P i).pCoreIn 2)) X
    sylowCenterSpan (P (other i)) ≤ centralizer (X : Set G) ∨
      sylowCenterSpan (P (other i)) ⊔ (V ⊓ centralizer (X : Set G)) = V := by
  let := d.finite_P
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  let V := conjugateSpanBy (omegaCenterIn ((P i).pCoreIn 2)) X
  let Z := sylowCenterSpan (P (other i))
  let C := coreClosure (P i) (P (other i))
  let ι := originalEmbedding (P i) (P (other i))
  have hinj := MarkedClosure.originalEmbedding_injective (P i) (P (other i))
  have hAP : (P i).pCoreIn 2 ≤ P (other i) :=
    (source_core_le_borel (Classical.choice (h.local_data i))).trans
      (le_sup_right.trans d.supplement.le)
  have hrange : ι.range = X := MarkedClosure.originalEmbedding_range _ _ hAP
  have hιX (x : C) : ι x ∈ X := hrange ▸ (show ι x ∈ ι.range from ⟨x,rfl⟩)
  have hn' := (inter_core_local_normal_iff h i d).mp hn
  have hZV : Z ≤ V := source_neighbor_center_le_baumann h hB hS i hn'
  have hZX : Z ≤ X := source_center_le_core_closure h hB hS i
  obtain ⟨hi,qX,hqX,hkX,_⟩ := source_linear_closure_premises h hB hS i d hn q hq hk
  let T := coreSylow (P i) (P (other i)) hi
  let Vi := BaumannBinary.centerClosure (T : Subgroup C)
  let Zi := Z.comap ι
  let : IsElementaryAbelian 2 Vi :=
    (BaumannBinary.centerClosure_reduced T (MarkedClosure.selfCentralizing h i)).elementary
  have hVi : Vi.map ι = V := MarkedClosure.centerClosure_image _ _ hAP
  have hZi : Zi.map ι = Z := by
    apply le_antisymm (map_comap_le _ _)
    intro z hz
    obtain ⟨x,rfl⟩ := (hrange.symm ▸ hZX hz : z ∈ ι.range)
    exact mem_map.mpr ⟨x,hz,rfl⟩
  have hZiVi : Zi ≤ Vi := (map_le_map_iff_of_injective hinj).mp (by rw [hZi,hVi]; exact hZV)
  have hZnorm : P (other i) ≤ normalizer (Z : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (sylowCenterSpan_le _)).mp (sylowCenterSpan_normal _)
  let : Zi.Normal := ⟨by
    intro z hz g
    change ι (g*z*g⁻¹) ∈ Z
    rw [map_mul,map_mul,map_inv]
    exact le_normalizer_iff.mp hZnorm (ι g) g.val.property (ι z) hz⟩
  let := Fintype.ofFinite F
  obtain ⟨n,_,hF⟩ := FiniteField.card F 2
  obtain ⟨f,_,hfker,hfe⟩ := BaumannBinary.centerClosure_natural_projection_all T
    (MarkedClosure.selfCentralizing h i) (MarkedClosure.noCharacteristicNormal h hB i d hn)
    qX hqX hkX n.property ((Nat.card_eq_fintype_card (α := F)).trans hF)
  have hker (v : Additive Vi) : f v = 0 ↔ (v.toMul : C) ∈ center C := by
    change v ∈ LinearMap.ker f ↔ _
    rw [hfker]
    change ((v.toMul : C) ∈ Vi ∧ (v.toMul : C) ∈ center C) ↔ _
    exact and_iff_right v.toMul.property
  have hc (x : C) : x ∈ center C ↔ ι x ∈ centralizer (X : Set G) := by
    rw [mem_center_iff]
    constructor
    · intro hx y hy
      obtain ⟨g,rfl⟩ := (hrange.symm ▸ hy : y ∈ ι.range)
      exact (map_mul ι g x).symm.trans ((congrArg ι (hx g)).trans (map_mul ι x g))
    · intro hx g
      apply hinj
      simpa only [map_mul] using hx (ι g) (hιX g)
  have hCV : (Vi ⊓ center C).map ι = V ⊓ centralizer (X : Set G) := by
    apply le_antisymm
    · rintro z ⟨x,hx,rfl⟩
      exact ⟨hVi ▸ mem_map_of_mem ι hx.1,(hc x).mp hx.2⟩
    · intro z hz
      obtain ⟨x,hx,rfl⟩ := (hVi.symm ▸ hz.1 : z ∈ Vi.map ι)
      exact mem_map.mpr ⟨x,⟨hx,(hc x).mpr hz.2⟩,rfl⟩
  rcases Representation.NormalElementaryQuotient.normal_subgroup_alternative_of_natural_projection
    Vi qX hqX f hker hfe Zi hZiVi with hcentral | hcover
  · left
    intro z hz
    obtain ⟨x,hx,rfl⟩ := (hZi.symm ▸ hz : z ∈ Zi.map ι)
    exact (hc x).mp (hcentral hx)
  · right
    have hm := congrArg (Subgroup.map ι) hcover
    rwa [Subgroup.map_sup,hZi,hCV,hVi] at hm
end CFSG.Quasithin.ChapterF.Source.DGS85

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The source 6.5 alternative in the actual reduced F1.11 completion, using
the original local linear quotient and no additional naturality premise. -/
theorem reduced_linear_neighbor_center_alternative (h : HypothesisF11 L S) (i : Fin 2)
    (hn : localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑(((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)))
    (e : (L (other i) ⧸ pCore 2 (L (other i))) ≃* PSL(2,F)) :
    let A := ((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2
    let Z := sylowCenterSpan ((P₀ L S (other i)).subgroupOf (G₀ L S))
    let X := conjugateSpanBy A ((P₀ L S (other i)).subgroupOf (G₀ L S))
    let V := conjugateSpanBy (omegaCenterIn A) X
    Z ≤ centralizer (X : Set (G₀ L S)) ∨
      Z ⊔ (V ⊓ centralizer (X : Set (G₀ L S))) = V := by
  let d := Classical.choice ((reduced_triple h).local_data (other i))
  let f := reduced_linearEnlargementQuotient h (other i) d e
  let q := f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localEnlargement d)))
  have hq : Function.Surjective q := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 (localEnlargement d) := by
    rw [MonoidHom.ker_comp_of_injective _ _ f.injective,QuotientGroup.ker_mk']
  exact source_linear_neighbor_center_alternative (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) i d hn q hq hk
end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction

namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Source 6.5's noncentral deduction: the full core-residual movement lies
in the actual neighboring center, with no central error term. -/
theorem source_linear_noncentral_residual_bound (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : localEnlargement d ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (q : localEnlargement d →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d))
    (hnc : ¬ sylowCenterSpan (P (other i)) ≤ centralizer
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) : Set G)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    ⁅X.pCoreIn 2,(pResidual 2 X).map X.subtype⁆ ≤ sylowCenterSpan (P (other i)) := by
  let := d.finite_P
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  let V := conjugateSpanBy (omegaCenterIn ((P i).pCoreIn 2)) X
  let Z := sylowCenterSpan (P (other i))
  have hXP : X ≤ P (other i) := conjugateSpanBy_le_self
    ((source_core_le_borel (Classical.choice (h.local_data i))).trans
      (le_sup_right.trans d.supplement.le))
  let : Finite X := Finite.of_injective (inclusion hXP) (inclusion_injective _)
  have hVX : V ≤ X := conjugateSpanBy_le_self
    ((show omegaCenterIn ((P i).pCoreIn 2) ≤ (P i).pCoreIn 2 from map_subtype_le _).trans
      (le_conjugateSpanBy _ _))
  have hZX : Z ≤ X := source_center_le_core_closure h hB hS i
  let : (Z.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer
    (hXP.trans ((normal_subgroupOf_iff_le_normalizer (sylowCenterSpan_le _)).mp
      (sylowCenterSpan_normal _)))
  have hcover : Z ⊔ (V ⊓ centralizer (X : Set G)) = V :=
    (source_linear_neighbor_center_alternative h hB hS i d hn q hq hk).resolve_left hnc
  have hcomm : ⁅pCore 2 X,(⊤ : Subgroup X)⁆ ≤ V.subgroupOf X := by
    apply (map_le_iff_le_comap).mp
    rw [map_commutator,←MonoidHom.range_eq_map,range_subtype]
    exact source_linear_baumann_commutator h hB hS i d hn q hq hk
  have hcoverX : Z.subgroupOf X ⊔ (V.subgroupOf X ⊓ center X) = V.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup,Subgroup.map_inf _ _ _ X.subtype_injective,
      map_subgroupOf_eq_of_le hZX,map_subgroupOf_eq_of_le hVX,←centerIn_eq_map_center]
    change Z ⊔ (V ⊓ (X ⊓ centralizer (X : Set G))) = V
    rw [←inf_assoc,inf_eq_left.mpr hVX]
    exact hcover
  have hm := map_mono (f := X.subtype)
    (core_residual_le_of_central_cover (V.subgroupOf X) (Z.subgroupOf X) hcomm hcoverX)
  rw [map_commutator,map_subgroupOf_eq_of_le hZX] at hm
  exact hm

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The literal reduced F1.11 noncentral branch supplies its core-residual
bound on the same center and completion; no Sylow or naturality premise is added. -/
theorem reduced_linear_noncentral_residual_bound (h : HypothesisF11 L S) (i : Fin 2)
    (hn : localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑(((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)))
    (e : (L (other i) ⧸ pCore 2 (L (other i))) ≃* PSL(2,F))
    (hnc : ¬ sylowCenterSpan ((P₀ L S (other i)).subgroupOf (G₀ L S)) ≤ centralizer
      (conjugateSpanBy (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)
        ((P₀ L S (other i)).subgroupOf (G₀ L S)) : Set (G₀ L S))) :
    let X := conjugateSpanBy (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)
      ((P₀ L S (other i)).subgroupOf (G₀ L S))
    ⁅X.pCoreIn 2,(pResidual 2 X).map X.subtype⁆ ≤
      sylowCenterSpan ((P₀ L S (other i)).subgroupOf (G₀ L S)) := by
  let d := Classical.choice ((reduced_triple h).local_data (other i))
  let f := reduced_linearEnlargementQuotient h (other i) d e
  let q := f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localEnlargement d)))
  have hq : Function.Surjective q := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 (localEnlargement d) := by
    rw [MonoidHom.ker_comp_of_injective _ _ f.injective,QuotientGroup.ker_mk']
  exact source_linear_noncentral_residual_bound (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) i d hn q hq hk hnc
end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
