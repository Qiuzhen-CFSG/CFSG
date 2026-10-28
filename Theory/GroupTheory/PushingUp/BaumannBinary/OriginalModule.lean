module

public import Theory.GroupTheory.PushingUp.BaumannBinary.ActionKernel
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.BinaryOffender.Homogeneous.Basic

/-!
# Fixed-space generation on the original Baumann module

The original Ω₁(Z(P)) lies in the P-fixed space. Its conjugates generate V,
so the fixed space of the marked Sylow image generates the binary module.
Global fixed vectors are precisely V∩Z(L), preserving the original center
in DGS85 (6.3), printed p.120. This also discharges fixed-space generation
when applying the corrected DGS (5.12) to this original action. It does not
supply quadraticity, the cardinality bound or the natural-module conclusion.
-/

public section
open Subgroup
open scoped IsMulCommutative

namespace Theory.GroupTheory.BaumannBinary
open Representation Representation.BinaryOffender
variable {G H : Type*} [Group G] [Group H]

/-- Fixed vectors of the original Sylow image generate its omega-center closure. -/
theorem fixed_generation (P : Sylow 2 G)
    [IsElementaryAbelian 2 (centerClosure (P : Subgroup G))]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (centerClosure (P : Subgroup G) : Set G)) :
    Homogeneous.orbitSpan
      (NormalElementaryQuotient.representation (centerClosure (P : Subgroup G)) q hq hker)
      ⊤ (fixedSpace
        (NormalElementaryQuotient.representation (centerClosure (P : Subgroup G)) q hq hker)
        ((P : Subgroup G).map q)) = ⊤ := by
  let V := centerClosure (P : Subgroup G)
  let ρ := NormalElementaryQuotient.representation V q hq hker
  let O := Homogeneous.orbitSpan ρ ⊤ (fixedSpace ρ ((P : Subgroup G).map q))
  let K : Subgroup V := O.toAddSubgroup.toSubgroup'
  let N := K.map V.subtype
  have hN : N.Normal := by
    constructor
    rintro _ ⟨v,hv,rfl⟩ g
    let w := (ρ (q g) (Additive.ofMul v)).toMul
    have hw : w ∈ K :=
      ((Homogeneous.orbitSpan_invariant ρ ⊤ _) (mem_top (q g)) (Additive.ofMul v)).2 hv
    exact ⟨w,hw,NormalElementaryQuotient.representation_apply V q hq hker g _⟩
  let : N.Normal := hN
  have hVN : V ≤ N := by
    apply normalClosure_le_normal
    intro z hz
    have hzV : z ∈ V := le_normalClosure hz
    let v : Additive V := Additive.ofMul ⟨z,hzV⟩
    have hv : v ∈ fixedSpace ρ ((P : Subgroup G).map q) := by
      apply (NormalElementaryQuotient.mem_fixedSpace_image V q hq hker _ v).mpr
      exact ((mem_omegaCenterIn_iff _ _).mp hz).2.1
    exact ⟨v.toMul,Homogeneous.le_orbitSpan ρ ⊤ _ hv,rfl⟩
  apply top_unique
  intro v _
  obtain ⟨w,hw,he⟩ := hVN v.toMul.property
  have he' : w = v.toMul := Subtype.ext he
  change v.toMul ∈ K
  rwa [he'] at hw

/-- The global fixed space retains precisely the original central summand. -/
theorem fixedSpace_eq_center (P : Sylow 2 G)
    [IsElementaryAbelian 2 (centerClosure (P : Subgroup G))]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (centerClosure (P : Subgroup G) : Set G)) :
    fixedSpace
      (NormalElementaryQuotient.representation (centerClosure (P : Subgroup G)) q hq hker) ⊤ =
      NormalElementaryQuotient.subspace (centerClosure (P : Subgroup G))
        (((centerClosure (P : Subgroup G)) ⊓ center G).subgroupOf
          (centerClosure (P : Subgroup G))) := by
  ext v
  have hh := NormalElementaryQuotient.mem_fixedSpace_image
    (centerClosure (P : Subgroup G)) q hq hker (⊤ : Subgroup G) v
  rw [map_top_of_surjective q hq, coe_top, centralizer_univ] at hh
  exact hh.trans (by
    change (v.toMul : G) ∈ center G ↔ (v.toMul : G) ∈ centerClosure (P : Subgroup G) ∧ (v.toMul : G) ∈ center G
    exact ⟨fun h => ⟨v.toMul.property,h⟩,And.right⟩)
end Theory.GroupTheory.BaumannBinary
