module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalIrreducibility.FaithfulAction
public import Theory.GroupTheory.Commutator.CentralQuotientSaturation
public import Theory.GroupTheory.ReducedNormal.SubspaceMinimality

/-!
# Lifting the original local central image to the full module

The local module maps to the literal full central quotient by inclusion
followed by its defining projection. Its image is nonzero and invariant
under the original L₀ action. If that image exhausts the quotient, full
commutator generation lifts the equality to V = V_M, retaining the central
kernel. In particular irreducibility for L₀, once established by D.3.9,
removes the full/local equality premise without any splitting assumption.

Source: Aschbacher--Smith D.3.9, printed pp.199--201; the required full
commutator generation is source 3.2.2(3), printed p.579.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

local instance tensorPassageFullElementary : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
local instance tensorPassageLocalElementary : IsElementaryAbelian 2 D.moduleSubgroup :=
  D.module_elementary

/-- The local module's literal map into V_M/C_VM(L₀). -/
def originalLocalCentralProjection : D.moduleSubgroup →* D.fullCentralQuotient :=
  (QuotientGroup.mk' D.fullCentralizer).comp
    (inclusion (le_componentOrbit D.moduleSubgroup D.maximalLocal))

/-- The same map in binary linear coordinates. -/
def originalLocalCentralLinearProjection :
    Additive D.moduleSubgroup →ₗ[ZMod 2] Additive D.fullCentralQuotient :=
  (originalLocalCentralProjection D).toAdditive.toZModLinearMap 2

/-- The central quotient retains enough information to recover the whole local module. -/
theorem source_local_eq_full_of_central_projection_surjective
    (hs : Function.Surjective (originalLocalCentralProjection D)) :
    D.moduleSubgroup = D.fullModule := by
  apply eq_of_central_quotient_surjective (localOrbit T L) D.fullModule D.moduleSubgroup
    (le_componentOrbit _ _) D.orbit_normalizes_module
    (D.fullModule_eq_commutator (source_module_nonsolvable_uniqueness D)).symm
    (QuotientGroup.mk' D.fullCentralizer) _ hs
  rw [QuotientGroup.ker_mk']
  exact le_rfl

/-- The local central image is nonzero before any classification or full/local equality. -/
theorem originalLocalCentralLinearProjection_range_ne_bot :
    (originalLocalCentralLinearProjection D).range ≠ ⊥ := by
  intro hz
  have hc : D.moduleSubgroup ≤ centralizer (localOrbit T L : Set G) := by
    intro v hv
    have he : originalLocalCentralLinearProjection D (Additive.ofMul ⟨v,hv⟩) = 0 := by
      have hm := LinearMap.mem_range_self (originalLocalCentralLinearProjection D)
        (Additive.ofMul ⟨v,hv⟩)
      rw [hz] at hm
      exact hm
    have hq : QuotientGroup.mk' D.fullCentralizer
        (inclusion (le_componentOrbit D.moduleSubgroup D.maximalLocal) ⟨v,hv⟩) = 1 := he
    have hm : inclusion (le_componentOrbit D.moduleSubgroup D.maximalLocal)
        ⟨v,hv⟩ ∈ (QuotientGroup.mk' D.fullCentralizer).ker := hq
    rw [QuotientGroup.ker_mk'] at hm
    exact hm
  apply D.homogeneous.isIrrPlus.not_le_fixedSpace
    (ReducedNormal.representation (localJoin T L))
  intro v hv
  apply (ReducedNormal.mem_reduced_fixedSpace_iff (localJoin T L)
    (localOrbit T L) le_sup_left v).mpr
  exact hc ((le_componentOrbit D.seed T)
    (mem_map_of_mem (localJoin T L).subtype
      (mem_map_of_mem (ReducedNormal.ModuleGroup (localJoin T L)).subtype hv)))

/-- Every original normalizing element preserves the same local central image. -/
theorem originalLocalCentralLinearProjection_normalizer_invariant
    (τ : Representation (ZMod 2) D.maximalLocal (Additive D.fullCentralQuotient))
    (hτ : ∀ (m : D.maximalLocal) (v : D.fullModule),
      τ m (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
        Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
          ⟨(m : G) * (v : G) * (m : G)⁻¹,
            (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule m.property) v).mp
              v.property⟩))
    (m : D.maximalLocal) (hm : (m : G) ∈ normalizer (D.moduleSubgroup : Set G))
    {v : Additive D.fullCentralQuotient}
    (hv : v ∈ (originalLocalCentralLinearProjection D).range) :
    τ m v ∈ (originalLocalCentralLinearProjection D).range := by
  obtain ⟨u,rfl⟩ := hv
  let w : D.moduleSubgroup := ⟨(m : G) * (u.toMul : G) * (m : G)⁻¹,
    (mem_normalizer_iff.mp hm u.toMul).mp u.toMul.property⟩
  exact ⟨Additive.ofMul w,
    (hτ m (inclusion (le_componentOrbit D.moduleSubgroup D.maximalLocal) u.toMul)).symm⟩

/-- The original Sylow preserves the local central image in any correctly
marked ambient action. This uses no full/local equality. -/
theorem originalLocalCentralLinearProjection_sylow_invariant
    (τ : Representation (ZMod 2) D.maximalLocal (Additive D.fullCentralQuotient))
    (hτ : ∀ (m : D.maximalLocal) (v : D.fullModule),
      τ m (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
        Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
          ⟨(m : G) * (v : G) * (m : G)⁻¹,
            (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule m.property) v).mp
              v.property⟩)) :
    (T : Subgroup G).subgroupOf D.maximalLocal ≤
      Representation.BinaryOffender.subspaceStabilizer τ
        (originalLocalCentralLinearProjection D).range := by
  apply Representation.BinaryOffender.le_subspaceStabilizer
  intro m hm v hv
  exact originalLocalCentralLinearProjection_normalizer_invariant D τ hτ m
    (D.sylow_normalizes_module hm) hv

variable (σ : Representation (ZMod 2) (localOrbit T L) (Additive D.fullCentralQuotient))
  (hσ : ∀ (g : localOrbit T L) (v : D.fullModule),
    σ g (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
      Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
        ⟨(g : G) * (v : G) * (g : G)⁻¹,
          (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule
            ((localOrbit T L).le_normalizer g.property)) v).mp v.property⟩))

/-- The actual local image, with the original orbit action and quotient map. -/
def originalLocalCentralImage : Subrepresentation σ where
  toSubmodule := (originalLocalCentralLinearProjection D).range
  apply_mem_toSubmodule := by
    intro g y hy
    obtain ⟨v,rfl⟩ := hy
    let w : D.moduleSubgroup := ⟨(g : G) * (v.toMul : G) * (g : G)⁻¹,
      (mem_normalizer_iff.mp (D.orbit_normalizes_module g.property) v.toMul).mp
        v.toMul.property⟩
    refine ⟨Additive.ofMul w, ?_⟩
    exact (hσ g (inclusion (le_componentOrbit D.moduleSubgroup D.maximalLocal) v.toMul)).symm

/-- The original local subgroup and its local central kernel realize this image. -/
def originalLocalCentralSection :
    BinaryConjugationSection (localOrbit T L) D.moduleSubgroup
      (D.moduleSubgroup ⊓ centralizer (localOrbit T L : Set G))
      (originalLocalCentralImage D σ hσ).toRepresentation where
  section_le := D.module_le_orbit
  kernel_le := inf_le_left
  normalized := D.orbit_normalizes_module
  coordinates := {
    toFun v := Multiplicative.ofAdd
      ⟨Additive.ofMul (originalLocalCentralProjection D v),
        ⟨Additive.ofMul v,rfl⟩⟩
    map_one' := by apply Subtype.ext; exact (originalLocalCentralProjection D).map_one
    map_mul' x y := by apply Subtype.ext; exact (originalLocalCentralProjection D).map_mul x y }
  onto := by
    intro v
    obtain ⟨u,hu⟩ := v.toAdd.property
    exact ⟨u.toMul,Subtype.ext hu⟩
  kernel_eq := by
    ext v
    constructor
    · intro hv
      have he := congrArg (fun x : Multiplicative
        (originalLocalCentralImage D σ hσ).toSubmodule => x.toAdd.val) hv
      have hm : inclusion (le_componentOrbit D.moduleSubgroup D.maximalLocal) v ∈
          (QuotientGroup.mk' D.fullCentralizer).ker := he
      rw [QuotientGroup.ker_mk'] at hm
      exact ⟨v.property,hm⟩
    · intro hv
      apply Subtype.ext
      change inclusion (le_componentOrbit D.moduleSubgroup D.maximalLocal) v ∈
        (QuotientGroup.mk' D.fullCentralizer).ker
      rw [QuotientGroup.ker_mk']
      exact hv.2
  equivariant g v := by
    apply Subtype.ext
    exact (hσ g (inclusion (le_componentOrbit D.moduleSubgroup D.maximalLocal) v)).symm

include hσ in
/-- A seed equal to the local module gives a genuinely irreducible local image,
without assuming that the local module equals its full conjugate closure. -/
theorem originalLocalCentralImage_irreducible
    (hseed : D.seed = D.moduleSubgroup) :
    (originalLocalCentralImage D σ hσ).toRepresentation.IsIrreducible := by
  have hn : (originalLocalCentralImage D σ hσ).toSubmodule ≠ ⊥ :=
    originalLocalCentralLinearProjection_range_ne_bot D
  let : Nontrivial (originalLocalCentralImage D σ hσ).toSubmodule :=
    (Submodule.nontrivial_iff_ne_bot).mpr hn
  apply (originalLocalCentralSection D σ hσ).irreducible_of_subgroup_minimal
  intro J hJ hnorm
  rcases ReducedNormal.subspaceImage_eq_or_le_centralizer (localJoin T L)
      (localOrbit T L) le_sup_left D.homogeneous.isIrrPlus J
      (by change J ≤ D.seed; rw [hseed]; exact hJ) hnorm with he | hc
  · exact Or.inl (he.trans hseed)
  · exact Or.inr (le_inf hJ hc)

/-- Exhaustion of the literal local image lifts through the full central kernel. -/
theorem source_local_eq_full_of_central_image_eq_top
    (htop : originalLocalCentralImage D σ hσ = ⊤) :
    D.moduleSubgroup = D.fullModule := by
  apply source_local_eq_full_of_central_projection_surjective D
  intro y
  have hy : Additive.ofMul y ∈ (originalLocalCentralImage D σ hσ).toSubmodule := by
    rw [htop]
    trivial
  obtain ⟨v,hv⟩ := hy
  exact ⟨v.toMul,hv⟩

include hσ in
/-- The exact remaining irreducibility premise suffices to recover V = V_M.
It is irreducibility for L₀, not the already established M-irreducibility. -/
theorem source_local_eq_full_of_orbit_quotient_irreducible
    [σ.IsIrreducible] : D.moduleSubgroup = D.fullModule := by
  apply source_local_eq_full_of_central_image_eq_top D σ hσ
  rcases eq_bot_or_eq_top (originalLocalCentralImage D σ hσ) with hb | ht
  · exact (originalLocalCentralLinearProjection_range_ne_bot D
      (congrArg Subrepresentation.toSubmodule hb)).elim
  · exact ht

end CFSG.Quasithin.Chapter10
