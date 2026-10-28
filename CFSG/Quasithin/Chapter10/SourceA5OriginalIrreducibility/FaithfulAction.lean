module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalIrreducibility.CanonicalQuotient
public import Theory.Representation.BinaryOffender.ReducedCentralQuotient
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates

/-!
# Faithful original action on the full central quotient

The literal actor Q=M/C_M(V_M) has trivial two-core because V_M is reduced.
Its normal subgroup induced by L₀ fully moves V_M. The central-quotient kernel
lemma therefore shows that the original action on V_M/C_VM(L₀) is faithful.
This is independent of any module classification or A₅-product coordinates.

For a minimal setup the same action is irreducible, and the genuine numerical
bound descends at the unchanged actor Q. This removes the faithfulness premise
in the original product-module classification consumer.
Source: Aschbacher–Smith D.3.4, D.3.9 and 3.2.2–6, pp.194,199–201,579–581.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
local instance faithfulFullElementary (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- Every action with the exact original quotient coordinates is faithful. -/
theorem source_full_central_quotient_faithful
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    ∀ τ : Representation (ZMod 2) (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))
      (Additive D.fullCentralQuotient),
      (∀ (m : D.maximalLocal) (v : D.fullModule),
        τ (q m) (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
          Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
            ⟨(m : G) * (v : G) * (m : G)⁻¹,
              (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule m.property) v).mp
                v.property⟩)) → Function.Injective τ := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let X := (localOrbit T L).subgroupOf M
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let : X.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let K := X.map q
  let : K.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  intro τ hτ
  have hVM : D.fullModule ≤ M := D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer
  have hXM : localOrbit T L ≤ M := (localOrbit T L).le_normalizer
  let eU : U ≃* D.fullModule := subgroupOfEquivOfLe hVM
  let f : Additive U →ₗ[ZMod 2] Additive D.fullCentralQuotient :=
    ((QuotientGroup.mk' D.fullCentralizer).comp eU.toMonoidHom).toAdditive.toZModLinearMap 2
  have he (g) (v : Additive U) : f (ρ g v) = τ g (f v) := by
    obtain ⟨m,rfl⟩ := QuotientGroup.mk'_surjective (centralizer (U : Set M)) g
    change Additive.ofMul (QuotientGroup.mk' D.fullCentralizer (eU (ρ (q m) v).toMul)) =
      τ (q m) (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer (eU v.toMul)))
    rw [hτ]
    congr 2
    apply Subtype.ext
    change (((ρ (q m) v).toMul : U) : G) = (m : G) * (v.toMul : G) * (m : G)⁻¹
    exact congrArg (fun x : M => (x : G)) (NormalElementaryQuotient.representation_apply U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) m v)
  have hk : f.ker = fixedSpace ρ K := by
    ext v
    rw [LinearMap.mem_ker,NormalElementaryQuotient.mem_fixedSpace_image U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) X]
    change eU v.toMul ∈ (QuotientGroup.mk' D.fullCentralizer).ker ↔ _
    rw [QuotientGroup.ker_mk']
    constructor
    · intro hv m hm
      apply Subtype.ext
      exact hv m hm
    · intro hv x hx
      exact congrArg (fun y : M => (y : G)) (hv ⟨x,hXM hx⟩ hx)
  have hwhole : ⁅U,X⁆ = U := by
    apply map_injective M.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVM,map_subgroupOf_eq_of_le hXM]
    exact (D.fullModule_eq_commutator (source_module_nonsolvable_uniqueness D)).symm
  have hmove : subspaceCommutator ρ ⊤ K = ⊤ := by
    rw [←NormalElementaryQuotient.commutatorSpace_eq U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) X]
    ext v
    change (v.toMul : M) ∈ ⁅U,X⁆ ↔ True
    rw [hwhole]
    exact iff_true_intro v.toMul.property
  exact faithful_of_equivariant_reduced_central_quotient ρ τ
    (NormalElementaryQuotient.representation_injective U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _))
    (source_full_module_reduced D).quotient_pCore_eq_bot K f hk he hmove
/-- The minimal source setup supplies the faithful irreducible action and its
original cubic bound on the literal central quotient. -/
theorem source_minimal_full_quotient_faithful_cubic_action
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (hD : D.IsMinimalFullModule)
    (hbound : SourceFullModuleCubicBound D) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    ∃ τ : Representation (ZMod 2) (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))
      (Additive D.fullCentralQuotient),
      Function.Injective τ ∧ τ.IsIrreducible ∧ BinaryOffender.cubicRatio τ ≤ 2 ∧
      (∀ (m : D.maximalLocal) (v : D.fullModule),
        τ (q m) (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
          Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
            ⟨(m : G) * (v : G) * (m : G)⁻¹,
              (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule m.property) v).mp
                v.property⟩)) := by
  dsimp only
  obtain ⟨τ,hi,hbound,hτ⟩ := source_minimal_full_quotient_cubic_action D hD hbound
  exact ⟨τ,source_full_central_quotient_faithful D τ hτ,hi,hbound,hτ⟩

end CFSG.Quasithin.Chapter10
