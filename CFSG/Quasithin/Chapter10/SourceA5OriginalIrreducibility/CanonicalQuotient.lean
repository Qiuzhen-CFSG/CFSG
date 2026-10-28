module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalIrreducibility.MaximalAction
public import CFSG.Quasithin.Chapter10.SourceA5ModuleQuadraticBound
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryOffender.CubicSurjection

/-!
# The original minimal module at its canonical faithful actor

The full-module action descends to the literal quotient M/C_M(V_M).
Its projection onto V_M/C_{V_M}(L₀) is equivariant for this same actor,
so the original cubic bound passes to the central quotient. Minimality
of V_M supplies irreducibility under M and hence under the quotient.
No faithfulness of the central quotient is asserted by this transport.

This is the actual numerical input to the A₅-specialized D.3.9 reduction,
with the source quotient maps retained throughout.
Source: Aschbacher–Smith, D.3.9 and 3.2.5–6, printed pp.199–201, 580–581.
-/

public noncomputable section


open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

local instance cubicFullElementary (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The full central-quotient action factors through the original action kernel. -/
theorem source_full_quotient_action_descent
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (σ : Representation (ZMod 2) D.maximalLocal (Additive D.fullCentralQuotient))
    (hσ : ∀ (g : D.maximalLocal) (v : D.fullModule),
      σ g (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
        Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
          ⟨(g : G) * (v : G) * (g : G)⁻¹,
            (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule g.property) v).mp
              v.property⟩)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    ∃ τ : Representation (ZMod 2) (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))
      (Additive D.fullCentralQuotient), τ.comp q = σ := by
  dsimp only
  let U := D.fullModule.subgroupOf D.maximalLocal
  let := (source_full_module_reduced D).normal
  let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
  have hk : q.ker ≤ σ.asGroupHom.ker := by
    intro m hm
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective D.fullCentralizer v.toMul
    change σ m (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer w)) =
      Additive.ofMul (QuotientGroup.mk' D.fullCentralizer w)
    rw [hσ]
    congr 2
    apply Subtype.ext
    have hc : m ∈ centralizer (U : Set D.maximalLocal) := (QuotientGroup.eq_one_iff m).mp hm
    let wM : D.maximalLocal := ⟨w,D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer w.property⟩
    have he := congrArg Subtype.val (hc wM w.property)
    change (w : G) * (m : G) = (m : G) * (w : G) at he
    change (m : G) * (w : G) * (m : G)⁻¹ = (w : G)
    rw [← he,mul_inv_cancel_right]
  let f := q.liftOfSurjective (QuotientGroup.mk'_surjective _) ⟨σ.asGroupHom,hk⟩
  let τ : Representation (ZMod 2) _ (Additive D.fullCentralQuotient) :=
    (Units.coeHom _).comp f
  refine ⟨τ,?_⟩
  ext m v
  have he := q.liftOfRightInverse_comp_apply
    (Function.surjInv (QuotientGroup.mk'_surjective _))
    (Function.rightInverse_surjInv (QuotientGroup.mk'_surjective _)) ⟨σ.asGroupHom,hk⟩ m
  exact congrArg (fun u : (Module.End (ZMod 2) (Additive D.fullCentralQuotient))ˣ => u.val v) he

/-- The original full-module cubic bound passes to its central quotient at the same actor. -/
theorem source_full_quotient_cubic_bound
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (σ : Representation (ZMod 2) D.maximalLocal (Additive D.fullCentralQuotient))
    (hσ : ∀ (g : D.maximalLocal) (v : D.fullModule),
      σ g (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
        Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
          ⟨(g : G) * (v : G) * (g : G)⁻¹,
            (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule g.property) v).mp
              v.property⟩)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    ∃ τ : Representation (ZMod 2) (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))
      (Additive D.fullCentralQuotient),
      τ.comp q = σ ∧ (SourceFullModuleCubicBound D → BinaryOffender.cubicRatio τ ≤ 2) := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  obtain ⟨τ,hτ⟩ := source_full_quotient_action_descent D σ hσ
  refine ⟨τ,hτ,?_⟩
  intro hbound
  have hVM : D.fullModule ≤ M := D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer
  let eU : U ≃* D.fullModule := subgroupOfEquivOfLe hVM
  let f : Additive U →ₗ[ZMod 2] Additive D.fullCentralQuotient :=
    ((QuotientGroup.mk' D.fullCentralizer).comp eU.toMonoidHom).toAdditive.toZModLinearMap 2
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨v,hv⟩ := QuotientGroup.mk'_surjective D.fullCentralizer w.toMul
    refine ⟨Additive.ofMul (eU.symm v),?_⟩
    change QuotientGroup.mk' D.fullCentralizer (eU (eU.symm v)) = w.toMul
    rw [eU.apply_symm_apply,hv]
  have he (g) (v : Additive U) : f (ρ g v) = τ g (f v) := by
    obtain ⟨m,rfl⟩ := QuotientGroup.mk'_surjective (centralizer (U : Set M)) g
    have hτm : τ (q m) = σ m := congrArg (fun r => r m) hτ
    rw [hτm]
    change Additive.ofMul (QuotientGroup.mk' D.fullCentralizer (eU (ρ (q m) v).toMul)) =
      σ m (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer (eU v.toMul)))
    rw [hσ]
    congr 2
    apply Subtype.ext
    change (((ρ (q m) v).toMul : U) : G) = (m : G) * (v.toMul : G) * (m : G)⁻¹
    exact congrArg (fun x : M => (x : G)) (NormalElementaryQuotient.representation_apply U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) m v)
  exact BinaryOffender.cubicRatio_le_nat_of_equivariant_surjection ρ τ f hf he 2 hbound

/-- The literal central quotient of a minimal setup is irreducible and has the
original cubic bound under M/C_M(V_M). -/
theorem source_minimal_full_quotient_cubic_action
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (hD : D.IsMinimalFullModule)
    (hbound : SourceFullModuleCubicBound D) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    ∃ τ : Representation (ZMod 2) (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))
      (Additive D.fullCentralQuotient),
      τ.IsIrreducible ∧ BinaryOffender.cubicRatio τ ≤ 2 ∧
      (∀ (m : D.maximalLocal) (v : D.fullModule),
        τ (q m) (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
          Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
            ⟨(m : G) * (v : G) * (m : G)⁻¹,
              (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule m.property) v).mp
                v.property⟩)) := by
  dsimp only
  let U := D.fullModule.subgroupOf D.maximalLocal
  let := (source_full_module_reduced D).normal
  let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
  obtain ⟨σ,hi,_,hσ⟩ := source_minimal_full_quotient_action D hD
  obtain ⟨τ,hτ,hq⟩ := source_full_quotient_cubic_bound D σ hσ
  refine ⟨τ,?_,hq hbound,?_⟩
  · apply (irreducible_comp_surjective_iff q (QuotientGroup.mk'_surjective _) τ).mp
    rw [hτ]
    exact hi
  · intro m v
    have he : τ (q m) = σ m := congrArg (fun r => r m) hτ
    rw [he]
    exact hσ m v

end CFSG.Quasithin.Chapter10
