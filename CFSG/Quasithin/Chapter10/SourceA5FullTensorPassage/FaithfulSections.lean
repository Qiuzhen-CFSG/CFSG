module
public import CFSG.Quasithin.Chapter10.SourceA5FullTensorPassage.CentralCover
public import CFSG.Quasithin.Chapter10.SourceA5OriginalCentralizerPassage
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.NormalType

/-!
# The actual local type in the full A₅ central quotient

When the chosen seed is already the local module, its literal image in
V_M/C_VM(L₀) is simple and preserved by the original Sylow subgroup.
The outer automorphism group of the marked normal A₅ square is a two-group;
inner automorphisms and the relative centralizer preserve every module type.
Consequently the entire full actor preserves this local type. Clifford
generation makes the full central quotient isotypic for that actual image.

This supplies type control for the invariant chief-section construction in
Aschbacher–Smith D.3.9(1), printed pp.199–200. It does not assume V=V_M.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
local instance tensorSectionsElementary (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

local instance tensorSectionsLocalElementary (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 D.moduleSubgroup := D.module_elementary

private theorem pair_outer_two :
    IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) := by
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  exact AutomorphismSquare.outer_isPGroup_two (alternatingGroup.center_eq_bot (by simp))
    Theory.AlternatingFive.outer_isPGroup_two

theorem source_a5_full_quotient_isotypic_of_seed_eq_local
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hseed : D.seed = D.moduleSubgroup) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    let _ : J.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
    ∀ τ : Representation (ZMod 2) (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))
        (Additive D.fullCentralQuotient), τ.IsIrreducible →
      (∀ (m : D.maximalLocal) (v : D.fullModule),
        τ (q m) (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
          Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
            ⟨(m : G) * (v : G) * (m : G)⁻¹,
              (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule m.property) v).mp
                v.property⟩)) →
      ∃ S : Subrepresentation (τ.comp J.subtype),
        S.toSubmodule = (originalLocalCentralLinearProjection D).range ∧
        S.toRepresentation.IsIrreducible ∧
        IsIsotypicOfType (ZMod 2)[J] (Representation.asModule (τ.comp J.subtype)) S.asSubmodule := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let J := ((localOrbit T L).subgroupOf M).map q
  let _ : J.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  intro τ hirr hτ
  let _ := hirr
  let qL := q.comp (inclusion (localOrbit T L).le_normalizer)
  let j : localOrbit T L →* J := qL.codRestrict J (fun x =>
    ⟨inclusion (localOrbit T L).le_normalizer x,x.property,rfl⟩)
  have hj : Function.Surjective j := by
    rintro ⟨x,y,hy,rfl⟩
    exact ⟨⟨y,hy⟩,rfl⟩
  have hτL (g : localOrbit T L) (v : D.fullModule) :=
    hτ (inclusion (localOrbit T L).le_normalizer g) v
  let S0 := originalLocalCentralImage D (τ.comp qL) hτL
  let S : Subrepresentation (τ.comp J.subtype) := {
    toSubmodule := S0.toSubmodule
    apply_mem_toSubmodule x v hv := by
      obtain ⟨g,rfl⟩ := hj x
      exact S0.apply_mem_toSubmodule g hv }
  have hS : S.toRepresentation.IsIrreducible := by
    apply (irreducible_comp_surjective_iff j hj S.toRepresentation).mp
    exact originalLocalCentralImage_irreducible D (τ.comp qL) hτL hseed
  refine ⟨S,rfl,hS,?_⟩
  apply restriction_isotypic_of_typeInertia_top τ J S hS
  obtain ⟨b⟩ := source_a5_original_actor_orbit_model D e hn ht htn
  have ho : IsPGroup 2 (MulAut.Outer J) := pair_outer_two.of_injective
    (MulAut.outerCongr b).toMonoidHom (MulAut.outerCongr b).injective
  let P := D.ambientSylow.mapSurjective (QuotientGroup.mk'_surjective (centralizer (U : Set M)))
  apply typeInertia_eq_top_of_outer_two τ J ho P S
  intro p
  have hp : (p : M ⧸ centralizer (U : Set M)) ∈
      (D.ambientSylow : Subgroup M).map q := p.property
  obtain ⟨m,hm,he⟩ := hp
  have hfix : (normalTypeAction τ J).conjugate p S = S := by
    apply Subrepresentation.toSubmodule_injective
    rw [show ((normalTypeAction τ J).conjugate p S).toSubmodule =
      S.toSubmodule.map (τ p) from conjugateSubrepresentationOrderIso_toSubmodule τ J p S]
    rw [← he]
    exact (subspace_map_eq_iff (τ.comp q) S.toSubmodule m).mpr
      (originalLocalCentralLinearProjection_sylow_invariant D (τ.comp q) hτ hm)
  rw [hfix]
  exact SameModule.refl S
end CFSG.Quasithin.Chapter10
