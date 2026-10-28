module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ContainingComponent
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.Index
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Comparing the selected component with its ambient containing component

If K ≤ D and both intrinsic two-core quotients are SL₄(2), the image of K
in D/O₂(D) is the whole quotient by index comparison. The two-core of D lies
in Tᵥ, so it normalizes K. Consequently K is normal in D with two-group
quotient. Perfectness of the containing C-component D forces equality.

This proves the equality step on printed p.933 without confusing D with
the faithful action image K⁺. The genuine 1.2.4 application in the sibling
module constructs D. The two intrinsic model markings remain required;
their construction from the source action markings is a separate obligation.
Once they are available, the final theorem also proves the residual equality
with no assumed subnormality or prime-to-three index for K.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.23(1), printed p.933/PDF p.950.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection
open ComponentSelection Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem eq_top_of_twoCore_quotient_card [Group.IsPerfect G]
    (B : Subgroup G) (hn : pCore 2 G ≤ normalizer (B : Set G))
    (hc : Nat.card (G ⧸ pCore 2 G) ≤ Nat.card (B ⧸ pCore 2 B)) : B = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let f := q.comp B.subtype
  have hfp : IsPGroup 2 f.ker := by
    rw [show f.ker = (pCore 2 G).comap B.subtype by
      change ((QuotientGroup.mk' (pCore 2 G)).comp B.subtype).ker = _
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']]
    exact pCore_isPGroup.comap_of_injective B.subtype B.subtype_injective
  have hfcore : f.ker ≤ pCore 2 B := le_sSup ⟨inferInstance, hfp⟩
  have hrange : f.range = ⊤ := by
    apply eq_top_of_le_card
    apply hc.trans
    rw [← index_eq_card, ← index_ker]
    exact index_antitone hfcore
  have hmap : B.map q = ⊤ := by
    simpa only [f, MonoidHom.range_comp, range_subtype] using hrange
  have hjoin : B ⊔ pCore 2 G = ⊤ := by
    have hh := congrArg (comap q) hmap
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh
  have hN : (⊤ : Subgroup G) ≤ normalizer (B : Set G) := by
    rw [← hjoin]
    exact sup_le B.le_normalizer hn
  let : B.Normal := normalizer_eq_top_iff.mp (top_unique hN)
  let : Group.IsNilpotent (G ⧸ B) :=
    (isPGroup_quotient_of_sup_eq_top B (pCore 2 G) pCore_isPGroup hjoin).isNilpotent
  exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ B)

/-- The two actual SL₄(2) quotients force equality with the containing C-component. -/
theorem eq_containing_component
    (K D T : Subgroup G) (v : G)
    (hD : D ∈ Chapter1.cComponentsIn (Gv v)) (hKD : K ≤ D)
    (hDn : Gv v ≤ normalizer (D : Set G))
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hKn : Tv T v ≤ normalizer (K : Set G))
    (eK : K ⧸ pCore 2 K ≃* SL(4, ZMod 2))
    (eD : D ⧸ pCore 2 D ≃* SL(4, ZMod 2)) : K = D := by
  let : (D.subgroupOf (Gv v)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hD.1).mpr hDn
  have hcore : D.pCoreIn 2 ≤ (Gv v).pCoreIn 2 := by
    have hh := pCoreIn_le_of_subnormal 2
      (inferInstance : (D.subgroupOf (Gv v)).Normal).isSubnormal
    have hm := map_mono (f := (Gv v).subtype) hh
    rw [pCoreIn, map_map] at hm
    have he : (Gv v).subtype.comp (D.subgroupOf (Gv v)).subtype =
      D.subtype.comp (subgroupOfEquivOfLe hD.1).toMonoidHom := rfl
    rw [he, ← map_map, pCore_map_iso] at hm
    exact hm
  obtain ⟨S, hS⟩ := hSyl
  have hcoreT : D.pCoreIn 2 ≤ Tv T v :=
    hcore.trans (hS ▸ pCoreIn_le_sylow (Gv v) S)
  let : Group.IsPerfect D := by
    let := hD.2.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hD.1).toMonoidHom) (subgroupOfEquivOfLe hD.1).surjective
  have hn : pCore 2 D ≤ normalizer (K.subgroupOf D : Set D) := by
    rw [← subgroupOf_normalizer_eq hKD]
    intro x hx
    exact hKn (hcoreT (mem_map.mpr ⟨x, hx, rfl⟩))
  let f : K.subgroupOf D ≃* K := subgroupOfEquivOfLe hKD
  let eq := (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans eK
  have hc : Nat.card (D ⧸ pCore 2 D) ≤
      Nat.card (K.subgroupOf D ⧸ pCore 2 (K.subgroupOf D)) := by
    rw [Nat.card_congr eD.toEquiv, Nat.card_congr eq.toEquiv]
  exact le_antisymm hKD (subgroupOf_eq_top.mp
    (eq_top_of_twoCore_quotient_card (K.subgroupOf D) hn hc))

/-- Apply the source comparison to the literal Gᵥ residual. Equality with
the ambient C-component supplies K's relative subnormality and normality;
the index is derived by the centerless A.3.18 argument. -/
theorem residual_eq_of_containing_component_models
    (K D T : Subgroup G) (v : G)
    (hK : K ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hD : D ∈ Chapter1.cComponentsIn (Gv v)) (hKD : K ≤ D)
    (hDn : Gv v ≤ normalizer (D : Set G))
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hKn : Tv T v ≤ normalizer (K : Set G))
    (eK : K ⧸ pCore 2 K ≃* SL(4, ZMod 2))
    (eD : D ⧸ pCore 2 D ≃* SL(4, ZMod 2))
    (hr : primeRank 3 (Gv v) ≤ 2) :
    K = (primeToResidual 3 (Gv v)).map (Gv v).subtype := by
  have he := eq_containing_component K D T v hD hKD hDn hSyl hKn eK eD
  subst D
  exact component_eq_primeToResidual_of_ambient_component K T v hK hD.2 hDn eK hr

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection
