module
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.OuterInvariantFlags
public import Theory.GroupTheory.EquivariantParabolicLift

/-!
# Node actions on literal binary linear two-core quotients

Conjugation by a subgroup normalizing K acts on K/O₂(K), transported
through the specified binary linear marking. A marked Sylow intersection
gives one full flag. If every actor is inner, every partial flag lifts to
an invariant subgroup. Otherwise an actual outer actor restricts every
invariant proper Sylow overgroup to the three graph-invariant flags.
Kernel containment recovers the original subgroups exactly.

Source: Aschbacher--Smith 15.1.22(3), printed pp.1099--1100.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace BinaryLinear.InvariantNodeActions
open OuterCyclic
variable {G : Type*} [Group G]

/-- The specified quotient map, followed by the binary linear identification. -/
noncomputable def coreFlagMap (K : Subgroup G) {m : ℕ}
    (e : (K ⧸ pCore 2 K) ≃* SL(m+1,ZMod 2)) : K →* LinearGroup (m+1) :=
  (e.trans (slEquivLinear (m+1))).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))

/-- Conjugation on the literal two-core quotient with the same marking. -/
noncomputable def coreFlagAction (K A : Subgroup G)
    (hn : A ≤ normalizer (K : Set G)) {m : ℕ}
    (e : (K ⧸ pCore 2 K) ≃* SL(m+1,ZMod 2)) : A →* MulAut (LinearGroup (m+1)) :=
  (MulAut.congr (e.trans (slEquivLinear (m+1)))).toMonoidHom.comp
    ((quotientAut (pCore 2 K)).comp (K.normalizerMonoidHom.comp (inclusion hn)))

/-- Every model element has an original lift. -/
theorem coreFlagMap_surjective (K : Subgroup G) {m : ℕ}
    (e : (K ⧸ pCore 2 K) ≃* SL(m+1,ZMod 2)) : Function.Surjective (coreFlagMap K e) :=
  (e.trans (slEquivLinear (m+1))).surjective.comp (QuotientGroup.mk'_surjective _)

/-- The comparison kernel is exactly the original two-core. -/
theorem coreFlagMap_ker (K : Subgroup G) {m : ℕ}
    (e : (K ⧸ pCore 2 K) ≃* SL(m+1,ZMod 2)) : (coreFlagMap K e).ker = pCore 2 K := by
  rw [coreFlagMap,MonoidHom.ker_comp_of_injective _ _ (e.trans (slEquivLinear (m+1))).injective,
    QuotientGroup.ker_mk']

/-- The model action agrees with conjugation on every original element. -/
theorem coreFlagAction_equivariant (K A : Subgroup G)
    (hn : A ≤ normalizer (K : Set G)) {m : ℕ}
    (e : (K ⧸ pCore 2 K) ≃* SL(m+1,ZMod 2)) (a : A) (k : K) :
    coreFlagMap K e (K.normalizerMonoidHom (inclusion hn a) k) =
      coreFlagAction K A hn e a (coreFlagMap K e k) := by
  let t := e.trans (slEquivLinear (m+1))
  change t (QuotientGroup.mk' (pCore 2 K) _) =
    t (quotientAut (pCore 2 K) _ (t.symm (t (QuotientGroup.mk' (pCore 2 K) k))))
  rw [t.symm_apply_apply,quotientAut_apply_mk]
  rfl

private theorem lift_image_eq (K : Subgroup G) {m : ℕ}
    (e : (K ⧸ pCore 2 K) ≃* SL(m+1,ZMod 2))
    (P : Subgroup G) (hPK : P ≤ K) (hk : pCore 2 K ≤ P.subgroupOf K) :
    EquivariantLift.lift K (coreFlagMap K e) ((P.subgroupOf K).map (coreFlagMap K e)) = P := by
  exact EquivariantLift.lift_map_subgroupOf K (coreFlagMap K e) P hPK
    (by rw [coreFlagMap_ker]; exact hk)

variable [Finite G]

/-- A common Sylow marking gives either individual invariance of every node,
or three exact possibilities for each invariant proper Sylow overgroup. -/
theorem exists_core_flag_control (K A : Subgroup G)
    (hn : A ≤ normalizer (K : Set G)) (Q : Sylow 2 K)
    (hQ : (Q : Subgroup K).map K.subtype = A ⊓ K)
    {m : ℕ} (hm : m=3 ∨ m=4) (e : (K ⧸ pCore 2 K) ≃* SL(m+1,ZMod 2)) :
    ∃ b : Basis m,
      ((A ⊓ K).subgroupOf K).map (coreFlagMap K e) = cutStabilizer b Set.univ ∧
      (((∀ x : A, coreFlagAction K A hn e x ∈ MulAut.innerSubgroup _) ∧
        ∀ cuts : Set (Fin m), A ≤ normalizer
          (EquivariantLift.lift K (coreFlagMap K e) (cutStabilizer b cuts) : Set G)) ∨
       ((∃ x : A, coreFlagAction K A hn e x ∉ MulAut.innerSubgroup _) ∧
        ∀ P : Subgroup G, A ⊓ K ≤ P → P < K → A ≤ normalizer (P : Set G) →
          P = A ⊓ K ∨
          P = EquivariantLift.lift K (coreFlagMap K e)
            (cutStabilizer b {i | i.val=0 ∨ i.val=m-1}) ∨
          P = EquivariantLift.lift K (coreFlagMap K e)
            (cutStabilizer b {i | i.val=0 ∨ i.val=m-1}ᶜ))) := by
  classical
  let q := coreFlagMap K e
  let α := coreFlagAction K A hn e
  have heq := coreFlagAction_equivariant K A hn e
  have hQS : (Q : Subgroup K) = (A ⊓ K).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [map_subgroupOf_eq_of_le (show A ⊓ K ≤ K from inf_le_right)]
    exact hQ
  let U := Q.mapSurjective (coreFlagMap_surjective K e)
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer U
  have himage : ((A ⊓ K).subgroupOf K).map q = cutStabilizer b Set.univ := by
    rw [←hQS]
    exact hb
  have hnQ : A ≤ normalizer ((A ⊓ K) : Set G) :=
    (le_inf A.le_normalizer hn).trans inf_normalizer_le_normalizer_inf
  have hUi (x : A) : (U : Subgroup (LinearGroup (m+1))).map (α x).toMonoidHom = U := by
    change ((Q : Subgroup K).map q).map (α x).toMonoidHom = (Q : Subgroup K).map q
    rw [hQS]
    exact EquivariantLift.map_invariant K q hn α heq hnQ x
  have hkQ : pCore 2 K ≤ (A ⊓ K).subgroupOf K :=
    hQS ▸ pCore_isPGroup.le_sylow_of_normal Q
  refine ⟨b,himage,?_⟩
  by_cases hi : ∀ x : A, α x ∈ MulAut.innerSubgroup _
  · refine Or.inl ⟨hi,fun cuts => ?_⟩
    apply EquivariantLift.normalizes_lift K q hn α heq
    intro x
    obtain ⟨g,hg⟩ := hi x
    have hu := hUi x
    rw [←hg,hb] at hu
    rw [←hg]
    exact inner_fixes_cutStabilizer b g hu cuts
  · push Not at hi
    obtain ⟨x,hx⟩ := hi
    refine Or.inr ⟨⟨x,hx⟩,fun P hSP hPK hPN => ?_⟩
    have hkP : pCore 2 K ≤ P.subgroupOf K :=
      hkQ.trans (subgroupOf_mono K hSP)
    have hlift := lift_image_eq K e P hPK.le hkP
    have hnot : (P.subgroupOf K).map q ≠ ⊤ := by
      intro hh
      rw [hh,EquivariantLift.lift_top] at hlift
      exact hPK.ne hlift.symm
    have hUP : (U : Subgroup (LinearGroup (m+1))) ≤ (P.subgroupOf K).map q := by
      change (Q : Subgroup K).map q ≤ _
      rw [hQS]
      exact map_mono (subgroupOf_mono K hSP)
    have hc := outer_invariant_overgroup hm U b hb (α x) hx (hUi x)
      ((P.subgroupOf K).map q) hUP hnot
      (EquivariantLift.map_invariant K q hn α heq hPN x)
    rcases hc with hc | hc | hc
    · apply Or.inl
      have hS := lift_image_eq K e (A ⊓ K) inf_le_right hkQ
      rw [←hQS] at hS
      exact hlift.symm.trans ((congrArg (EquivariantLift.lift K q) hc).trans hS)
    · exact Or.inr (Or.inl (hlift.symm.trans (congrArg (EquivariantLift.lift K q) hc)))
    · exact Or.inr (Or.inr (hlift.symm.trans (congrArg (EquivariantLift.lift K q) hc)))
end BinaryLinear.InvariantNodeActions
