module
public import CFSG.Quasithin.ChapterF.Section08.F7Specialization
public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Completion
public import Theory.GroupTheory.ReducedNormal.Equiv
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The original F.8 track

Transfer every F.7 input to G₀=⟨LT,H⟩, with explicit seed and conjugate-span
comparisons back to G. The nontrivial point makes the seed nontrivial;
G.2.2 puts its H-span in O₂(H), forcing the track to exceed one.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.8.3–5,
printed p.316.
-/
@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section08.Setup
open Section07
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
namespace Hypothesis
variable (h : D.Hypothesis)
include h

abbrev family := Geometry.family D.LT D.H
abbrev G₀ := (D.LT ⊔ D.H : Subgroup G)

/-- The first vertex subgroup is canonically isomorphic to LT. -/
def firstEquiv : D.LT ≃* (family (D := D) false) :=
  (subgroupOfEquivOfLe (show D.LT ≤ D.LT ⊔ D.H from le_sup_left)).symm

omit h [Finite G] in
/-- The first-vertex isomorphism preserves the literal seed. -/
theorem map_seed :
    (D.V.subgroupOf D.LT).map (firstEquiv (D := D)).toMonoidHom =
      (D.V.subgroupOf (D.LT ⊔ D.H)).subgroupOf (family (D := D) false) := by
  ext x
  rw [mem_map_equiv]
  rfl

/-- F.7.6 on the actual generated subgroup. -/
noncomputable def f7Setup : Track.SourceSetup (family (D := D)) := by
  let P := Classical.choose h.sylow
  have hP := Classical.choose_spec h.sylow
  have hTH : D.T ≤ D.H := le_sup_right.trans h.local_le
  have hPG : (P : Subgroup G) ≤ D.LT ⊔ D.H := hP ▸ le_sup_right.trans le_sup_left
  let P₀ := P.subtype hPG
  have hPi (i : Bool) : (P₀ : Subgroup (G₀ (D := D))) ≤ family (D := D) i := by
    cases i
    · exact fun x hx => (show D.T ≤ D.LT from le_sup_right) (hP ▸ hx)
    · exact fun x hx => hTH (hP ▸ hx)
  let S (i : Bool) := P₀.subtype (hPi i)
  let E := firstEquiv (D := D)
  have hV := h.reduced.map_equiv E
  rw [map_seed] at hV
  refine {
    finite := fun _ => inferInstance
    generates := Geometry.family_generates D.LT D.H
    characteristicTwo := ?_
    core_free := ?_
    sylow := S
    same_sylow := ?_
    V := (D.V.subgroupOf (D.LT ⊔ D.H)).subgroupOf (family (D := D) false)
    reduced := hV
    centralizer_eq := ?_ }
  · rw [← map_generalizedFitting_equiv E, h.characteristic_LT, pCore_map_iso]
  · let e : (family (D := D) false ⊔ family (D := D) true : Subgroup (G₀ (D := D))) ≃*
        G₀ (D := D) :=
      (MulEquiv.subgroupCongr (Geometry.family_generates D.LT D.H)).trans (Subgroup.topEquiv)
    apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
    rw [pCore_map_iso]
    exact h.generated_core
  · exact (map_subgroupOf_eq_of_le (hPi false)).trans
      (map_subgroupOf_eq_of_le (hPi true)).symm
  · rw [AmalgamLocalCores.reduced_centralizer_core _ hV]
    apply map_injective (f := E.symm.toMonoidHom) E.symm.injective
    rw [Subgroup.map_inf _ _ _ E.symm.injective, pCore_map_iso]
    have hS : (S false : Subgroup (family (D := D) false)).map E.symm.toMonoidHom =
        D.T.subgroupOf D.LT := by
      ext x
      rw [mem_map_equiv]
      change x.val ∈ (P : Subgroup G) ↔ x.val ∈ D.T
      rw [hP]
    rw [hS, map_centralizer_equiv]
    have hVV : E.symm '' ((D.V.subgroupOf (D.LT ⊔ D.H)).subgroupOf
        (family (D := D) false) : Set (family (D := D) false)) =
        (D.V.subgroupOf D.LT : Set D.LT) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨E x, hx, E.symm_apply_apply x⟩
    rw [hVV, ← AmalgamLocalCores.reduced_centralizer_core _ h.reduced]
    exact h.sylow_centralizer_LT

/-- The track's seed is literally V inside the generated subgroup. -/
theorem f7Seed_eq : h.f7Setup.seed = D.V.subgroupOf (D.LT ⊔ D.H) := by
  change ((D.V.subgroupOf (D.LT ⊔ D.H)).subgroupOf (family (D := D) false)).map
    (family (D := D) false).subtype = _
  exact map_subgroupOf_eq_of_le (comap_mono h.V_le_LT)

/-- Mapping the seed back to the original group recovers V. -/
theorem f7Seed_map : h.f7Setup.seed.map (D.LT ⊔ D.H).subtype = D.V := by
  rw [h.f7Seed_eq, map_subgroupOf_eq_of_le (h.V_le_LT.trans le_sup_left)]

/-- F.8's nontrivial point supplies the necessary nontrivial track seed. -/
theorem f7V_ne_bot : h.f7Setup.V ≠ ⊥ := by
  intro he
  have hs : h.f7Setup.seed = ⊥ := by rw [Track.SourceSetup.seed, he, Subgroup.map_bot]
  have hz : D.V = ⊥ := by rw [← h.f7Seed_map, hs, Subgroup.map_bot]
  exact h.point_ne_bot (eq_bot_iff.mpr (h.point_le.trans hz.le))

/-- The last radius fixed by V at γ₀, as in F.8.4. -/
noncomputable def b : ℕ := h.f7Setup.track h.f7V_ne_bot

/-- The second vertex module maps to the original H-conjugate span U_H. -/
theorem secondModule_map :
    (CriticalPairs.vertexModule (family (D := D)) h.f7Setup.seed
      (Subgroup.CosetGeometry.RankTwo.base (family (D := D)) true)).map
        (D.LT ⊔ D.H).subtype = D.U := by
  rw [CriticalPairs.second_base_module_eq_conjugate_join _ _ h.f7Setup.seed_normalized,
    ← conjugateSpanBy_eq_iSup_conj, map_conjugateSpanBy, h.f7Seed_map]
  rw [show (family (D := D) true).map (D.LT ⊔ D.H).subtype = D.H from
    map_subgroupOf_eq_of_le le_sup_right]
  rfl

/-- The closure is a normal two-subgroup of H. -/
theorem U_le_QH : D.U ≤ D.QH :=
  le_pCoreIn_of_normalizes h.g2.U_isPGroup h.g2.U_le_H
    (le_normalizer_conjugateSpanBy D.V D.H)

/-- The true-core input of F.7.11 follows from G.2.2, on the actual family. -/
theorem f7Seed_le_true_core : h.f7Setup.seed ≤ (family (D := D) true).pCoreIn 2 := by
  apply (map_le_map_iff_of_injective (D.LT ⊔ D.H).subtype_injective).mp
  rw [h.f7Seed_map, ← AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (D.LT ⊔ D.H).subtype_injective,
    show (family (D := D) true).map (D.LT ⊔ D.H).subtype = D.H from
      map_subgroupOf_eq_of_le le_sup_right]
  exact (le_conjugateSpanBy _ _).trans h.U_le_QH

/-- The F.8 track exceeds one, before its oddness is established. -/
theorem one_lt_b : 1 < h.b :=
  CriticalPairs.Completion.one_lt_track_of_true_core _ h.f7Setup h.f7V_ne_bot
    h.f7Seed_le_true_core

end Hypothesis
end CFSG.Quasithin.ChapterF.Section08.Setup
