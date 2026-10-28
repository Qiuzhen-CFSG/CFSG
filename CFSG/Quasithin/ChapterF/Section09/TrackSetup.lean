module
public import CFSG.Quasithin.ChapterF.Section09.F7Specialization
public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Completion
public import Theory.GroupTheory.ReducedNormal.Equiv
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The original F.9 track

Transfer every F.7 input to G₀=⟨LT,H⟩, with explicit seed and conjugate-span
comparisons back to G. The nontrivial central line makes the seed nontrivial. No parity or
abelian-closure conclusion is included in this construction.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.2(4) and F.9.10,
printed pp.319–321.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section09.Setup
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
  let P₀ := D.T.subtype (show (D.T : Subgroup G) ≤ D.LT ⊔ D.H from le_sup_right.trans le_sup_left)
  have hPi (i : Bool) : (P₀ : Subgroup (G₀ (D := D))) ≤ family (D := D) i := by
    cases i
    · exact fun x hx => mem_sup_right hx
    · exact fun x hx => h.T_le_H hx
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
        (D.T : Subgroup G).subgroupOf D.LT := by
      ext x
      rw [mem_map_equiv]
      rfl
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

/-- F.9's nontrivial point supplies the necessary nontrivial track seed. -/
theorem f7V_ne_bot : h.f7Setup.V ≠ ⊥ := by
  intro he
  have hs : h.f7Setup.seed = ⊥ := by rw [Track.SourceSetup.seed, he, Subgroup.map_bot]
  have hz : D.V = ⊥ := by rw [← h.f7Seed_map, hs, Subgroup.map_bot]
  have hp : D.V₁=⊥ := bot_unique (h.point_lt.le.trans (h.plus_le.trans hz.le))
  have hc:=h.point_card
  rw [hp] at hc
  simp at hc

/-- The last radius fixed by V at γ₀, as in F.9.10. -/
noncomputable def b : ℕ := h.f7Setup.track h.f7V_ne_bot

end Hypothesis
end CFSG.Quasithin.ChapterF.Section09.Setup
