module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Geometry
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Projection
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.CentralizerGeometry

/-!
# Reduction of the binary degree-four intersection

Put K = M ∩ L, regarded as a subgroup of L. The local hypotheses make K
proper and force it to contain the centralizer of the involution projection.
Only N_S(L), rather than all of S, is needed to preserve K under conjugation.

The geometric reduction uses two explicit inputs: every proper overgroup of
the centralizer is contained in its line or hyperplane stabilizer, and a
dimension-changing automorphism fixing the projection exchanges these two
stabilizers. Invariance then puts K in both stabilizers, whose intersection
is the centralizer by the rank-one calculation.

The cover and exchange remain hypotheses of the reduction below. This module
does not establish either model fact or claim the completed source theorem.
It isolates their application in Aschbacher–Smith 2.3.9(7)(g), combined
manuscript of 1 March 2004, printed pp.525–526 (`refs/quasithin.pdf`).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.FourIntersection

open Subgroup

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The intrinsic intersection is invariant under the actual conjugation
action of N_S(L), even when S permutes the components of H. -/
theorem intersection_map_normalizer (h : LocalSetup H L M S z) {s : G}
    (hsS : s ∈ (S : Subgroup H).map H.subtype)
    (hsL : s ∈ normalizer (L : Set G)) :
    (M.subgroupOf L).map (L.normalizerMonoidHom ⟨s, hsL⟩).toMonoidHom =
      M.subgroupOf L := by
  let α := L.normalizerMonoidHom ⟨s, hsL⟩
  have hsM := h.sylow_le hsS
  have hinv (x : L) : x ∈ M.subgroupOf L ↔ α x ∈ M.subgroupOf L := by
    change (x : G) ∈ M ↔ s * (x : G) * s⁻¹ ∈ M
    exact mem_normalizer_iff.mp (M.le_normalizer hsM) x
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (hinv x).mp hx
  · intro x hx
    refine ⟨α.symm x, ?_, α.apply_symm_apply x⟩
    exact (hinv (α.symm x)).mpr (by simpa using hx)

/-- Properness is relative to L and follows from the source's L not ≤ M. -/
theorem intersection_ne_top (h : LocalSetup H L M S z) : M.subgroupOf L ≠ ⊤ := by
  intro he
  apply h.outside
  intro x hx
  exact show (⟨x, hx⟩ : L) ∈ M.subgroupOf L from he ▸ mem_top _

/-- The lower containment, expressed intrinsically in the component. -/
theorem centralizer_le_intersection (h : LocalSetup H L M S z) {t : L}
    (ht : IsConjugationProjection L z t) :
    centralizer ({t} : Set L) ≤ M.subgroupOf L := by
  intro x hx
  exact (projection_centralizer_le_intersection ht h.centralizer_le
    ⟨x.property, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx))⟩).2

/-- Conditional assembly of the degree-four intersection. The two geometric
premises concern the actual transported parabolics. They must be proved by
the model calculation before applying this as the source conclusion. -/
theorem intersection_eq_of_geometric_inputs (h : LocalSetup H L M S z)
    (e : L ≃* PSL 4) {t : L} (ht : IsConjugationProjection L z t)
    (c : TransvectionCoordinates e t)
    (hd : NontrivialDynkinAction e ((S : Subgroup H).map H.subtype))
    (hcover : ∀ K : Subgroup L, centralizer ({t} : Set L) ≤ K → K ≠ ⊤ →
      K ≤ subspaceStabilizer e c.line ∨ K ≤ subspaceStabilizer e c.hyperplane)
    (hexchange : ∀ α : MulAut L, α t = t → ∀ W W' : Space 4,
      W ≠ ⊥ → W ≠ ⊤ → W' ≠ ⊥ → W' ≠ ⊤ →
      Module.finrank (ZMod 2) W ≠ Module.finrank (ZMod 2) W' →
      (subspaceStabilizer e W).map α.toMonoidHom = subspaceStabilizer e W' →
      (subspaceStabilizer e c.line).map α.toMonoidHom =
          subspaceStabilizer e c.hyperplane ∧
        (subspaceStabilizer e c.hyperplane).map α.toMonoidHom =
          subspaceStabilizer e c.line) :
    L ⊓ M = L ⊓ centralizer ({(t : G)} : Set G) := by
  obtain ⟨s, hsS, hsL, W, W', hW0, hW1, hW'0, hW'1, hdim, hmap⟩ := hd
  let α := L.normalizerMonoidHom ⟨s, hsL⟩
  have hfix : α t = t := by
    apply Subtype.ext
    change s * (t : G) * s⁻¹ = (t : G)
    rw [projection_centralizes_normalizer h e ht hsS hsL, mul_inv_cancel_right]
  have hK : (M.subgroupOf L).map α.toMonoidHom = M.subgroupOf L :=
    intersection_map_normalizer h hsS hsL
  obtain ⟨hPQ, hQP⟩ := hexchange α hfix W W' hW0 hW1 hW'0 hW'1 hdim hmap
  have hupper : M.subgroupOf L ≤ centralizer ({t} : Set L) := by
    rw [c.centralizer_eq]
    rcases hcover _ (centralizer_le_intersection h ht) (intersection_ne_top h) with hp | hq
    · exact le_inf hp
        (by simpa only [hK, hPQ] using map_mono (f := α.toMonoidHom) hp)
    · exact le_inf
        (by simpa only [hK, hQP] using map_mono (f := α.toMonoidHom) hq) hq
  apply le_antisymm
  · rintro x ⟨hxL, hxM⟩
    exact ⟨hxL, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp
        (hupper (show (⟨x, hxL⟩ : L) ∈ M.subgroupOf L from hxM))))⟩
  · exact projection_centralizer_le_intersection ht h.centralizer_le

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.FourIntersection

end
