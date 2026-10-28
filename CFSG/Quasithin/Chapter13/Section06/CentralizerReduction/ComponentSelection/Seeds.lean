module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Notation

/-!
# Propagating seed centralization in the faithful quotient

A normal subgroup of G*_v fixing z has preimage normalized by G_v.
The seed-centralization lemma then makes that preimage centralize U_v.
Its star image is therefore trivial, proving source 13.6.12 without a
classification premise. We also prove the source's replacement observation
for Y_z and identify its moving condition with the actual quotient action.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, combined
1 March 2004 manuscript, printed p.929.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open Subgroup
variable {G : Type*} [Group G]

/-- Quotient images vanish precisely when their ambient subgroups centralize U_v. -/
theorem starImage_eq_bot_iff (z v : G) (H : Subgroup G) (hH : H ≤ Gv v) :
    starImage z v H = ⊥ ↔ H ≤ centralizer (Uv z v : Set G) := by
  rw [starImage, Subgroup.map_eq_bot_iff, starMk_ker]
  constructor
  · intro h x hx
    exact h (show (⟨x, hH hx⟩ : Gv v) ∈ H.subgroupOf (Gv v) from hx)
  · intro h x hx
    exact h hx

/-- The preimage formulation in X_z is equivalent to moving the actual vector z. -/
theorem starPreimage_centralizes_seed_iff (z v : G) (X : Subgroup (Gstar z v)) :
    starPreimage z v X ≤ centralizer ({z} : Set G) ↔
      ∀ x ∈ X, starAction z v x ⟨z, z_mem_Uv z v⟩ = ⟨z, z_mem_Uv z v⟩ := by
  constructor
  · intro h x hx
    obtain ⟨g, rfl⟩ := starMk_surjective z v x
    apply Subtype.ext
    change (g : G) * z * (g : G)⁻¹ = z
    have hg : (g : G) ∈ starPreimage z v X := mem_map.mpr ⟨g, hx, rfl⟩
    have he := mem_centralizer_singleton_iff.mp (h hg)
    rw [he]
    simp [mul_assoc]
  · intro h g hg
    obtain ⟨x, hx, rfl⟩ := hg
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg (fun w : Uv z v => (w : G)) (h _ hx)
    change (x : G) * z * (x : G)⁻¹ = z at he
    exact mul_inv_eq_iff_eq_mul.mp he

/-- Relative normality of the full preimage of a normal quotient subgroup. -/
theorem starPreimage_normalized (z v : G) (X : Subgroup (Gstar z v)) [X.Normal] :
    Gv v ≤ normalizer (starPreimage z v X : Set G) := by
  apply (normal_subgroupOf_iff_le_normalizer (starPreimage_le_Gv z v X)).mp
  change (((X.comap (starMk z v)).map (Gv v).subtype).comap (Gv v).subtype).Normal
  rw [comap_map_eq_self_of_injective (Gv v).subtype_injective]
  infer_instance

/-- A normal subgroup of the faithful action quotient that fixes z is trivial.
Normality propagates seed centralization to the full span U_v. -/
theorem normal_star_subgroup_eq_bot_of_centralizes_seed
    (z v : G) (X : Subgroup (Gstar z v)) [X.Normal]
    (hseed : starPreimage z v X ≤ centralizer ({z} : Set G)) : X = ⊥ := by
  have hline : starPreimage z v X ≤ centralizer (zpowers z : Set G) := by
    simpa only [zpowers_eq_closure, centralizer_closure] using hseed
  have hall : starPreimage z v X ≤ centralizer (Uv z v : Set G) :=
    le_centralizer_conjugateSpanBy_of_normalizes _ _ _
      (starPreimage_normalized z v X) hline
  have himage := (starImage_eq_bot_iff z v (starPreimage z v X)
    (starPreimage_le_Gv z v X)).mpr hall
  rwa [starImage_starPreimage] at himage

/-- Source 13.6.12. This uses the actual faithful quotient; no classification
or solvability hypothesis is required for seed propagation. -/
theorem XFamily_subset_Xz (L T : Subgroup G) (z v : G) :
    XFamily L T z v ⊆ Xz L T z v := by
  intro X hX
  let : X.Normal := hX.2
  exact ⟨hX.1, fun h => hX.1.2.2.1
    (normal_star_subgroup_eq_bot_of_centralizes_seed z v X h)⟩

/-- The source observation that Y_z depends only on K* inside the local family. -/
theorem mem_Yz_of_starImage_eq (L T : Subgroup G) (z v : G)
    {K K₀ : Subgroup G} (hK : K ∈ Yz L T z v)
    (hK₀ : K₀ ∈ Chapter1.LIn (Gv v) (Tv T v))
    (he : starImage z v K₀ = starImage z v K) : K₀ ∈ Yz L T z v := by
  refine ⟨hK₀, ?_, ?_⟩
  · exact (congrArg (fun X : Subgroup (Gstar z v) =>
      Theory.GroupTheory.IsQuasisimple (X ⧸ pCore 2 X)) he).mpr hK.2.1
  · rw [he]
    exact hK.2.2

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
end
