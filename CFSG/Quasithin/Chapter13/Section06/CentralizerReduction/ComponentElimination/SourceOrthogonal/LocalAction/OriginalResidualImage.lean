module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.SourceAction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.SpecificGroups.SymmetricEight.FourBlockSylowResidual

/-!
# The original residual local group in the marked orthogonal action

Restrict the original Sylow subgroup Tᵥ in C_G(v) to the centralizer of z
inside the literal actor KTᵥ. Its image is Sylow in the actual seed
stabilizer. Transport through the chosen natural-section actor gives a
Sylow subgroup of the four-block stabilizer. The prime-to-three residual
of the even block stabilizer, together with that Sylow subgroup, generates
the full block stabilizer.

The final theorem uses exactly the selected source configuration and the
marked natural section; it has no preferred Sylow identification or local
image premise. It discharges the local-image field used by the Thompson
comparison after Aschbacher–Smith 13.6.23, printed p.933 (combined manuscript,
1 March 2004).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction
open ComponentSelection Theory.SpecificGroups.SymmetricEight
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The full actor centralizer maps onto the stabilizer of the original seed. -/
theorem plusImage_seedCentralizer (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    plusImage K L T z v hL hz (plusActor K L T v ⊓ Gv z) =
      seedStabilizer K L T z v hL hz := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mk_mem_seedStabilizer K L T z v hL hz x).mpr hx.2
  · intro ha
    obtain ⟨x, rfl⟩ := plusMk_surjective K L T z v hL hz a
    exact ⟨x, ⟨x.property, (mk_mem_seedStabilizer K L T z v hL hz x).mp ha⟩, rfl⟩

/-- Restriction of the genuine local Sylow subgroup survives the plus quotient. -/
theorem plusImage_Tv_sylow_seedStabilizer (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hKv : K ≤ Gv v)
    (hs : Chapter1.IsSylowIn 2 (Tv T v) (Gv v)) :
    Chapter1.IsSylowIn 2 (plusImage K L T z v hL hz (Tv T v))
      (seedStabilizer K L T z v hL hz) := by
  let A := plusActor K L T v
  have hAv : A ≤ Gv v := by
    change plusActor K L T v ≤ _
    rw [plusActor_eq K L T v hK hLK]
    exact sup_le hKv inf_le_right
  have hTA : Tv T v ≤ A := le_sup_right
  have hres : Chapter1.IsSylowIn 2 (Tv T v) (A ⊓ Gv z) :=
    hs.restrict (le_inf hTA hz) (inf_le_left.trans hAv)
  have hi : Chapter1.IsSylowIn 2 ((Tv T v).subgroupOf A)
      ((A ⊓ Gv z).subgroupOf A) := by
    apply (Chapter1.IsSylowIn.map_iff A.subtype A.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hTA, map_subgroupOf_eq_of_le inf_le_left]
    exact hres
  have hm := Chapter1.Section02.IndexTwo.isSylowIn_map hi (plusMk K L T z v hL hz)
  change Chapter1.IsSylowIn 2 (plusImage K L T z v hL hz (Tv T v))
    (plusImage K L T z v hL hz (plusActor K L T v ⊓ Gv z)) at hm
  rwa [plusImage_seedCentralizer] at hm

open OrthogonalModule
variable {𝒦 : GroupClass} {K L V : Subgroup G} {T : Sylow 2 G} {z v : G}

/-- The literal O^{3′}(C_K(z))Tᵥ has the required four-block image under the
actor already chosen for its natural moved section. -/
theorem source_residual_join_image
    (c : Recognition.SourceAction.Configuration 𝒦 K L V T z v) :
    letI := c.elementary
    ∀ (m : NaturalMovedSection K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed),
      (seedStabilizer K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed).map
        m.actor.toMonoidHom = A6ShadowTwoLocals.fourStabilizer →
      (plusImage K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
        (Source.orthogonalResidual K z ⊔ Tv (T : Subgroup G) v)).map
          m.actor.toMonoidHom = A6ShadowTwoLocals.fourStabilizer := by
  let := c.elementary
  intro m hseed
  have hs := plusImage_Tv_sylow_seedStabilizer K L (T : Subgroup G) z v
    c.lv_invariant c.seed_fixed c.invariant c.lv_le c.selected.1.1 c.sylow
  have ht := Chapter1.Section02.IndexTwo.isSylowIn_map hs m.actor.toMonoidHom
  rw [hseed] at ht
  obtain ⟨S, hS⟩ := ht
  have hX : Source.orthogonalResidual K z ≤ plusActor K L (T : Subgroup G) v :=
    (map_subtype_le _).trans (inf_le_left.trans (K_le_plusActor K L (T : Subgroup G) v))
  rw [plusImage_sup K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
    _ _ hX le_sup_right, Subgroup.map_sup,
    residual_image_of_seed_marking K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
      m.actor m.component_image hseed, ← hS]
  exact FourBlockSylowResidual.residual_sup_sylow S

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction
