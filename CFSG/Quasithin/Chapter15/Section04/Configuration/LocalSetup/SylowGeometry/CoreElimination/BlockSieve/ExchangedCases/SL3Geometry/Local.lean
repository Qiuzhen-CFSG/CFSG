module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.Actions
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Mathlib.GroupTheory.Nilpotent

/-!
# The local Sylow subgroup and the fifth SL₃ alternative

If R lies in a Sylow subgroup P and normalizes a subnormal L, then
P ∩ LR is Sylow in LR. Restrict P to L and use the coprime index formula
for a normalized product. Applied to the selected component, this gives a
specific local Sylow subgroup containing the source radical and seed.

The seed is in its omega center. Thus the central-omega clause of C.1.34(5)
would put the whole local group in the seed centralizer, a two-group.
This contradicts the nonsolvability of the selected C-component.
No assertion that R itself is Sylow is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.34(5),
printed p.137, and the proof of 15.4.20, p.1164.
-/

@[expose] public section

open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Restrict the supplied Sylow to the product with a normalized subnormal subgroup. -/
theorem local_sylow (P : Sylow 2 G) (L R : Subgroup G)
    (hL : L.IsSubnormal) (hR : R ≤ (P : Subgroup G))
    (hn : R ≤ normalizer (L : Set G)) :
    ∃ S : Sylow 2 (L ⊔ R : Subgroup G),
      (S : Subgroup (L ⊔ R : Subgroup G)).map (L ⊔ R : Subgroup G).subtype =
        (P : Subgroup G) ⊓ (L ⊔ R) := by
  let D := L ⊔ R
  let T : Subgroup G := (P : Subgroup G) ⊓ D
  have hDT : L ⊔ T = D := le_antisymm (sup_le le_sup_left inf_le_right)
    (sup_le le_sup_left (le_sup_right.trans' (le_inf hR le_sup_right)))
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_subnormal L hL
  have hQT : (Q : Subgroup L).map L.subtype ≤ T := by
    rw [hQ]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hx, (le_sup_left : L ≤ L ⊔ R) x.property⟩
  obtain ⟨S, hS⟩ := (P.isPGroup'.to_le (inf_le_left : T ≤ (P : Subgroup G))).exists_sylow_sup_of_coprime_index
    L T (inf_le_right.trans (sup_le L.le_normalizer hn)) (Q : Subgroup L) Q.not_dvd_index hQT
  let e : (L ⊔ T : Subgroup G) ≃* D := MulEquiv.subgroupCongr hDT
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((S : Subgroup (L ⊔ T : Subgroup G)).map e.toMonoidHom).map D.subtype = T
  rw [map_map]
  exact hS

variable {d : Source.Geometry G} {i j : Bool} {H U K K₁ : Subgroup G} {r : G}

/-- The actual local Sylow, with its image in H retained. -/
theorem source_local_sylow (h : Input d i j H U K) (s : Selected H U K K₁ r)
    (hn : (sourceRadical d U).subgroupOf H ≤ normalizer (K₁.subgroupOf H : Set H)) :
    ∃ S : Sylow 2 (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H : Subgroup H),
      (S : Subgroup _).map (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H : Subgroup H).subtype =
        (h.placed.sylow : Subgroup H) ⊓ (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H) := by
  apply local_sylow h.placed.sylow _ _ s.relative_subnormal _ hn
  intro x hx
  have hxU := h.radical_le_sylow hx
  rw [← h.placed.sylow_image] at hxU
  obtain ⟨y, hy, he⟩ := hxU
  exact (Subtype.ext he : y = x) ▸ hy

/-- The source seed belongs to the omega center of this local Sylow subgroup. -/
theorem source_seed_le_local_omega (h : Input d i j H U K)
    (L : Subgroup H)
    (S : Sylow 2 (L ⊔ (sourceRadical d U).subgroupOf H : Subgroup H))
    (hS : (S : Subgroup _).map (L ⊔ (sourceRadical d U).subgroupOf H : Subgroup H).subtype =
      (h.placed.sylow : Subgroup H) ⊓ (L ⊔ (sourceRadical d U).subgroupOf H)) :
    (d.Z.subgroupOf H).subgroupOf (L ⊔ (sourceRadical d U).subgroupOf H) ≤
      omegaOneCenterAmbient (S : Subgroup _) := by
  intro z hz
  have hZ := (mem_omegaOneCenterAmbient_iff _ _).mp (h.seed_inputs.2.2.2.1 hz)
  apply (mem_omegaOneCenterAmbient_iff _ _).mpr
  refine ⟨?_, Subtype.ext hZ.2.1, ?_⟩
  · have hzmap : (z : H) ∈ (S : Subgroup _).map (L ⊔ (sourceRadical d U).subgroupOf H : Subgroup H).subtype := by
      rw [hS]
      exact ⟨hZ.1, z.property⟩
    obtain ⟨y, hy, he⟩ := hzmap
    exact (Subtype.ext he : y = z) ▸ hy
  · intro x hx
    have hxP : (x : H) ∈ (h.placed.sylow : Subgroup H) := by
      have hh := mem_map_of_mem (L ⊔ (sourceRadical d U).subgroupOf H : Subgroup H).subtype hx
      rw [hS] at hh
      exact hh.1
    exact Subtype.ext (hZ.2.2 x hxP)

/-- C.1.34(5)'s central-omega clause is impossible for the selected component. -/
theorem not_source_local_central_omega (h : Input d i j H U K)
    (s : Selected H U K K₁ r)
    (S : Sylow 2 (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H : Subgroup H))
    (hS : (S : Subgroup _).map (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H : Subgroup H).subtype =
      (h.placed.sylow : Subgroup H) ⊓ (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H))
    (hc : omegaOneCenterAmbient (S : Subgroup
      (K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H : Subgroup H)) ≤ center _) : False := by
  let D : Subgroup H := K₁.subgroupOf H ⊔ (sourceRadical d U).subgroupOf H
  have hZR : d.Z.subgroupOf H ≤ (sourceRadical d U).subgroupOf H :=
    fun _ hz => h.seed_le_radical hz
  have hZD : d.Z.subgroupOf H ≤ D := hZR.trans le_sup_right
  have hZC := (source_seed_le_local_omega h (K₁.subgroupOf H) S hS).trans hc
  have hDC : D ≤ centralizer (d.Z.subgroupOf H : Set H) := by
    intro x hx z hz
    exact (congrArg Subtype.val ((mem_center_iff.mp (hZC (show
      (⟨z, hZD hz⟩ : D) ∈ (d.Z.subgroupOf H).subgroupOf D from hz))) ⟨x, hx⟩)).symm
  have hLP : K₁.subgroupOf H ≤ (h.placed.sylow : Subgroup H) := by
    rw [← h.seed_inputs.2.2.1]
    exact le_sup_left.trans hDC
  have hp := h.placed.sylow.isPGroup'.to_le hLP
  let : Group.IsNilpotent (K₁.subgroupOf H) := hp.isNilpotent
  exact s.component.2.not_isSolvable inferInstance

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry
