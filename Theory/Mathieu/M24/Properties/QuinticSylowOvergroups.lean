module
public import Theory.Mathieu.M24.LocalGeometry.LinearFourPlacement.Orbits
public import Theory.Mathieu.M24.LocalGeometry.OctadCharacteristicTwo
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.ThreeFree
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Three-free Sylow overgroups in the native M₂₄ carrier

A subgroup containing a full Sylow two-subgroup and having order prime to
three cannot act transitively on the actual 24 points. Native orbit geometry
places it in an octad stabilizer. The literal octad action has kernel of
order sixteen and quotient A₈. The exceptional A₈–SL₄(2) equivalence and
binary flag theorem make its image a Sylow subgroup of order 64. The
original subgroup therefore has order 1024.

This supplies the original prime-five exclusion in Aschbacher–Smith
15.1.22(5), printed pp.1099–1100, using the actor of 15.1.21(ii).
The native octad geometry is GLS3 Table 5.3e. All maps use the existing
Witt-design carrier and the actual exceptional model equivalence.
-/

public section
open Subgroup MulAction
open scoped Pointwise
namespace Sporadic.Mathieu.M24QuinticSylow
open M24LocalGeometry M24LocalGeometry.LinearFourCore

private theorem alternating_three_free {α : Type*} [Fintype α] [DecidableEq α]
    (hc : Nat.card α = 8) (P : Sylow 2 (alternatingGroup α))
    (H : Subgroup (alternatingGroup α)) (hPH : (P : Subgroup _) ≤ H)
    (h3 : ¬3 ∣ Nat.card H) : H = P := by
  classical
  let a : α ≃ Fin 8 := Classical.choice (Finite.card_eq.mp (by simpa using hc))
  let e := ((a.altCongrHom.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two).trans
    Atlas.Order20160A8.sl4TwoEquivPSL.symm).trans
      (BinaryLinear.OuterCyclic.slEquivLinear 4)
  have he := BinaryLinear.SylowFlagOvergroups.eq_sylow_of_not_three_dvd
    (P.mapSurjective (f := e.toMonoidHom) e.surjective) (H.map e.toMonoidHom) (map_mono hPH)
    (by rwa [card_map_of_injective e.injective])
  exact map_injective e.injective he

private theorem seed_card_eq (P : Sylow 2 (octadStabilizer seedOctad))
    (H : Subgroup (octadStabilizer seedOctad)) (hPH : (P : Subgroup _) ≤ H)
    (h3 : ¬3 ∣ Nat.card H) : Nat.card H = 1024 := by
  let f := alternatingAction
  have hk : f.ker = (action seedOctad).ker := by
    ext g
    change (alternatingAction g = 1) ↔ action seedOctad g = 1
    simp only [Subtype.ext_iff, alternatingAction_coe, Subgroup.coe_one]
  have hkc : Nat.card f.ker = 16 := hk ▸ kernel_card
  have hkp : IsPGroup 2 f.ker := IsPGroup.of_card (hkc.trans (by decide : 16 = 2^4))
  have hkh : f.ker ≤ H := (hkp.le_sylow_of_normal P).trans hPH
  let Q := P.mapSurjective (f := f) alternatingAction_surjective
  have he : H.map f = (Q : Subgroup _) :=
    alternating_three_free seed_card Q (H.map f) (map_mono hPH)
      (fun hd => h3 (hd.trans (H.card_map_dvd f)))
  let : Nontrivial seedOctad.val := Finite.one_lt_card_iff_nontrivial.mp (by rw [seed_card]; decide)
  have hQ : Nat.card Q = 64 := by
    rw [Sylow.card_eq_multiplicity,nat_card_alternatingGroup,seed_card]
    decide +kernel
  have hh := (f.ker.subgroupOf H).card_mul_index
  change Nat.card (f.ker.subgroupOf H) * f.ker.relIndex H = _ at hh
  rw [relIndex_ker,Nat.card_congr (subgroupOfEquivOfLe hkh).toEquiv,hkc,he,hQ] at hh
  exact hh.symm

/-- An overgroup of a full M₂₄ Sylow two-subgroup, of order prime to three,
is a two-group of order 1024. -/
theorem card_eq_1024 (P : Sylow 2 M24) (H : Subgroup M24)
    (hPH : (P : Subgroup M24) ≤ H) (h3 : ¬3 ∣ Nat.card H) : Nat.card H = 1024 := by
  have ht : ¬IsPretransitive H (Fin 24) := by
    intro ht
    let := ht
    have hd : 24 ∣ Nat.card H := by
      have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H (0 : Fin 24))
      rw [Nat.card_prod,orbit_eq_univ] at hh
      simp only [Nat.card_fin,Nat.card_coe_set_eq,Set.ncard_univ] at hh
      exact ⟨_,hh.symm⟩
    exact h3 ((by decide : 3 ∣ 24).trans hd)
  obtain ⟨O,hO⟩ := LinearFourPlacement.intransitive_sylow_overgroup_le_octadStabilizer P H hPH ht
  obtain ⟨g,hg⟩ := exists_smul_octad_eq O seedOctad
  let e : octadStabilizer O ≃* octadStabilizer seedOctad :=
    MulAction.stabilizerEquivStabilizer (G := M24) hg.symm
  let Q := (P.subtype (hPH.trans hO)).mapSurjective (f := e.toMonoidHom) e.surjective
  let X := (H.subgroupOf (octadStabilizer O)).map e.toMonoidHom
  have hc : Nat.card X = Nat.card H := by
    rw [card_map_of_injective e.injective,Nat.card_congr (subgroupOfEquivOfLe hO).toEquiv]
  have hh := seed_card_eq Q X (map_mono (comap_mono hPH)) (fun hd => h3 (hc ▸ hd))
  exact hc.symm.trans hh

end Sporadic.Mathieu.M24QuinticSylow
