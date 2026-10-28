module

public import CFSG.Quasithin.ChapterE.Section01.MinimalStructure.Frattini
public import Theory.GroupTheory.SolvableRadical.Transport

/-!
# Two-closed radicals of minimal supplements

If the radical of the quotient image is 2-closed, its normal Sylow
subgroup lies in the intrinsic two-core of that image. Thus the Sylow
intersection with the radical upstairs lies in the Sylow intersection
with the preimage of that two-core. The latter is normal by the Frattini
argument for minimal supplements. Intersecting with the radical gives
its normal Sylow subgroup. This proof does not require kernel solvability.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
the second conclusion of E.1.10(4), printed p.211.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE
open Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem two_subgroup_le_core {N P : Subgroup G} [N.Normal]
    (hN : IsTwoClosed N) (hP : IsPGroup 2 P) (hPN : P ≤ N) : P ≤ pCore 2 G := by
  obtain ⟨S, hS⟩ := hN
  let : (S : Subgroup N).Characteristic := S.characteristic_of_normal hS
  have hsn : ((S : Subgroup N).map N.subtype).Normal := inferInstance
  have hle : P.subgroupOf N ≤ (S : Subgroup N) := by
    let := hS
    have hpg := hP.comap_of_injective N.subtype N.subtype_injective
    -- The normal Sylow subgroup contains every two-subgroup.
    obtain ⟨U, hU⟩ := hpg.exists_le_sylow
    have hSU : S = U := by
      apply Sylow.ext
      exact (S.is_maximal' U.isPGroup' (S.isPGroup'.le_sylow_of_normal U)).symm
    simpa only [hSU, subgroupOf] using hU
  calc
    P = (P.subgroupOf N).map N.subtype := (map_subgroupOf_eq_of_le hPN).symm
    _ ≤ (S : Subgroup N).map N.subtype := map_mono hle
    _ ≤ pCore 2 G := le_sSup ⟨hsn, S.isPGroup'.map N.subtype⟩

/-- The radical conclusion of E.1.10(4), from the corresponding hypothesis
on the actual quotient image alone. -/
theorem IsMinimalSupplement.twoClosed_solvableRadical (T : Sylow 2 G) {X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K)
    (hr : IsTwoClosed (solvableRadical (K.map (QuotientGroup.mk' Y)))) :
    IsTwoClosed (solvableRadical K) := by
  let f := (QuotientGroup.mk' Y).subgroupMap K
  have hf := (QuotientGroup.mk' Y).subgroupMap_surjective K
  let R := solvableRadical K
  let S : Sylow 2 K := T.subtype h.1.1
  let Z := (pCore 2 (K.map (QuotientGroup.mk' Y))).comap f
  let B := (S : Subgroup K) ⊓ R
  have hBZ : B ≤ Z := by
    apply map_le_iff_le_comap.mp
    exact two_subgroup_le_core hr (S.isPGroup'.to_inf_left.map f)
      ((map_mono inf_le_right).trans (map_solvableRadical_le_of_surjective f hf))
  have he : B = ((S : Subgroup K) ⊓ Z) ⊓ R := by
    apply le_antisymm (le_inf (le_inf inf_le_left hBZ) inf_le_right)
    exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hn : ((S : Subgroup K) ⊓ Z).Normal := by
    simpa only [S, Sylow.coe_subtype, Z, f] using
      h.normal_inf_preimage T (pCore 2 (K.map (QuotientGroup.mk' Y))) pCore_isPGroup
  have hB : B.Normal := by rw [he]; infer_instance
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal R
  have hp : ((P : Subgroup R).map R.subtype).Normal := by
    simpa only [hP, subgroupOf_map_subtype] using hB
  exact ⟨P, hp.of_map_subtype⟩

end CFSG.Quasithin.ChapterE
