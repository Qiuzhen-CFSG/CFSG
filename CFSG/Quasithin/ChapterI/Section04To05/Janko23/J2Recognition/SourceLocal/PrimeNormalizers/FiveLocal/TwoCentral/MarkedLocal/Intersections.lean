module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.MarkedLocal.Factors
public import Theory.GroupTheory.ComplementNormalizerCentralizer

/-!
# Ambient intersections through the marked extraspecial complement

The split-extension normalizer and centralizer formulas are applied inside
C_G(W.inverter), then mapped through its literal subtype into G. This
converts the core fixed subgroup and the internal A₅ calculations into the
two intersections required in Aschbacher, *Sporadic Groups* (1994), 47.2,
printed p.261. Normality is relative to that centralizer throughout.

The fixed subgroup and internal A₅ inputs remain explicit here. The caller
discharges the internal centralizer using self-centralization of P; the core
fixed subgroup and internal normalizer have independent source producers.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.MarkedLocal
variable {G : Type*} [Group G]
private theorem map_relative_centralizer (H Y : Subgroup G) (hYH : Y ≤ H) :
    (centralizer (Y.subgroupOf H : Set H)).map H.subtype =
      H ⊓ centralizer (Y : Set G) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.property, mem_centralizer_iff.mpr ?_⟩
    intro y hy
    exact congrArg Subtype.val (mem_centralizer_iff.mp ha ⟨y, hYH hy⟩ hy)
  · rintro ⟨hxH, hxC⟩
    refine ⟨⟨x, hxH⟩, mem_centralizer_iff.mpr ?_, rfl⟩
    intro y hy
    exact Subtype.ext (mem_centralizer_iff.mp hxC y hy)

private theorem map_relative_normalizer (H Y : Subgroup G) (hYH : Y ≤ H) :
    (normalizer (Y.subgroupOf H : Set H)).map H.subtype =
      H ⊓ normalizer (Y : Set G) := by
  rw [← subgroupOf_normalizer_eq hYH, subgroupOf_map_subtype, inf_comm]

variable [Finite G] {D : Seed G} {E : Subgroup G}

/-- The two literal local intersections follow from the core fixed group and
from the centralizer and normalizer inside the specified complement. -/
theorem local_intersections (W : RootFiveWitness D E) (Y : Subgroup G)
    (hYL : Y ≤ fiveComponent E) (t : G)
    (hQ : ambientCore W.inverter ⊓ centralizer (Y : Set G) = zpowers W.inverter)
    (hC : fiveComponent E ⊓ centralizer (Y : Set G) = Y)
    (hN : fiveComponent E ⊓ normalizer (Y : Set G) = Y ⊔ zpowers t) :
    (involutionCentralizer W.inverter ⊓ centralizer (Y : Set G) = Y ⊔ zpowers W.inverter) ∧
    (involutionCentralizer W.inverter ⊓ normalizer (Y : Set G) =
      Y ⊔ (zpowers W.inverter ⊔ zpowers t)) := by
  let H := involutionCentralizer W.inverter
  let L := (fiveComponent E).subgroupOf H
  let Q := (ambientCore W.inverter).subgroupOf H
  let YH := Y.subgroupOf H
  have hYH : Y ≤ H := hYL.trans W.component_le
  have hYHL : YH ≤ L := comap_mono hYL
  have hQeq : Q = localCore W.inverter := ambientCore_subgroupOf _
  let : Q.Normal := hQeq ▸ inferInstance
  have hmL : L.map H.subtype = fiveComponent E := map_subgroupOf_eq_of_le W.component_le
  have hmQ : Q.map H.subtype = ambientCore W.inverter :=
    map_subgroupOf_eq_of_le (ambientCore_le _)
  have hc := congrArg (fun A : Subgroup H => A.map H.subtype)
    (Subgroup.IsComplement'.centralizer_eq_sup L Q YH W.complement hYHL)
  have hn := congrArg (fun A : Subgroup H => A.map H.subtype)
    (Subgroup.IsComplement'.normalizer_eq_sup_centralizer L Q YH W.complement hYHL)
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ H.subtype_injective,
    Subgroup.map_inf _ _ _ H.subtype_injective, hmL, hmQ,
    map_relative_centralizer H Y hYH] at hc
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ H.subtype_injective,
    Subgroup.map_inf _ _ _ H.subtype_injective, hmL, hmQ,
    map_relative_centralizer H Y hYH, map_relative_normalizer H Y hYH] at hn
  have hLH : fiveComponent E ⊓ H = fiveComponent E := inf_eq_left.mpr W.component_le
  have hQH : ambientCore W.inverter ⊓ H = ambientCore W.inverter :=
    inf_eq_left.mpr (ambientCore_le _)
  rw [← inf_assoc, ← inf_assoc, hLH, hQH, hC, hQ] at hc
  rw [← inf_assoc, ← inf_assoc, hLH, hQH, hN, hQ] at hn
  refine ⟨hc, hn.trans ?_⟩
  ac_rfl
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.MarkedLocal
