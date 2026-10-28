module

public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.ResidualCore
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallAutomizer
public import CFSG.Quasithin.ChapterE.Section02.SolvableStructure.CubicActors

/-!
# Placement of the small pair core in the solvable ambient core

The quaternion core of the actual original witness lies in its own two-residual.
The image of that residual in the ambient two-core quotient is a three-group,
whereas the pair core has two-power order. Its image is therefore trivial.
The solvable source theorem supplies the three-group condition directly from
E.2.1, and restriction of the ambient two-core gives the exact intersection
of the marked module with the pair core.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, E.2.17,
opening of the solvable case, printed p.229. All maps and marked subgroups
remain those of the source witness.
-/

public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
open TwoConjugate
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]
  {S : Sylow 2 H} {N W U : Subgroup H} [IsElementaryAbelian 2 W] {n : ℕ}

theorem OriginalWitness.small_core_le_residual (w : OriginalWitness S N W n)
    (hWS : W ≤ (S : Subgroup H))
    (hSW : (S : Subgroup H) ≤ normalizer (W : Set H))
    (hcore : W ≤ N.pCoreIn 2) (hn : normalizer (W : Set H) ≤ N)
    (hfit : generalizedFitting H = pCore 2 H) (hW : Nat.card W = 16)
    (hSU : (S : Subgroup H) ≤ U) (hU : U ≤ normalizer (W : Set H))
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (W : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U W hU q hq hk)) :
    pCore 2 w.pair.subgroup ≤ pResidual 2 w.pair.subgroup := by
  let h := w.pair.hypotheses hWS hSW hcore hn
  let hSU' := w.pair.sylow_eq.le.trans (inf_le_left.trans hSU)
  let e := subgroupOfEquivOfLe w.pair.le
  let ρ := DihedralCubic.representation U W hU q hq hk
  let f := DihedralCubic.actorMap h hSU' q
  have hp := w.pair.proper_of_quotient_card_ne_one hn w.model.card_ne_one
  have hf := w.pair.fitting hSW hfit
  have ha : ∀ (a : A (W.subgroupOf w.pair.subgroup) (N.subgroupOf w.pair.subgroup) w.pair.conjugator)
      (v : W.subgroupOf w.pair.subgroup),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : w.pair.subgroup) =
        (a : w.pair.subgroup) * v * (a : w.pair.subgroup)⁻¹ := by
    intro a v
    apply Subtype.ext
    change ((ρ (q (DihedralCubic.actorIn h hSU' a)) (Additive.ofMul (e v))).toMul : H) =
      ((a : w.pair.subgroup) : H) * ((v : w.pair.subgroup) : H) *
        ((a : w.pair.subgroup) : H)⁻¹
    rw [DihedralCubic.representation_apply]
    rfl
  have hρ := DihedralCubic.representation_injective U W hU q hq hk
  have hcard := w.model.star_card_two h hp hf ((Nat.card_congr e.toEquiv).trans hW)
    e ρ hρ f ha hD hratio
  have hc := h.small_automizer_quaternion_core hp hf hcard
    ((Nat.card_congr e.toEquiv).trans hW) e ρ hρ f ha hD hratio
  let := hc.2.1
  have hle := h.P_le_twoResidual_of_extraspecial hc.1
  rwa [(h.odd_dihedral hcard).1] at hle

theorem OriginalWitness.small_core_le_twoCore_of_cubic_residual
    (w : OriginalWitness S N W n)
    (hWS : W ≤ (S : Subgroup H))
    (hSW : (S : Subgroup H) ≤ normalizer (W : Set H))
    (hcore : W ≤ N.pCoreIn 2) (hn : normalizer (W : Set H) ≤ N)
    (hfit : generalizedFitting H = pCore 2 H) (hW : Nat.card W = 16)
    (hSU : (S : Subgroup H) ≤ U) (hU : U ≤ normalizer (W : Set H))
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (W : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U W hU q hq hk))
    (hR : IsPGroup 3 (pResidual 2 (H ⧸ pCore 2 H))) :
    w.pair.subgroup.pCoreIn 2 ≤ pCore 2 H := by
  let π := QuotientGroup.mk' (pCore 2 H)
  have hle := w.small_core_le_residual hWS hSW hcore hn hfit hW hSU hU q hq hk hD hratio
  have hi : (w.pair.subgroup.pCoreIn 2).map π ≤ pResidual 2 (H ⧸ pCore 2 H) := by
    change ((pCore 2 w.pair.subgroup).map w.pair.subgroup.subtype).map π ≤ _
    rw [map_map]
    exact (map_mono hle).trans (map_pResidual_le 2 (π.comp w.pair.subgroup.subtype))
  have h2 : IsPGroup 2 ((w.pair.subgroup.pCoreIn 2).map π) :=
    (pCore_isPGroup.map w.pair.subgroup.subtype).map π
  have hd := h2.disjoint_of_coprime hR (by decide : Nat.Coprime 2 3)
  have hm : (w.pair.subgroup.pCoreIn 2).map π = ⊥ := by
    exact bot_unique (fun x hx => hd.le_bot ⟨hx,hi hx⟩)
  simpa only [π,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hm

theorem OriginalWitness.small_core_placement_of_solvable
    {κ : GroupClass} (hH : IsSQTK κ H)
    (hP : ChapterB.IsMinimalParabolicOver S ⊤) (hs : Group.IsSolvable H)
    (w : OriginalWitness S (ChapterB.minimalParabolicMax S hP) W n)
    (hWS : W ≤ (S : Subgroup H))
    (hSW : (S : Subgroup H) ≤ normalizer (W : Set H))
    (hcore : W ≤ (ChapterB.minimalParabolicMax S hP).pCoreIn 2)
    (hout : ¬ W ≤ ChapterB.minimalParabolicCore S hP)
    (hfit : generalizedFitting H = pCore 2 H) (hW : Nat.card W = 16)
    (hSU : (S : Subgroup H) ≤ U) (hU : U ≤ normalizer (W : Set H))
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (W : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U W hU q hq hk)) :
    w.pair.subgroup.pCoreIn 2 ≤ pCore 2 H ∧
      w.pair.subgroup.pCoreIn 2 ⊓ W = pCore 2 H ⊓ W := by
  have hn := ChapterE.minimalParabolic_normalizer_le S hP W
    (IsElementaryAbelian.isPGroup 2 W) hSW hout
  have hc := w.small_quaternion_core hWS hSW hcore hn hfit hW hSU hU q hq hk hD hratio
  obtain ⟨e⟩ := hc.2.2.2.1
  have hI : Nat.card (w.pair.subgroup ⧸ pCore 2 w.pair.subgroup) = 6 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have h3 : 3 ∣ Nat.card H := by
    have hh := (pCore 2 w.pair.subgroup).index_dvd_card
    change Nat.card (w.pair.subgroup ⧸ pCore 2 w.pair.subgroup) ∣ Nat.card w.pair.subgroup at hh
    rw [hI] at hh
    exact ((by decide : 3 ∣ 6).trans hh).trans w.pair.subgroup.card_subgroup_dvd_card
  have he : ¬ (ChapterB.minimalParabolicMax S hP).pCoreIn 2 ≤ pCore 2 H := by
    intro hle
    exact hout (hcore.trans (hle.trans (ChapterB.minimalParabolicTwoCore_le_core S hP)))
  have hR : IsPGroup 3 (pResidual 2 (H ⧸ pCore 2 H)) := by
    rcases SolvableMinimalParabolic.source_cubic_models hH S hP hs (Or.inl he) h3 with
      h3 | h9 | h27
    · exact IsPGroup.of_card (n := 1) (by simpa using h3.1)
    · exact IsPGroup.of_card (n := 2) (by simpa using h9.1)
    · exact IsPGroup.of_card (n := 3) (by simpa using h27.1)
  have hPQ := w.small_core_le_twoCore_of_cubic_residual
    hWS hSW hcore hn hfit hW hSU hU q hq hk hD hratio hR
  refine ⟨hPQ, le_antisymm (inf_le_inf_right W hPQ) ?_⟩
  have hQ : (pCore 2 H).subgroupOf w.pair.subgroup ≤ pCore 2 w.pair.subgroup :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_subtype⟩
  intro x hx
  exact ⟨mem_map_of_mem w.pair.subgroup.subtype (hQ (show
    (⟨x,w.pair.le hx.2⟩ : w.pair.subgroup) ∈ (pCore 2 H).subgroupOf w.pair.subgroup from hx.1)),hx.2⟩
end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
