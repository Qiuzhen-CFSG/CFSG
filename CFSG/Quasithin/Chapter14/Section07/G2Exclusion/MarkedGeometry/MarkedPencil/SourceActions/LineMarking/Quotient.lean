module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Models
public import Theory.Representation.BinaryOffender.ConjugationImage

/-!
# Local identities in the literal module quotient

Pull the image of V in U/(N.subgroupOf U) back through the supplied
module equivalence. Its cardinality is unchanged. The earlier identity
[V,X]N = V becomes equality with the span of action differences because
the quotient kills N. Normalization of V by T becomes invariance under
the actual image of T. Both deductions retain the literal quotient map
and the conjugation equations, and require only relative normalization
of U; U need not be normal in the ambient group.

These are the local-to-module steps in Aschbacher–Smith 14.7.55(1), printed
p.1066, PDF p.1083. `LineMarking` uses them with N = V₁ and X = L₁.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.LineMarking
open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion Atlas.G2.Natural
open Representation.BinaryOffender
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification

open Subgroup

section Source
open scoped IsMulCommutative
variable {Q W : Type*} [Group Q] [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def sourceMap (U N : Subgroup Q) [(N.subgroupOf U).Normal]
    (e : Multiplicative W ≃* U ⧸ N.subgroupOf U) : U →* Multiplicative W :=
  e.symm.toMonoidHom.comp (QuotientGroup.mk' (N.subgroupOf U))

def sourcePlane (U N V : Subgroup Q) [(N.subgroupOf U).Normal]
    (e : Multiplicative W ≃* U ⧸ N.subgroupOf U) : Submodule (ZMod 2) W :=
  AddSubgroup.toZModSubmodule 2
    (AddSubgroup.toSubgroup.symm ((V.subgroupOf U).map (sourceMap U N e)))

theorem sourcePlane_image (U N V : Subgroup Q) [(N.subgroupOf U).Normal]
    (e : Multiplicative W ≃* U ⧸ N.subgroupOf U) :
    (sourcePlane U N V e).toAddSubgroup.toSubgroup.map e.toMonoidHom =
      (V.subgroupOf U).map (QuotientGroup.mk' (N.subgroupOf U)) := by
  change ((V.subgroupOf U).map (sourceMap U N e)).map e.toMonoidHom = _
  rw [Subgroup.map_map]
  congr 1
  ext u
  exact e.apply_symm_apply _

theorem sourcePlane_card (U N V : Subgroup Q) [(N.subgroupOf U).Normal]
    (e : Multiplicative W ≃* U ⧸ N.subgroupOf U) :
    Nat.card (sourcePlane U N V e) =
      Nat.card ((V.subgroupOf U).map (QuotientGroup.mk' (N.subgroupOf U))) := by
  change Nat.card ((V.subgroupOf U).map (sourceMap U N e)) = _
  rw [sourceMap, ← Subgroup.map_map, Subgroup.card_map_of_injective e.symm.injective]

theorem sourcePlane_commutator (U N V X : Subgroup Q) [(N.subgroupOf U).Normal]
    (e : Multiplicative W ≃* U ⧸ N.subgroupOf U)
    (σ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (k : X →* Model (ZMod 2))
    (hVU : V ≤ U) (hn : X ≤ normalizer (U : Set Q))
    (hlocal : ⁅V, X⁆ ⊔ N = V)
    (hact : ∀ (x : X) (v : U), σ (k x) ((sourceMap U N e v).toAdd) =
      (sourceMap U N e ⟨(x : Q) * v * (x : Q)⁻¹,
        le_normalizer_iff.mp hn x x.property v v.property⟩).toAdd) :
    subspaceCommutator σ (sourcePlane U N V e) k.range = sourcePlane U N V e := by
  have hNU : N ≤ U := (le_sup_right.trans hlocal.le).trans hVU
  have hMU : ⁅V, X⁆ ≤ U := (le_sup_left.trans hlocal.le).trans hVU
  have hNmap : (N.subgroupOf U).map (sourceMap U N e) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro v hv
    change e.symm (QuotientGroup.mk' (N.subgroupOf U) v) = 1
    have hq : QuotientGroup.mk' (N.subgroupOf U) v = 1 :=
      (QuotientGroup.eq_one_iff v).mpr hv
    rw [hq, map_one]
  have hm := congrArg (fun B : Subgroup Q => (B.subgroupOf U).map (sourceMap U N e)) hlocal
  rw [Subgroup.subgroupOf_sup hMU hNU, Subgroup.map_sup, hNmap, sup_bot_eq] at hm
  let q := sourceMap U N e
  let P := sourcePlane U N V e
  let M := subspaceCommutator σ P k.range
  let B : Subgroup (Multiplicative W) := M.toAddSubgroup.toSubgroup
  let E : Subgroup Q := (B.comap q).map U.subtype
  have hME : ⁅V, X⁆ ≤ E := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro x hx v hv
    let xX : X := ⟨x, hx⟩
    let vU : U := ⟨v, hVU hv⟩
    let c : U := ⟨x * v * x⁻¹, le_normalizer_iff.mp hn x hx v (hVU hv)⟩
    have hvP : (q vU).toAdd ∈ P := ⟨vU, hv, rfl⟩
    have hd : σ (k xX) (q vU).toAdd - (q vU).toAdd ∈ M :=
      Submodule.subset_span ⟨k xX, ⟨xX, rfl⟩, _, hvP, rfl⟩
    refine ⟨c * vU⁻¹, ?_, rfl⟩
    change (q (c * vU⁻¹)).toAdd ∈ M
    rw [map_mul, map_inv]
    change (q c).toAdd + -(q vU).toAdd ∈ M
    rw [hact xX vU] at hd
    simpa only [sub_eq_add_neg] using hd
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨x, rfl⟩, w, hw, rfl⟩
    obtain ⟨v, hv, he⟩ := hw
    have hew : (q v).toAdd = w := congrArg Multiplicative.toAdd he
    rw [← hew, hact]
    let c : U := ⟨(x : Q) * v * (x : Q)⁻¹,
      le_normalizer_iff.mp hn x x.property v v.property⟩
    simp only [sub_eq_add_neg]
    change q c * (q v)⁻¹ ∈ (V.subgroupOf U).map q
    rw [← hm]
    refine ⟨c * v⁻¹, ?_, ?_⟩
    · change (x : Q) * v * (x : Q)⁻¹ * (v : Q)⁻¹ ∈ ⁅V, X⁆
      rw [commutator_comm]
      exact commutator_mem_commutator x.property hv
    · change q (c * v⁻¹) = q c * (q v)⁻¹
      simp only [map_mul, map_inv]
  · intro w hw
    change Multiplicative.ofAdd w ∈ (V.subgroupOf U).map q at hw
    rw [← hm] at hw
    obtain ⟨v, hv, he⟩ := hw
    obtain ⟨z, hz, hzv⟩ := hME hv
    have hze : z = v := Subtype.ext hzv
    subst z
    have hd : (q v).toAdd ∈ M := hz
    have hew : (q v).toAdd = w := congrArg Multiplicative.toAdd he
    exact hew ▸ hd

theorem sourcePlane_invariant (U N V T : Subgroup Q) [(N.subgroupOf U).Normal]
    (e : Multiplicative W ≃* U ⧸ N.subgroupOf U)
    (σ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (k : T →* Model (ZMod 2))
    (hn : T ≤ normalizer (U : Set Q)) (hnV : T ≤ normalizer (V : Set Q))
    (hact : ∀ (t : T) (v : U), σ (k t) ((sourceMap U N e v).toAdd) =
      (sourceMap U N e ⟨(t : Q) * v * (t : Q)⁻¹,
        le_normalizer_iff.mp hn t t.property v v.property⟩).toAdd) :
    k.range ≤ subspaceStabilizer σ (sourcePlane U N V e) := by
  apply le_subspaceStabilizer
  rintro _ ⟨t, rfl⟩ w hw
  obtain ⟨v, hv, he⟩ := hw
  have hw' : (sourceMap U N e v).toAdd = w := congrArg Multiplicative.toAdd he
  rw [← hw', hact]
  exact ⟨⟨(t : Q) * v * (t : Q)⁻¹,
    le_normalizer_iff.mp hn t t.property v v.property⟩,
    le_normalizer_iff.mp hnV t t.property v hv, rfl⟩

end Source

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.LineMarking
