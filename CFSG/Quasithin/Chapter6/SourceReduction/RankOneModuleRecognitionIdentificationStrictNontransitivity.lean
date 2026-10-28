module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictNormalizer

/-!
# Nontransitivity on the strict moved plane

The image of Z_S in U/Z(U) has dimension one, inside the moved plane
of dimension two. The exact stabilizer lift of 6.2.16(5), together with
N_H(Z_S)=H∩M, makes this line invariant under the entire plane stabilizer.
A nonzero vector on that line therefore cannot be sent to a vector
outside it. This proves the source nontransitivity assertion for the
literal dotted representation.

Source: Aschbacher--Smith, 6.2.16(6), printed p.689. The G.11 alternatives
will be contradicted using this statement and the type-a₂ involution.
The remaining crossing construction and exclusions stay with this task;
LocalAnalysis is discharged by qt-d-1222-rankone-recognition-identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G]

/-- The actual image of the source four-group in U/Z(U). -/
@[expose] def strictSourceLine (T L R : Subgroup G) (z : G)
    [IsElementaryAbelian 2 (StrictVectorQuotient T L R z)] :
    Submodule (ZMod 2) (Additive (StrictVectorQuotient T L R z)) :=
  AddSubgroup.toZModSubmodule 2
    (((ZS T L R).subgroupOf (sourceClosure T L R z)).map
      (QuotientGroup.mk' (center (sourceClosure T L R z)))).toAddSubgroup

variable [Finite G] {κ : GroupClass.{u}} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}
  [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]

omit [Finite G] in
theorem strictSourceLine_le_plane
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    strictSourceLine (T : Subgroup G) L R z ≤ strictCentralPlane (T : Subgroup G) L R z := by
  intro w hw
  change w.toMul ∈ (((ZS (T : Subgroup G) L R).subgroupOf
    (sourceClosure (T : Subgroup G) L R z)).map (QuotientGroup.mk' _)) at hw
  change w.toMul ∈ (((sourceClosure (T : Subgroup G) L R z ⊓ layer L R).subgroupOf
    (sourceClosure (T : Subgroup G) L R z)).map (QuotientGroup.mk' _))
  exact map_mono (subgroupOf_mono _ hstrict.le) hw

theorem LocalAnalysis.strictSourceLine_finrank
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    Module.finrank (ZMod 2) (strictSourceLine (T : Subgroup G) L R z) = 1 := by
  let U := sourceClosure (T : Subgroup G) L R z
  let S := (ZS (T : Subgroup G) L R).subgroupOf U
  let q := QuotientGroup.mk' (center U)
  have hSU : ZS (T : Subgroup G) L R ≤ U := hstrict.le.trans inf_le_left
  have hS : Nat.card S = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hSU).toEquiv).trans
      (h611.natural_ZS_geometry hnatural).2.1
  have hcenter := A.strict_layer_center_intersection h611 hnatural hz horder hstrict
  have hline : zpowers z ≤ ZS (T : Subgroup G) L R := zpowers_le.mpr hz
  have hmap : (center U ⊓ S).map U.subtype = zpowers z := by
    rw [map_inf _ _ _ U.subtype_injective, map_subgroupOf_eq_of_le hSU]
    apply le_antisymm
    · exact (inf_le_inf_left _ (show ZS (T : Subgroup G) L R ≤ layer L R from inf_le_left)).trans
        hcenter.le
    · exact le_inf (hcenter ▸ inf_le_left) hline
  have hcs : Nat.card (center U ⊓ S : Subgroup U) = 2 := by
    rw [← card_subtype U (center U ⊓ S), hmap, Nat.card_zpowers, horder]
  have hc := relIndex_mul_relIndex (⊥ : Subgroup U) (center U ⊓ S) S bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, hcs, hS, inf_relIndex_right] at hc
  have hr := relIndex_ker S q
  rw [QuotientGroup.ker_mk'] at hr
  have hcQ : Nat.card (S.map q) = 2 := by omega
  let e : strictSourceLine (T : Subgroup G) L R z ≃ S.map q := {
    toFun w := ⟨w.val.toMul, w.property⟩
    invFun w := ⟨Additive.ofMul w.val, w.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hcL : Nat.card (strictSourceLine (T : Subgroup G) L R z) = 2 :=
    (Nat.card_congr e).trans hcQ
  have hd := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := strictSourceLine (T : Subgroup G) L R z)
  rw [hcL, Nat.card_zmod] at hd
  exact Nat.pow_right_injective (by decide : 1 < 2) (by simpa using hd.symm)

theorem LocalAnalysis.strict_stabilizer_preserves_sourceLine
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    (b : StrictActor (T : Subgroup G) L R z)
    (hb : ∀ x, x ∈ strictCentralPlane (T : Subgroup G) L R z ↔
      strictRepresentation (T : Subgroup G) L R z b x ∈ strictCentralPlane (T : Subgroup G) L R z) :
    ∀ x ∈ strictSourceLine (T : Subgroup G) L R z,
      strictRepresentation (T : Subgroup G) L R z b x ∈ strictSourceLine (T : Subgroup G) L R z := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (strictQuotientAction (T : Subgroup G) L R z).ker b
  have hm := (A.strict_plane_stabilizer_iff_mem h611 hnatural hz horder hstrict h).mp hb
  have hn : (h : G) ∈ normalizer (ZS (T : Subgroup G) L R : Set G) := by
    have hh : (h : G) ∈ centralizer ({z} : Set G) ⊓ M := ⟨h.property, hm⟩
    rw [← A.plane_normalizer] at hh
    exact hh.2
  intro x hx
  obtain ⟨s, hs, he⟩ := hx
  have hx' : x = Additive.ofMul (QuotientGroup.mk' _ s) := congrArg Additive.ofMul he.symm
  rw [hx', strictRepresentation_mk]
  change Additive.ofMul (strictQuotientAction (T : Subgroup G) L R z h
    (QuotientGroup.mk' _ s)) ∈ strictSourceLine (T : Subgroup G) L R z
  rw [strictQuotientAction_mk]
  change QuotientGroup.mk' _ (strictClosureAction (T : Subgroup G) L R z h s) ∈
    ((ZS (T : Subgroup G) L R).subgroupOf (sourceClosure (T : Subgroup G) L R z)).map
      (QuotientGroup.mk' _)
  apply mem_map_of_mem
  change (strictClosureAction (T : Subgroup G) L R z h s : G) ∈ ZS (T : Subgroup G) L R
  rw [strictClosureAction_apply]
  exact (mem_normalizer_iff.mp hn s.val).mp hs

theorem LocalAnalysis.strict_plane_not_stabilizerTransitive
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    ¬ Representation.RankTwo.StabilizerTransitive
      (strictRepresentation (T : Subgroup G) L R z) (strictCentralPlane (T : Subgroup G) L R z) := by
  let P := strictCentralPlane (T : Subgroup G) L R z
  let D := strictSourceLine (T : Subgroup G) L R z
  have hD := A.strictSourceLine_finrank h611 hnatural hz horder hstrict
  have hP := A.strictCentralPlane_finrank h611 hnatural hz horder hstrict
  have hD0 : D ≠ ⊥ := by
    intro he
    change Module.finrank (ZMod 2) D = 1 at hD
    rw [he, finrank_bot] at hD
    omega
  obtain ⟨u, hu, hun⟩ := D.ne_bot_iff.mp hD0
  have hPD : ¬ P ≤ D := by
    intro hh
    have hr := Submodule.finrank_mono hh
    change Module.finrank (ZMod 2) P ≤ Module.finrank (ZMod 2) D at hr
    change Module.finrank (ZMod 2) D = 1 at hD
    change Module.finrank (ZMod 2) P = 2 at hP
    omega
  obtain ⟨w, hw, hwd⟩ : ∃ w, w ∈ P ∧ w ∉ D := by
    by_contra! hh
    exact hPD hh
  have hwn : w ≠ 0 := fun hh => hwd (hh ▸ D.zero_mem)
  intro ht
  obtain ⟨b, hb, he⟩ := ht u (strictSourceLine_le_plane hstrict hu) hun w hw hwn
  exact hwd (he ▸ A.strict_stabilizer_preserves_sourceLine h611 hnatural hz horder hstrict b hb u hu)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
