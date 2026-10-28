module
public import Theory.GroupTheory.MinusExtraspecialA5Count
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.LocalFusion

/-!
# The first literal Thompson-pair count for J₂

The §46 fusion theorem identifies the first coordinates of P(z) with core
involutions and its second coordinates with outside involutions in C_G(z).
An explicit equivalence retains the source's ambient conjugacy and literal
cyclic-subgroup condition. The minus-extraspecial A₅ extension has 120 outside
involutions and eight compatible core involutions over each, giving 960.

Both counts are transported through `HTypeAt`'s actual core and quotient
isomorphisms. The central involution is identified using the model's center;
cyclic membership is transported along the literal centralizer inclusion.
The final theorem fills every field of the existing `LocalCensus` consumer.
No ambient order, recognition, or additional local-count premise is used.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1, printed p.259.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry
variable {G : Type*} [Group G] [Finite G]

/-- Outside-core involutions in the literal centralizer. -/
abbrev OutsideInvolutions (D : Seed G) :=
  {v : involutionCentralizer D.z // orderOf v = 2 ∧ v ∉ localCore D.z}

/-- The core choices compatible with an outside involution in the printed pair set. -/
abbrev CompatibleCore (D : Seed G) (v : involutionCentralizer D.z) :=
  {u : localCore D.z // orderOf u = 2 ∧
    D.z ∈ zpowers (((u : involutionCentralizer D.z) : G) * (v : G))}

private theorem local_mem_core_iff (D : Seed G) (v : involutionCentralizer D.z) :
    v ∈ localCore D.z ↔ (v : G) ∈ ambientCore D.z := by
  change v ∈ localCore D.z ↔ v ∈ (ambientCore D.z).subgroupOf (involutionCentralizer D.z)
  rw [ambientCore_subgroupOf]

/-- The source's ambient conjugacy clauses identify exactly the local pair choices. -/
noncomputable def sourcePairsEquivCompatible {D : Seed G} {t : G}
    (ht : OtherInvolution D t) :
    SourcePairs D.z t D.z ≃ Σ v : OutsideInvolutions D, CompatibleCore D v.val where
  toFun p := by
    have hpH := sourcePairs_mem_centralizer ht D.localType.involution p
    have hu : orderOf p.val.1 = 2 := by
      obtain ⟨g, hg⟩ := isConj_iff.mp p.property.1
      exact (congrArg orderOf hg).symm.trans (((MulAut.conj g).orderOf_eq D.z).trans D.localType.involution)
    have hv : orderOf p.val.2 = 2 := by
      obtain ⟨g, hg⟩ := isConj_iff.mp p.property.2.1
      exact (congrArg orderOf hg).symm.trans (((MulAut.conj g).orderOf_eq t).trans ht.1)
    let uH : involutionCentralizer D.z := ⟨p.val.1, hpH.1⟩
    let vH : involutionCentralizer D.z := ⟨p.val.2, hpH.2⟩
    have huQ : uH ∈ localCore D.z := (local_mem_core_iff D uH).mpr
      ((core_fusion D hpH.1 hu).mp p.property.1)
    have hvQ : vH ∉ localCore D.z := by
      intro hvQ
      exact ht.2 (((core_fusion D hpH.2 hv).mpr
        ((local_mem_core_iff D vH).mp hvQ)).trans p.property.2.1.symm)
    exact ⟨⟨vH, (orderOf_coe vH).symm.trans hv, hvQ⟩,
      ⟨⟨uH, huQ⟩, (orderOf_coe _).symm.trans ((orderOf_coe uH).symm.trans hu),
        p.property.2.2⟩⟩
  invFun p := by
    have hu : orderOf (((p.2.val : localCore D.z) : involutionCentralizer D.z) : G) = 2 :=
      (orderOf_coe _).trans ((orderOf_coe _).trans p.2.property.1)
    have hv : orderOf (p.1.val : G) = 2 := (orderOf_coe _).trans p.1.property.1
    have huconj := (core_fusion D p.2.val.val.property hu).mpr
      ((local_mem_core_iff D p.2.val.val).mp p.2.val.property)
    have hvconj : IsConj t (p.1.val : G) := (ht.classes _ hv).resolve_left (by
      intro hzv
      exact p.1.property.2 ((local_mem_core_iff D p.1.val).mpr
        ((core_fusion D p.1.val.property hv).mp hzv)))
    exact ⟨⟨p.2.val.val.val, p.1.val.val⟩, huconj, hvconj, p.2.property.2⟩
  left_inv p := Subtype.ext rfl
  right_inv p := by cases p; rfl

/-- Counting the literal source pairs by their second coordinate. The two local
numerical facts are explicit here and must be supplied in the source assembly. -/
theorem sourceCount_eq_960_of_local_counts {D : Seed G} {t : G}
    (ht : OtherInvolution D t) (hout : Nat.card (OutsideInvolutions D) = 120)
    (hcore : ∀ v : OutsideInvolutions D, Nat.card (CompatibleCore D v.val) = 8) :
    sourceCount D.z t D.z = 960 := by
  classical
  let : Fintype (OutsideInvolutions D) := Fintype.ofFinite _
  rw [sourceCount, Nat.card_congr (sourcePairsEquivCompatible ht), Nat.card_sigma]
  simp only [hcore, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, hout]
  norm_num


private theorem core_self_centralizing (D : Seed G) :
    centralizer (localCore D.z : Set (involutionCentralizer D.z)) ≤ localCore D.z :=
  centralizer_generalizedFitting_le _

/-- The 120 outside involutions in Aschbacher 47.1, in the actual local group. -/
theorem outsideInvolutions_card (D : Seed G) : Nat.card (OutsideInvolutions D) = 120 := by
  obtain ⟨t, ht, hzt⟩ := exists_commuting_other D
  let v : involutionCentralizer D.z := ⟨t, mem_centralizer_singleton_iff.mpr hzt.symm.eq⟩
  exact MinusExtraspecial.outside_involutions_card (localCore D.z)
    D.localType.core_equiv.some (core_self_centralizing D) D.localType.quotient_equiv.some
    v ((orderOf_coe v).symm.trans ht.1)
    (fun hv => ht.not_mem_core ((local_mem_core_iff D v).mp hv))

/-- The eight compatible core involutions over each of the 120 outside choices. -/
theorem compatibleCore_card (D : Seed G) (v : OutsideInvolutions D) :
    Nat.card (CompatibleCore D v.val) = 8 := by
  let zH : involutionCentralizer D.z := ⟨D.z, mem_centralizer_singleton_iff.mpr rfl⟩
  have hzZ : zH ∈ center (involutionCentralizer D.z) :=
    mem_center_iff.mpr fun q => Subtype.ext (mem_centralizer_singleton_iff.mp q.property)
  let zQ : localCore D.z := ⟨zH, HTypeAt.center_le_core hzZ⟩
  have hzQ : orderOf zQ = 2 := (orderOf_coe zQ).symm.trans
    ((orderOf_coe zH).symm.trans D.localType.involution)
  let e := D.localType.core_equiv.some
  have heZ : e zQ ∈ center MinusExtraspecial.Model := by
    apply mem_center_iff.mpr
    intro x
    obtain ⟨q, rfl⟩ := e.surjective x
    rw [← map_mul, ← map_mul]
    apply congrArg e
    apply Subtype.ext
    exact mem_center_iff.mp hzZ q.val
  have hez : e zQ = MinusExtraspecial.quaternion MinusExtraspecial.z := by
    rcases (MinusExtraspecial.mem_center_iff _).mp heZ with he | he
    · have ho := (e.orderOf_eq zQ).trans hzQ
      rw [he, orderOf_one] at ho
      omega
    · exact he
  have hc := MinusExtraspecial.compatible_core_card (localCore D.z) e
    (core_self_centralizing D) D.localType.quotient_equiv.some
    v.val v.property.1 v.property.2 zQ hzQ hez
  let ec : CompatibleCore D v.val ≃
      {q : localCore D.z // orderOf q = 2 ∧
        (zQ : involutionCentralizer D.z) ∈ zpowers ((q : involutionCentralizer D.z) * v.val)} :=
    Equiv.subtypeEquivRight (fun q => by
      apply and_congr_right
      intro _
      simp only [mem_zpowers_iff]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, Subtype.ext (by simpa only [Subgroup.coe_zpow, Subgroup.coe_mul] using hn)⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, congrArg Subtype.val hn⟩)
  exact (Nat.card_congr ec).trans hc

/-- The first numerical assertion in the proof of Aschbacher 47.1. This uses
ambient conjugacy and the literal rotation-subgroup condition from the source,
without ambient order or recognition hypotheses. -/
theorem sourceCount_at_z_eq_960 {D : Seed G} {t : G} (ht : OtherInvolution D t) :
    sourceCount D.z t D.z = 960 :=
  sourceCount_eq_960_of_local_counts ht (outsideInvolutions_card D) (compatibleCore_card D)

/-- The complete earlier-source census required by second-centralizer recognition. -/
theorem localCensus_of_seed (D : Seed G) : LocalCensus D :=
  localCensus_of_count D (fun _ ht => sourceCount_at_z_eq_960 ht)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry
