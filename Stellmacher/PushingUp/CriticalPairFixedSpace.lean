module

public import Stellmacher.PushingUp.CriticalPairSL2TwoData
public import Theory.GroupTheory.PCoreOddIndex

/-!
# Fixed spaces and indices for a critical-pair action

This module proves the fixed-space, action-commutator, and cardinal
identifications used in Stellmacher, *Pushing up*, Arch. Math. 46 (1986),
the proof of Lemma (2.2), journal p.11.  For the canonical action of
`G_a / C_{G_a}(Z_a)` on `Z_a`, the image of the opposite vertex group has
fixed space `Z_a ∩ Q_{a'}`, action commutator `[Z_a,Z_{a'}]`, and order
`[Z_{a'} : Z_{a'} ∩ Q_a]`; the quotient by its fixed space has order
`[Z_a : Z_a ∩ Q_{a'}]`.  The global fixed space is recorded as the
literal subgroup `Z_a ∩ Z(G_a)` inside the local module.

The quotient-action fixed-point and commutator generators are transported
through the canonical module and stabilizer embeddings using
`vertexZ_eq_local_vSubgroup`.  At each endpoint, the relevant centralizer
intersection is a `2`-subgroup of the local centralizer; its odd index over
the two-core puts it inside that core, while the omega-center hypothesis
gives the reverse inclusion.  The two cardinal formulas then follow from
the quotient kernel relative-index formula and invariance of relative index
under injective maps.  All action instances are the single named quotient
conjugation action fixed in `CriticalPairSL2TwoData`.
-/

namespace Stellmacher.PushingUp

open scoped Pointwise
open AmalgamGraph

universe u

variable {M : Type u} [Group M]

private theorem vertexZ_isPGroup_of_le_coreOmega [Finite M]
    (S : Subgroup M) (a : Vertex S)
    (hZ : vertexZ S a ≤ omegaOneCenterAmbient (vertexTwoCore S a)) :
    IsPGroup 2 (vertexZ S a) := by
  have hOmega : IsPGroup 2
      (omegaOneCenterAmbient (vertexTwoCore S a)) := by
    let _ : IsElementaryAbelian 2
        (omegaOneCenterAmbient (vertexTwoCore S a)) :=
      omegaOneCenterAmbient_elementaryAbelian _
    exact IsElementaryAbelian.isPGroup 2 _
  exact hOmega.to_le hZ

private theorem vertexZ_inf_centralizer_eq_inf_twoCore [Finite M]
    (S : Subgroup M) (a a' : Vertex S)
    (haa' : vertexZ S a ≤ stabilizer S a')
    (hZaTwo : IsPGroup 2 (vertexZ S a))
    (hZa'omega :
      vertexZ S a' ≤ omegaOneCenterAmbient (vertexTwoCore S a'))
    (hodd : CriticalVertexCentralizer.Conclusion S a') :
    vertexZ S a ⊓ Subgroup.centralizer (vertexZ S a' : Set (FreeAmalgam S)) =
      vertexZ S a ⊓ vertexTwoCore S a' := by
  classical
  let H : Subgroup (FreeAmalgam S) :=
    vertexZ S a ⊓ Subgroup.centralizer (vertexZ S a' : Set (FreeAmalgam S))
  have hHstab : H ≤ stabilizer S a' := inf_le_left.trans haa'
  let A : Subgroup (stabilizer S a') := H.subgroupOf (stabilizer S a')
  have hAcentral : A ≤ vertexCentralizerLocal S a' := by
    intro x hx
    rw [mem_vertexCentralizerLocal_iff]
    exact hx.2
  have hHtwo : IsPGroup 2 H := hZaTwo.to_le inf_le_left
  have hAtwo : IsPGroup 2 A :=
    hHtwo.of_equiv (Subgroup.subgroupOfEquivOfLe hHstab).symm
  have hAcore : A ≤ pCore 2 (stabilizer S a') :=
    hAtwo.le_pCore_of_le_oddIndexOverCore hodd.core_le_centralizer
      hodd.centralizer_mod_core_odd hAcentral
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1, ?_⟩
    exact Subgroup.mem_map_of_mem (stabilizer S a').subtype
      (hAcore (show (⟨x, hHstab hx⟩ : stabilizer S a') ∈ A from hx))
  · intro x hx
    refine ⟨hx.1, ?_⟩
    exact (Subgroup.mem_centralizer_iff).2 (fun z hz ↦ by
      have hzData :=
        (mem_omegaOneCenterAmbient_iff (vertexTwoCore S a') z).mp
          (hZa'omega hz)
      exact (hzData.2.2 x hx.2).symm)

private theorem vertexModule_inf_centralizer_map [Finite M]
    (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a) :
    (vertexModule S a ⊓
        Subgroup.centralizer
          (((vertexZ S a').subgroupOf (stabilizer S a)) :
            Set (stabilizer S a))).map
      (stabilizer S a).subtype =
        vertexZ S a ⊓
          Subgroup.centralizer (vertexZ S a' : Set (FreeAmalgam S)) := by
  classical
  ext x
  constructor
  · rintro ⟨y, ⟨hyV, hyC⟩, rfl⟩
    refine ⟨?_, (Subgroup.mem_centralizer_iff).2 ?_⟩
    · rw [← vertexZ_eq_local_vSubgroup S a]
      exact Subgroup.mem_map_of_mem (stabilizer S a).subtype hyV
    · intro z hz
      let zlocal : stabilizer S a := ⟨z, ha' hz⟩
      have hcomm := (Subgroup.mem_centralizer_iff.mp hyC) zlocal hz
      exact congrArg Subtype.val hcomm
  · rintro ⟨hxZ, hxC⟩
    let y : stabilizer S a := ⟨x, vertexZ_le_stabilizer S a hxZ⟩
    have hyV : y ∈ vertexModule S a := by
      rw [← vertexZ_eq_local_vSubgroup S a] at hxZ
      obtain ⟨v, hv, heq⟩ := hxZ
      have hvy : v = y := by
        apply Subtype.ext
        exact heq
      simpa [hvy] using hv
    have hyC : y ∈ Subgroup.centralizer
        (((vertexZ S a').subgroupOf (stabilizer S a)) :
          Set (stabilizer S a)) := by
      apply (Subgroup.mem_centralizer_iff).2
      intro z hz
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hxC) z hz
    exact ⟨y, ⟨hyV, hyC⟩, rfl⟩

private theorem criticalPair_oppositeFixed_map [Finite M]
    (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a)
    (hV : IsElementaryAbelian 2 (vertexModule S a))
    (hinputs : CriticalPairSL2Two.ActionInputs S a a' ha' hV) :
    let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
    let _ := vertexQuotientConjugationAction S a
    ((FixedPoints.subgroup (oppositeImage S a a' ha')
        (vertexModule S a)).map (vertexModule S a).subtype).map
          (stabilizer S a).subtype =
      vertexZ S a ⊓ vertexTwoCore S a' := by
  let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
  let _ := vertexQuotientConjugationAction S a
  change
    ((FixedPoints.subgroup
        (((vertexZ S a').subgroupOf (stabilizer S a)).map
          (vertexActionQuotientMap S a))
        (vertexModule S a)).map (vertexModule S a).subtype).map
          (stabilizer S a).subtype =
      vertexZ S a ⊓ vertexTwoCore S a'
  rw [Stellmacher.SectionTwo.quotientConjugationAction_fixedPoints_image_map
    (vertexSylow S a) (vertexActionQuotientMap S a)
    (QuotientGroup.mk'_surjective (vertexActionCentralizer S a))
    (QuotientGroup.ker_mk' (vertexActionCentralizer S a))
    ((vertexZ S a').subgroupOf (stabilizer S a))]
  rw [vertexModule_inf_centralizer_map S a a' ha']
  exact vertexZ_inf_centralizer_eq_inf_twoCore S a a'
    hinputs.left_Z_le_right_stabilizer
    (vertexZ_isPGroup_of_le_coreOmega S a hinputs.left_Z_le_coreOmega)
    hinputs.right_Z_le_coreOmega hinputs.oppositeCentralizer_odd

private theorem criticalPair_globalFixed_eq_centerPart [Finite M]
    (S : Subgroup M) (a : Vertex S)
    (hV : IsElementaryAbelian 2 (vertexModule S a)) :
    let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
    let _ := vertexQuotientConjugationAction S a
    FixedPoints.subgroup (VertexActionQuotient S a) (vertexModule S a) =
      vertexCenterPart S a := by
  let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
  let _ := vertexQuotientConjugationAction S a
  ext x
  constructor
  · intro hx
    change (x : stabilizer S a) ∈ Subgroup.center (stabilizer S a)
    rw [Subgroup.mem_center_iff]
    intro g
    have hfix := (FixedPoints.mem_subgroup
      (M := VertexActionQuotient S a) (a := x)).mp hx
        (vertexActionQuotientMap S a g)
    have heq := congrArg Subtype.val hfix
    rw [Stellmacher.SectionTwo.quotientConjugationAction_smul_coe
      (vertexSylow S a) (vertexActionQuotientMap S a)
      (QuotientGroup.mk'_surjective (vertexActionCentralizer S a))
      (QuotientGroup.ker_mk' (vertexActionCentralizer S a))] at heq
    exact mul_inv_eq_iff_eq_mul.mp heq
  · intro hx
    rw [FixedPoints.mem_subgroup]
    intro b
    obtain ⟨g, hg⟩ :=
      QuotientGroup.mk'_surjective (vertexActionCentralizer S a) b
    apply Subtype.ext
    change ((b • x : vertexModule S a) : stabilizer S a) = x
    rw [← hg, Stellmacher.SectionTwo.quotientConjugationAction_smul_coe
      (vertexSylow S a) (vertexActionQuotientMap S a)
      (QuotientGroup.mk'_surjective (vertexActionCentralizer S a))
      (QuotientGroup.ker_mk' (vertexActionCentralizer S a))]
    change (x : stabilizer S a) ∈ Subgroup.center (stabilizer S a) at hx
    rw [(Subgroup.mem_center_iff.mp hx) g, mul_inv_cancel_right]

private theorem quotientConjugationAction_commutator_image_map
    {G : Type*} [Group G] (S : Sylow 2 G)
    {barG : Type*} [Group barG] (q : G →* barG)
    (hq : Function.Surjective q) (hker : q.ker = Stellmacher.SectionTwo.cSubgroup S)
    (A : Subgroup G) :
    let _ := Stellmacher.SectionTwo.quotientConjugationAction S q hq hker
    (commutatorAction (A.map q) (Stellmacher.SectionTwo.vSubgroup S)).map
        (Stellmacher.SectionTwo.vSubgroup S).subtype =
      ⁅Stellmacher.SectionTwo.vSubgroup S, A⁆ := by
  let _ := Stellmacher.SectionTwo.quotientConjugationAction S q hq hker
  let V := Stellmacher.SectionTwo.vSubgroup S
  let _ : V.Normal := Subgroup.normalClosure_normal
  have hnorm : A ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.le_normalizer_of_normal
  let _ : Subgroup.Normalizes A V := ⟨hnorm⟩
  have hcomm : commutatorAction (A.map q) V = commutatorAction A V := by
    rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨e, x, rfl⟩
      obtain ⟨g, hg, heq⟩ := e.property
      refine ⟨⟨g, hg⟩, x, ?_⟩
      congr 1
      apply Subtype.ext
      change ((e.val • x : V) : G) = g * (x : G) * g⁻¹
      rw [← heq, Stellmacher.SectionTwo.quotientConjugationAction_smul_coe
        S q hq hker]
    · rintro ⟨g, x, rfl⟩
      refine ⟨⟨q g, Subgroup.mem_map_of_mem q g.property⟩, x, ?_⟩
      congr 1
      apply Subtype.ext
      change (g : G) * (x : G) * (g : G)⁻¹ = ((q g • x : V) : G)
      rw [Stellmacher.SectionTwo.quotientConjugationAction_smul_coe
        S q hq hker]
  change (commutatorAction (A.map q) V).map V.subtype = ⁅V, A⁆
  rw [hcomm, commutatorAction_subgroup_conj_map_eq_commutator V A hnorm]

private theorem criticalPair_commutator_map [Finite M]
    (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a)
    (hV : IsElementaryAbelian 2 (vertexModule S a)) :
    let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
    let _ := vertexQuotientConjugationAction S a
    ((commutatorAction (oppositeImage S a a' ha')
        (vertexModule S a)).map (vertexModule S a).subtype).map
          (stabilizer S a).subtype =
      ⁅vertexZ S a, vertexZ S a'⁆ := by
  let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
  let _ := vertexQuotientConjugationAction S a
  change
    ((commutatorAction
        (((vertexZ S a').subgroupOf (stabilizer S a)).map
          (vertexActionQuotientMap S a))
        (vertexModule S a)).map (vertexModule S a).subtype).map
          (stabilizer S a).subtype =
      ⁅vertexZ S a, vertexZ S a'⁆
  rw [quotientConjugationAction_commutator_image_map
    (vertexSylow S a) (vertexActionQuotientMap S a)
    (QuotientGroup.mk'_surjective (vertexActionCentralizer S a))
    (QuotientGroup.ker_mk' (vertexActionCentralizer S a))
    ((vertexZ S a').subgroupOf (stabilizer S a)),
    Subgroup.map_commutator, vertexZ_eq_local_vSubgroup S a,
    Subgroup.map_subgroupOf_eq_of_le ha']

private theorem vertexActionCentralizer_inf_opposite_map [Finite M]
    (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a) :
    ((vertexActionCentralizer S a ⊓
        (vertexZ S a').subgroupOf (stabilizer S a)).map
      (stabilizer S a).subtype) =
        vertexZ S a' ⊓
          Subgroup.centralizer (vertexZ S a : Set (FreeAmalgam S)) := by
  classical
  ext x
  constructor
  · rintro ⟨y, ⟨hyC, hyA⟩, rfl⟩
    refine ⟨hyA, (Subgroup.mem_centralizer_iff).2 ?_⟩
    intro z hz
    rw [← vertexZ_eq_local_vSubgroup S a] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    change y ∈ Subgroup.centralizer
      (vertexModule S a : Set (stabilizer S a)) at hyC
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hyC) v hv)
  · rintro ⟨hxZ, hxC⟩
    let y : stabilizer S a := ⟨x, ha' hxZ⟩
    have hyC : y ∈ vertexActionCentralizer S a := by
      change y ∈ Subgroup.centralizer
        (vertexModule S a : Set (stabilizer S a))
      apply (Subgroup.mem_centralizer_iff).2
      intro v hv
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hxC) (v : FreeAmalgam S)
        (by rw [← vertexZ_eq_local_vSubgroup S a]
            exact Subgroup.mem_map_of_mem (stabilizer S a).subtype hv)
    exact ⟨y, ⟨hyC, hxZ⟩, rfl⟩

private theorem criticalPair_oppositeKernel_inf_map [Finite M]
    (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a)
    (hV : IsElementaryAbelian 2 (vertexModule S a))
    (hinputs : CriticalPairSL2Two.ActionInputs S a a' ha' hV) :
    ((vertexActionCentralizer S a ⊓
        (vertexZ S a').subgroupOf (stabilizer S a)).map
      (stabilizer S a).subtype) =
        vertexZ S a' ⊓ vertexTwoCore S a := by
  rw [vertexActionCentralizer_inf_opposite_map S a a' ha']
  exact vertexZ_inf_centralizer_eq_inf_twoCore S a' a ha'
    (vertexZ_isPGroup_of_le_coreOmega S a' hinputs.right_Z_le_coreOmega)
    hinputs.left_Z_le_coreOmega hinputs.critical.centralizer_odd

private theorem criticalPair_oppositeImage_card [Finite M]
    (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a)
    (hV : IsElementaryAbelian 2 (vertexModule S a))
    (hinputs : CriticalPairSL2Two.ActionInputs S a a' ha' hV) :
    Nat.card (oppositeImage S a a' ha') =
      (vertexZ S a' ⊓ vertexTwoCore S a).relIndex (vertexZ S a') := by
  let A : Subgroup (stabilizer S a) :=
    (vertexZ S a').subgroupOf (stabilizer S a)
  let C : Subgroup (stabilizer S a) := vertexActionCentralizer S a
  let q : stabilizer S a →* VertexActionQuotient S a :=
    vertexActionQuotientMap S a
  have hker : q.ker = C := QuotientGroup.ker_mk' C
  have hinf := criticalPair_oppositeKernel_inf_map S a a' ha' hV hinputs
  calc
    Nat.card (oppositeImage S a a' ha') = Nat.card (A.map q) := rfl
    _ = q.ker.relIndex A := (Subgroup.relIndex_ker (K := A) q).symm
    _ = C.relIndex A := by rw [hker]
    _ = (C ⊓ A).relIndex A := (Subgroup.inf_relIndex_right C A).symm
    _ = ((C ⊓ A).map (stabilizer S a).subtype).relIndex
          (A.map (stabilizer S a).subtype) :=
      (Subgroup.relIndex_map_map_of_injective (C ⊓ A) A
        (stabilizer S a).subtype_injective).symm
    _ = (vertexZ S a' ⊓ vertexTwoCore S a).relIndex (vertexZ S a') := by
      rw [show (C ⊓ A).map (stabilizer S a).subtype =
          vertexZ S a' ⊓ vertexTwoCore S a from hinf]
      rw [Subgroup.map_subgroupOf_eq_of_le ha']

private theorem criticalPair_fixedQuotient_card [Finite M]
    (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a)
    (hV : IsElementaryAbelian 2 (vertexModule S a))
    (hfixed :
      let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
      let _ := vertexQuotientConjugationAction S a
      ((FixedPoints.subgroup (oppositeImage S a a' ha')
          (vertexModule S a)).map (vertexModule S a).subtype).map
            (stabilizer S a).subtype =
        vertexZ S a ⊓ vertexTwoCore S a') :
    let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
    let _ := vertexQuotientConjugationAction S a
    Nat.card ((vertexModule S a) ⧸
        FixedPoints.subgroup (oppositeImage S a a' ha')
          (vertexModule S a)) =
      (vertexZ S a ⊓ vertexTwoCore S a').relIndex (vertexZ S a) := by
  let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
  let _ := vertexQuotientConjugationAction S a
  let V : Subgroup (stabilizer S a) := vertexModule S a
  let F : Subgroup V :=
    FixedPoints.subgroup (oppositeImage S a a' ha') V
  change ((F.map V.subtype).map (stabilizer S a).subtype) =
    vertexZ S a ⊓ vertexTwoCore S a' at hfixed
  change Nat.card (V ⧸ F) =
    (vertexZ S a ⊓ vertexTwoCore S a').relIndex (vertexZ S a)
  calc
    Nat.card (V ⧸ F) = F.index := (Subgroup.index_eq_card F).symm
    _ = F.relIndex ⊤ := (Subgroup.relIndex_top_right F).symm
    _ = (F.map V.subtype).relIndex ((⊤ : Subgroup V).map V.subtype) :=
      (Subgroup.relIndex_map_map_of_injective F ⊤ V.subtype_injective).symm
    _ = (F.map V.subtype).relIndex V := by
      rw [← V.subtype.range_eq_map, V.range_subtype]
    _ = ((F.map V.subtype).map (stabilizer S a).subtype).relIndex
          (V.map (stabilizer S a).subtype) :=
      (Subgroup.relIndex_map_map_of_injective (F.map V.subtype) V
        (stabilizer S a).subtype_injective).symm
    _ = (vertexZ S a ⊓ vertexTwoCore S a').relIndex (vertexZ S a) := by
      rw [hfixed]
      exact congrArg ((vertexZ S a ⊓ vertexTwoCore S a').relIndex)
        (vertexZ_eq_local_vSubgroup S a)

/-- The fixed-space and relative-index data in Stellmacher's proof of
Lemma (2.2). -/
public theorem criticalPair_fixedSpaceData [Finite M]
    (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a)
    (hV : IsElementaryAbelian 2 (vertexModule S a))
    (hinputs : CriticalPairSL2Two.ActionInputs S a a' ha' hV) :
    CriticalPairSL2Two.FixedSpaceData S a a' ha' hV := by
  have hfixed := criticalPair_oppositeFixed_map S a a' ha' hV hinputs
  exact {
    oppositeFixed_map := hfixed
    globalFixed_eq_centerPart :=
      criticalPair_globalFixed_eq_centerPart S a hV
    commutator_map := criticalPair_commutator_map S a a' ha' hV
    oppositeImage_card :=
      criticalPair_oppositeImage_card S a a' ha' hV hinputs
    fixedQuotient_card :=
      criticalPair_fixedQuotient_card S a a' ha' hV hfixed
  }

end Stellmacher.PushingUp
