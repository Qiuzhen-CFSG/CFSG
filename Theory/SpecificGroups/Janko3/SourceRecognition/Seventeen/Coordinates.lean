module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.PairEmbedding
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.ComplementConjugacy

/-!
# Core coordinates for the seventeen-point action

The point two-core is identified with the actual binary four-space in the
source semidirect product. It acts regularly on the sixteen points other
than the fixed point. This gives coordinates by `Option O₂(H₁)`, in which
the point group acts by translations and its literal overlap action.
The faithful overlap actions of two source completions are then aligned
through an isomorphism of their two-cores.

Source: Baumeister, *A geometry for groups of J₃-type* (2007),
Lemma 2.9, printed p.498, the regular-normal-subgroup identification.
-/

public noncomputable section
open Subgroup MulAction
namespace Sporadic.Janko3.SourceRecognition.Seventeen.SourceData
variable {G : Type*} [Group G] (S : SourceData G)

noncomputable def coreEquivPlane : pCore 2 S.H1 ≃* Plane := by
  let M := Plane ⋊[S.action] Complement
  let I : Subgroup M := (SemidirectProduct.inl : Plane →* M).range
  have hi : Nat.card I = 16 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv]
    norm_num [Plane, Nat.card_eq_fintype_card, Fintype.card_multiplicative]
  have hm : Nat.card M = 480 := (Nat.card_congr S.pointEquiv.toEquiv).symm.trans S.point_card
  let : Finite M := Nat.finite_of_card_ne_zero (by rw [hm]; decide)
  have hI : I = (SemidirectProduct.rightHom : M →* Complement).ker :=
    SemidirectProduct.range_inl_eq_ker_rightHom
  let : I.Normal := hI ▸ inferInstance
  have hp : IsPGroup 2 I := IsPGroup.of_card (n := 4) hi
  have hle : I ≤ pCore 2 M := le_sSup ⟨inferInstance, hp⟩
  let e := (equivMapOfInjective (pCore 2 S.H1) S.pointEquiv.toMonoidHom S.pointEquiv.injective).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 S.pointEquiv))
  have hc : Nat.card (pCore 2 M) = 16 := (Nat.card_congr e.toEquiv).symm.trans S.core_card
  have he : I = pCore 2 M := eq_of_le_of_card_ge hle (by rw [hi, hc])
  exact (e.trans (MulEquiv.subgroupCongr he.symm)).trans
    (MonoidHom.ofInjective SemidirectProduct.inl_injective).symm

noncomputable def coreCosetEquiv
    (b : G) (hb : b*b=1) (hout : b ∉ S.H1) (hb2 : b ∈ S.H2) (hb3 : b ∈ S.H3) :
    pCore 2 S.H1 ≃ {x : CosetGraph.Vertex (S.cosetData b hb hout) //
      x ≠ CosetGraph.base (S.cosetData b hb hout)} := by
  let D := S.cosetData b hb hout
  let f : pCore 2 S.H1 → {x : CosetGraph.Vertex D // x ≠ CosetGraph.base D} := fun v =>
    ⟨((v : S.H1) : G) • CosetGraph.other D, by
      intro he
      apply CosetGraph.base_ne_other D
      apply MulAction.injective (((v : S.H1) : G))
      have hfix : ((v : S.H1) : G) • CosetGraph.base D = CosetGraph.base D := by
        change ((v : S.H1) : G) ∈ stabilizer G (CosetGraph.base D)
        rw [CosetGraph.point_stabilizer D]
        exact (v : S.H1).property
      exact hfix.trans he.symm⟩
  apply Equiv.ofBijective f
  constructor
  · intro v w hvw
    have he : ((v : S.H1) : G) • CosetGraph.other D =
        ((w : S.H1) : G) • CosetGraph.other D := congrArg Subtype.val hvw
    have hedge : ((w⁻¹*v : pCore 2 S.H1) : S.H1) ∈ CosetGraph.edgeStabilizer D := by
      change (((w : S.H1) : G)⁻¹ * ((v : S.H1) : G)) • CosetGraph.other D = CosetGraph.other D
      rw [mul_smul, he, inv_smul_smul]
    rw [S.edge_stabilizer b hb hout hb2] at hedge
    have hh : (((w⁻¹*v : pCore 2 S.H1) : S.H1)) = 1 :=
      S.overlap_core_disjoint.le_bot ⟨hedge, (w⁻¹*v).property⟩
    exact (inv_mul_eq_one.mp (Subtype.ext hh : w⁻¹*v=1)).symm
  · intro x
    obtain ⟨v, hv⟩ := S.core_orbit_of_complete b hb hout hb2
      (S.consequences b hb hout hb2 hb3).2.2.1 x x.property
    exact ⟨v, Subtype.ext hv⟩

noncomputable def coreCoordinates
    (b : G) (hb : b*b=1) (hout : b ∉ S.H1) (hb2 : b ∈ S.H2) (hb3 : b ∈ S.H3) :
    Option (pCore 2 S.H1) ≃ CosetGraph.Vertex (S.cosetData b hb hout) := by
  classical
  exact (Equiv.optionCongr (S.coreCosetEquiv b hb hout hb2 hb3)).trans
    (Equiv.optionSubtypeNe (CosetGraph.base (S.cosetData b hb hout)))

theorem coreCoordinates_none
    (b : G) (hb : b*b=1) (hout : b ∉ S.H1) (hb2 : b ∈ S.H2) (hb3 : b ∈ S.H3) :
    S.coreCoordinates b hb hout hb2 hb3 none = CosetGraph.base (S.cosetData b hb hout) := by rfl

theorem coreCoordinates_some
    (b : G) (hb : b*b=1) (hout : b ∉ S.H1) (hb2 : b ∈ S.H2) (hb3 : b ∈ S.H3)
    (v : pCore 2 S.H1) :
    S.coreCoordinates b hb hout hb2 hb3 (some v) =
      ((v : S.H1) : G) • CosetGraph.other (S.cosetData b hb hout) := by rfl

theorem core_actions_equivalent {K : Type*} [Group K] (T : SourceData K) :
    ∃ e : pCore 2 S.H1 ≃* pCore 2 T.H1,
      S.overlapAction.range.map (MulAut.congr e).toMonoidHom = T.overlapAction.range := by
  let e0 := S.coreEquivPlane.trans T.coreEquivPlane.symm
  let A := S.overlapAction.range.map (MulAut.congr e0).toMonoidHom
  let B := T.overlapAction.range
  let eA : A ≃* Complement :=
    (equivMapOfInjective S.overlapAction.range (MulAut.congr e0).toMonoidHom
      (MulAut.congr e0).injective).symm.trans
      ((MonoidHom.ofInjective S.overlapAction_injective).symm.trans S.overlapEquiv)
  let eB : B ≃* Complement :=
    (MonoidHom.ofInjective T.overlapAction_injective).symm.trans T.overlapEquiv
  let : Finite (pCore 2 T.H1) := Nat.finite_of_card_ne_zero (by rw [T.core_card]; decide)
  obtain ⟨u, hu⟩ := complement_subgroups_conjugate T.core_card A B eA eB
  refine ⟨e0.trans u, ?_⟩
  change (S.overlapAction.range.map (MulAut.congr e0).toMonoidHom).map
    (MulAut.conj u).toMonoidHom = B at hu
  rw [map_map] at hu
  have he : (MulAut.congr (e0.trans u)).toMonoidHom =
      (MulAut.conj u).toMonoidHom.comp (MulAut.congr e0).toMonoidHom := by
    ext a v
    rfl
  rw [he]
  exact hu


theorem coreCoordinates_smul
    (b : G) (hb : b*b=1) (hout : b ∉ S.H1) (hb2 : b ∈ S.H2) (hb3 : b ∈ S.H3)
    (v : pCore 2 S.H1) (c : S.H2.subgroupOf S.H1) (z : Option (pCore 2 S.H1)) :
    (((v : S.H1) : G) * ((c : S.H1) : G)) • S.coreCoordinates b hb hout hb2 hb3 z =
      S.coreCoordinates b hb hout hb2 hb3 (z.map (fun w => v * S.overlapAction c w)) := by
  let D := S.cosetData b hb hout
  cases z with
  | none =>
    change (((v : S.H1) : G) * ((c : S.H1) : G)) • CosetGraph.base D = CosetGraph.base D
    change (((v : S.H1) : G) * ((c : S.H1) : G)) ∈ stabilizer G (CosetGraph.base D)
    rw [CosetGraph.point_stabilizer D]
    exact S.H1.mul_mem (v : S.H1).property (c : S.H1).property
  | some w =>
    simp only [Option.map_some, S.coreCoordinates_some]
    have hfix : ((c : S.H1) : G) • CosetGraph.other D = CosetGraph.other D := by
      have hh : (c : S.H1) ∈ CosetGraph.edgeStabilizer D :=
        (S.edge_stabilizer b hb hout hb2).symm ▸ c.property
      exact hh
    change (((v : S.H1) : G) * ((c : S.H1) : G)) •
      (((w : S.H1) : G) • CosetGraph.other D) =
      (((v : S.H1) : G) * (((c : S.H1) : G) * ((w : S.H1) : G) *
        ((c : S.H1) : G)⁻¹)) • CosetGraph.other D
    calc
      _ = (((v : S.H1) : G) * (((c : S.H1) : G) * ((w : S.H1) : G) *
          ((c : S.H1) : G)⁻¹)) • (((c : S.H1) : G) • CosetGraph.other D) := by
        simp only [← mul_smul]
        congr 1
        group
      _ = _ := by rw [hfix]


end Sporadic.Janko3.SourceRecognition.Seventeen.SourceData
