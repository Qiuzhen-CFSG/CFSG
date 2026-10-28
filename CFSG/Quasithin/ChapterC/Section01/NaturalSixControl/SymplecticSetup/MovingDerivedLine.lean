module
public import Theory.Representation.BinaryPermutation.SixCentralDerived
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.MovingLayer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.LocalGroups
/-!
# Derived order of the actual moving radius

A marked natural binary four-dimensional central quotient bounds the moving
radius derived subgroup by two. The action is literal conjugation by the
embedded local group, restricted to its alternating component; no splitting
of the local quotient is used. Containment in the source fixed core makes this
component fix the derived subgroup, supplying the remaining hypothesis of the
central-extension theorem.

The coordinates of the central quotient are explicit. This is the source
(3.10)(i) input to Meierfrankenfeld--Stellmacher (1993), (5.12)(2), not the
separate recognition of that central quotient.
-/
public noncomputable section

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Subgroup Theory.GroupTheory BinaryPermutation
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
variable {M : Type*} [Group M]

/-- The literal conjugation action of M on the moving radius at its base vertex. -/
@[expose] noncomputable def movingRadiusAction (R : Subgroup M) : M→*MulAut (Vcirc R (alpha R)) :=
  (Vcirc R (alpha R)).normalizerMonoidHom.comp ((embedM R).codRestrict _ (by
    intro m
    apply Vcirc_normalized (alpha R)
    change embedM R m∈stabilizer R (mVertex R 1)
    rw [stabilizer_m_base]
    exact ⟨m,rfl⟩))

theorem movingRadiusAction_apply (R : Subgroup M) (m : M) (p : Vcirc R (alpha R)) :
    (movingRadiusAction R m p:FreeAmalgam R)=
      embedM R m*(p:FreeAmalgam R)*(embedM R m)⁻¹ := rfl

namespace Source
variable [Finite M]
variable {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)

/-- A marked natural central quotient bounds the actual moving-radius derived
subgroup by two, using its literal fixedCore containment. -/
theorem movingRadius_derived_card_le_two
    (e : ((Vcirc R (alpha R)) ⧸ center (Vcirc R (alpha R))) ≃*
      Multiplicative (natural (Fin 6))) (σ : Model.S≃*Model.S)
    (he : ∀ (m : M) (p : Vcirc R (alpha R)),
      (e (QuotientGroup.mk' (center (Vcirc R (alpha R))) (movingRadiusAction R m p))).toAdd=
      naturalRepresentation (Fin 6) (σ (s.projection m))
        (e (QuotientGroup.mk' (center (Vcirc R (alpha R))) p)).toAdd)
    (hfixed : ⁅Vcirc R (alpha R),Vcirc R (alpha R)⁆≤fixedCore R (alpha R)) :
    Nat.card (⁅Vcirc R (alpha R),Vcirc R (alpha R)⁆:Subgroup (FreeAmalgam R))≤2 := by
  let P := Vcirc R (alpha R)
  let q : P→*Multiplicative (natural (Fin 6)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (center P))
  let ρ : L→*MulAut P := (movingRadiusAction R).comp L.subtype
  let π : L→*Model.S := (σ.toMonoidHom.comp s.projection).comp L.subtype
  have hπ : alternatingGroup (Fin 6)≤π.range := by
    have hm : π.range=(L.map s.projection).map σ.toMonoidHom := by
      rw [MonoidHom.range_comp,range_subtype,map_map]
    rw [hm,s.component_image]
    exact (characteristic_iff_map_eq.mp (inferInstance : (alternatingGroup (Fin 6)).Characteristic) σ).symm.le
  have hk : q.ker≤center P := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hb := SixCentralDerived.card_derived_le_two q
    (e.surjective.comp (QuotientGroup.mk'_surjective (center P))) hk ρ π hπ
    (fun l p => he l p) (by
      intro l _ z hz
      apply Subtype.ext
      have hz' : (z:FreeAmalgam R)∈⁅P,P⁆ := by
        rw [←map_subtype_commutator]
        exact mem_map_of_mem P.subtype hz
      have hl : embedM R (l:M)∈Ltilde R (alpha R) := by
        rw [Ltilde_alpha,s.residual]
        exact mem_map_of_mem (embedM R) l.property
      change embedM R (l:M)*(z:FreeAmalgam R)*(embedM R (l:M))⁻¹=(z:FreeAmalgam R)
      rw [(hfixed hz').2 _ hl,mul_inv_cancel_right])
  rw [←map_subtype_commutator,card_map_of_injective (Vcirc R (alpha R)).subtype_injective]
  exact hb
end Source
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
open Subgroup Theory.GroupTheory BinaryPermutation
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B:Subgroup K)

/-- The derived bound on the literal characteristic replacement, with its
marked central-quotient coordinates retained. -/
theorem reducedSource_movingRadius_derived_card_le_two
    (r : CharacteristicReduction (L.subgroupOf J) (d.B.subgroupOf J)) :
    let s := (originalSource d hm).reduce r
    ∀ (e : ((Vcirc r.radical (alpha r.radical)) ⧸
        center (Vcirc r.radical (alpha r.radical))) ≃*
        Multiplicative (natural (Fin 6))) (σ : Model.S≃*Model.S),
      (∀ (m : r.overgroup) (p : Vcirc r.radical (alpha r.radical)),
        (e (QuotientGroup.mk' (center (Vcirc r.radical (alpha r.radical)))
          (movingRadiusAction r.radical m p))).toAdd=
        naturalRepresentation (Fin 6) (σ (s.projection m))
          (e (QuotientGroup.mk' (center (Vcirc r.radical (alpha r.radical))) p)).toAdd) →
      ⁅Vcirc r.radical (alpha r.radical),Vcirc r.radical (alpha r.radical)⁆≤
        fixedCore r.radical (alpha r.radical) →
      Nat.card (⁅Vcirc r.radical (alpha r.radical),Vcirc r.radical (alpha r.radical)⁆:
        Subgroup (FreeAmalgam r.radical))≤2 := by
  intro s e σ he hf
  exact s.movingRadius_derived_card_le_two e σ he hf
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
