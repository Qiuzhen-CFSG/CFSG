module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootPairKernel
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.DegreeAbelian

/-!
# Distinct full root actors in one original vertex marking

Two full actors in the same edge with image and fixed index q are full
transvection roots in one natural marking. Distinct fixed kernels on the
whole vertex Z force distinct root images, so their join has order q².
If the entire maximum-small-mover image had order at most q², the model's
small-actor inclusion theorem would force equality with this root pair.
The original root-product exclusion forbids that equality.

All quotient kernels and central attachments are retained. The two full
actors are supplied by the actual common-edge path construction; no
arbitrary small actor is placed in the maximum-order join without its
proved order bound. Source: MS93 (5.12)(3), printed p.927, using (5.1).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Distinct full fixed kernels force two distinct full root images in one
marking, and exclude a square-order image for the actual mover join. -/
theorem Input.replacement_distinct_root_actor_coordinates
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t)
    (E₁ E₂ : Subgroup (FreeAmalgam d.radical))
    (hE₁ : E₁ ≤ Q d.radical t) (hE₂ : E₂ ≤ Q d.radical t)
    (hc₁ : (Q d.radical a).relIndex E₁=Nat.card F)
    (hc₂ : (Q d.radical a).relIndex E₂=Nat.card F)
    (hi₁ : (centralizer (E₁ : Set (FreeAmalgam d.radical))).relIndex (U d.radical a)=Nat.card F)
    (hi₂ : (centralizer (E₂ : Set (FreeAmalgam d.radical))).relIndex (U d.radical a)=Nat.card F)
    (hne : Z d.radical a ⊓ centralizer (E₁ : Set (FreeAmalgam d.radical)) ≠
      Z d.radical a ⊓ centralizer (E₂ : Set (FreeAmalgam d.radical))) :
    ∃ E : BinaryField, E.degree=n ∧
      ∃ f : stabilizer d.radical a →* Sp E.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype=Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
              2 ^ fixedCodim (restrictScalars (k := ZMod 2)
                (symplecticNatural (k := E.Carrier) 2)) (A.map f)) ∧
        ∃ s₁ s₂ : Option E.Carrier, s₁ ≠ s₂ ∧
          (E₁.subgroupOf (stabilizer d.radical a)).map f=rootImage s₁ ∧
          (E₂.subgroupOf (stabilizer d.radical a)).map f=rootImage s₂ ∧
          Nat.card (rootImage s₁ ⊔ rootImage s₂ : Subgroup (Sp E.Carrier))=Nat.card F^2 ∧
          (Q d.radical a).relIndex (E₁ ⊔ E₂)=Nat.card F^2 ∧
          Nat.card F^2 < (Q d.radical a).relIndex
            (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
              (Q d.radical t) (Nat.card F^2)) := by
  obtain ⟨E,hE,f,hf,hfQ,hTf,hglobal,hidx⟩ :=
    h.replacement_small_mover_action_coordinates d geometry hb ha hat
  have hcard : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  let S := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S
  let T := (Q d.radical t).subgroupOf S
  let J := Subgroup.SmallMover.join U₀ f.ker T (Nat.card E.Carrier^2)
  let A₁ := E₁.subgroupOf S
  let A₂ := E₂.subgroupOf S
  let C := Degree.Quotient.coordinates f unipotent.subtype
  let := finite_stabilizer d.radical a
  have hTS : Q d.radical t ≤ S := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hES₁ : E₁ ≤ S := hE₁.trans hTS
  have hES₂ : E₂ ≤ S := hE₂.trans hTS
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  obtain ⟨j,_,_,hjR,hjQ,_⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hQeq : f.ker=(Q d.radical a).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1)]
  have hkT : f.ker ≤ T := by rw [hQeq]; exact comap_mono hQT
  have hUK : U₀ ≤ centralizer (f.ker : Set S) := by
    intro u hu k hk
    apply Subtype.val_injective
    have hkQ : k.val ∈ Q d.radical a := hfQ ▸ mem_map_of_mem S.subtype hk
    exact (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha))
      (U_le_Z a hu) k.val hkQ
  have hUT : U₀.map S.subtype=U d.radical a := map_subgroupOf_eq_of_le hUS
  have hTT : T.map S.subtype=Q d.radical t := map_subgroupOf_eq_of_le hTS
  have hTi : T.map f ≤ unipotent.subtype.range := by simpa only [range_subtype] using hTf
  have hjoin : J.map S.subtype=Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2) := by
    rw [Subgroup.SmallMover.join_map S.subtype S.subtype_injective,hUT,hfQ,hTT,hcard]
  have hJsub : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf S=J := by
    rw [←hjoin]
    exact comap_map_eq_self (by rw [S.subtype.ker_eq_bot S.subtype_injective]; exact bot_le)
  have hCmap (A : Subgroup S) (hAT : A ≤ T) : (C A).map unipotent.subtype=A.map f :=
    Degree.Quotient.coordinates_map f unipotent.subtype A ((map_mono hAT).trans hTi)
  have hCc (A : Subgroup S) (hAT : A ≤ T) : Nat.card (C A)=f.ker.relIndex A := by
    rw [relIndex_ker,←hCmap A hAT,card_map_of_injective unipotent.subtype_injective]
  have hc (A : Subgroup (FreeAmalgam d.radical)) (hAS : A ≤ S) :
      f.ker.relIndex (A.subgroupOf S)=(Q d.radical a).relIndex A := by
    rw [hQeq,relIndex_subgroupOf hAS]
  have hi (A : Subgroup (FreeAmalgam d.radical)) (hAS : A ≤ S) :
      (centralizer (A.subgroupOf S : Set S)).relIndex U₀=
        (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    rw [←Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective,
      hUT,map_subgroupOf_eq_of_le hAS]
  have hA₁ : A₁ ≤ T := comap_mono hE₁
  have hA₂ : A₂ ≤ T := comap_mono hE₂
  obtain ⟨s₁,hs₁⟩ := Degree.eq_rootFamily_of_field_indices (C A₁)
    (by rw [hCc A₁ hA₁,hc E₁ hES₁,hc₁,hcard])
    (by
      change movingIndex ((A₁.map f).subgroupOf unipotent)=Nat.card E.Carrier
      exact (hidx A₁ hA₁).symm.trans ((hi E₁ hES₁).trans (hi₁.trans hcard.symm)))
  obtain ⟨s₂,hs₂⟩ := Degree.eq_rootFamily_of_field_indices (C A₂)
    (by rw [hCc A₂ hA₂,hc E₂ hES₂,hc₂,hcard])
    (by
      change movingIndex ((A₂.map f).subgroupOf unipotent)=Nat.card E.Carrier
      exact (hidx A₂ hA₂).symm.trans ((hi E₂ hES₂).trans (hi₂.trans hcard.symm)))
  have hm₁ : A₁.map f=rootImage s₁ := by rw [←hCmap A₁ hA₁,hs₁]
  have hm₂ : A₂.map f=rootImage s₂ := by rw [←hCmap A₂ hA₂,hs₂]
  have hsne : s₁ ≠ s₂ := by
    intro he
    have hm : A₁.map f=A₂.map f := hm₁.trans ((congrArg rootImage he).trans hm₂.symm)
    have hp := congrArg (fun A : Subgroup (Sp E.Carrier) => A.comap f) hm
    rw [comap_map_eq,comap_map_eq] at hp
    have hamb := congrArg (fun A : Subgroup S => A.map S.subtype) hp
    rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hES₁,
      map_subgroupOf_eq_of_le hES₂,hfQ] at hamb
    have hsup : Q d.radical a ⊔ E₁=Q d.radical a ⊔ E₂ := by
      simpa only [sup_comm] using hamb
    have hZQ := commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha)
    apply hne
    rw [←Subgroup.SmallMover.fixed_inf_sup (Z d.radical a) (Q d.radical a) E₁ hZQ,
      ←Subgroup.SmallMover.fixed_inf_sup (Z d.radical a) (Q d.radical a) E₂ hZQ,hsup]
  have hpair : Nat.card (rootImage s₁ ⊔ rootImage s₂ : Subgroup (Sp E.Carrier))=Nat.card F^2 := by
    change Nat.card ((rootFamily s₁).map unipotent.subtype ⊔
      (rootFamily s₂).map unipotent.subtype : Subgroup (Sp E.Carrier))=_
    rw [←Subgroup.map_sup,card_map_of_injective unipotent.subtype_injective,
      rootFamily_sup_card hsne,hcard]
  have hpairIndex : (Q d.radical a).relIndex (E₁ ⊔ E₂)=Nat.card F^2 := by
    rw [←hc (E₁ ⊔ E₂) (sup_le hES₁ hES₂),relIndex_ker,
      subgroupOf_sup hES₁ hES₂,Subgroup.map_sup,hm₁,hm₂,hpair]
  refine ⟨E,hE,f,hf,hfQ,hTf,hglobal,s₁,s₂,hsne,hm₁,hm₂,hpair,hpairIndex,?_⟩
  apply Nat.lt_of_not_ge
  intro hbound
  have hCJ := Degree.Quotient.coordinates_join U₀ T f unipotent.subtype
    unipotent.subtype_injective hkT hUK hTi hidx
  change C J=Degree.join (C T) at hCJ
  have hcb : Nat.card (Degree.join (C T)) ≤ Nat.card E.Carrier^2 := by
    rw [←hCJ,hCc J (Subgroup.SmallMover.join_le _ _ _ _),
      ←relIndex_map_map_of_injective f.ker J S.subtype_injective,hfQ,hjoin,hcard]
    exact hbound
  have hrt : rootFamily s₁ ⊔ rootFamily s₂ ≤ C T := by
    rw [←hs₁,←hs₂]
    exact sup_le (comap_mono (map_mono hA₁)) (comap_mono (map_mono hA₂))
  have hrj := Degree.small_le_join_of_card_le_square hcb hrt (Degree.small_rootFamily_sup s₁ s₂)
  have heq : Degree.join (C T)=rootFamily s₁ ⊔ rootFamily s₂ :=
    (eq_of_le_of_card_ge hrj (by rw [rootFamily_sup_card hsne]; exact hcb)).symm
  have hJimage : ((Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf S).map f = rootImage s₁ ⊔ rootImage s₂ := by
    rw [hJsub,←hCmap J (Subgroup.SmallMover.join_le _ _ _ _),hCJ,heq,Subgroup.map_sup]
  exact h.replacement_small_mover_not_root_pair d geometry hb ha hat E hE f hf hfQ hglobal s₁ s₂ hJimage

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
