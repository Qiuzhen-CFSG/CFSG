module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductBaumann
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.DegreeRootProduct
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.RootPairEnvelope


/-!
# Root-product coordinates retaining the whole natural action

The same inner marking both identifies the two full roots and computes
fixed indices for every vertex subgroup, including their rank-one
overgroup. A containing Sylow is aligned by conjugation; all natural
fixed indices are unchanged. The original degree and entire Q-kernel
remain attached to this single marking.

Source: MS93 (5.1), printed p.913, the action needed for clause (iii)
of the rank-one construction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The same quotient marking puts the actual edge in a containing Sylow
and computes all of its full centralizer indices. -/
theorem Input.replacement_small_mover_action_coordinates
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp E.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
              2 ^ fixedCodim (restrictScalars (k := ZMod 2)
                (symplecticNatural (k := E.Carrier) 2)) (A.map f)) ∧
        ∀ A : Subgroup (stabilizer d.radical a), A ≤ (Q d.radical t).subgroupOf (stabilizer d.radical a) →
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            movingIndex ((A.map f).subgroupOf unipotent) := by
  obtain ⟨E,hE,f,hf,hfQ,hidx⟩ := h.replacement_inner_natural_indices d geometry hb ha
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hpT : IsPGroup 2 (Q d.radical t) := hjR ▸ (h.replacement_two_group d).map j
  let T := (Q d.radical t).subgroupOf (stabilizer d.radical a)
  obtain ⟨S,hS⟩ := (hpT.comap_subtype.map f).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp E.Carrier) S
    (unipotentSylow (by rw [E.card_eq]) (by rw [hE]; exact h.nonbinary.le))
  have hSm : (S : Subgroup (Sp E.Carrier)).map (MulAut.conj g).toMonoidHom = unipotent :=
    congrArg (fun S : Sylow 2 (Sp E.Carrier) => (S : Subgroup (Sp E.Carrier))) hg
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hTf : T.map f' ≤ unipotent := by
    rw [←Subgroup.map_map]
    exact (map_mono hS).trans_eq hSm
  have hker : f'.ker = f.ker := by
    ext x
    change (MulAut.conj g) (f x) = 1 ↔ f x = 1
    exact (MulAut.conj g).map_eq_one_iff
  refine ⟨E,hE,f',(MulAut.conj g).surjective.comp hf,by rw [hker]; exact hfQ,hTf,?_,?_⟩
  · intro A
    rw [←Subgroup.map_map,fixedCodim_map_conj]
    exact hidx A
  · intro A hAT
    have hAf : A.map f' ≤ unipotent := (map_mono hAT).trans hTf
    let τ := restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)
    have hi : (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) = 2 ^ fixedCodim τ (A.map f') := by
      rw [←Subgroup.map_map, fixedCodim_map_conj]
      exact hidx A
    rw [hi,←binary_movingIndex]
    congr 1
    have hcomp : restrictScalars (k := ZMod 2) (natural (F := E.Carrier)) =
        τ.comp (unipotent (F := E.Carrier)).subtype := rfl
    rw [hcomp]
    rw [fixedCodim,fixedCodim,fixedSpace_comp_map,map_subgroupOf_eq_of_le hAf]
/-- The original product premise gives full root coordinates and equality
of the actual small-mover join with the two original subgroups' join. -/
theorem Input.replacement_root_product_action_coordinates
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (E₁ E₂ : Subgroup (FreeAmalgam d.radical))
    (hE₁ : E₁ ≤ Q d.radical t) (hE₂ : E₂ ≤ Q d.radical t)
    (hc₁ : (Q d.radical a).relIndex E₁ = Nat.card F)
    (hc₂ : (Q d.radical a).relIndex E₂ = Nat.card F)
    (hi₁ : (centralizer (E₁ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hi₂ : (centralizer (E₂ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hprod : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F ^ 2) : Set (FreeAmalgam d.radical)) ⊆
      (E₁ : Set (FreeAmalgam d.radical)) * (E₂ : Set (FreeAmalgam d.radical))) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp E.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
              2 ^ fixedCodim (restrictScalars (k := ZMod 2)
                (symplecticNatural (k := E.Carrier) 2)) (A.map f)) ∧
      ∃ s₁ s₂ : Option E.Carrier,
        ((E₁.subgroupOf (stabilizer d.radical a)).map f) = (rootFamily s₁).map unipotent.subtype ∧
        ((E₂.subgroupOf (stabilizer d.radical a)).map f) = (rootFamily s₂).map unipotent.subtype ∧
        (((Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t)
          (Nat.card F ^ 2)).subgroupOf (stabilizer d.radical a)).map f) =
            (rootFamily s₁ ⊔ rootFamily s₂).map unipotent.subtype ∧
        Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t)
          (Nat.card F ^ 2) = E₁ ⊔ E₂ := by
  obtain ⟨E,hE,f,hf,hfQ,hTf,hglobal,hidx⟩ := h.replacement_small_mover_action_coordinates d geometry hb ha hat
  have hcard : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  let S := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S
  let T := (Q d.radical t).subgroupOf S
  let J := Subgroup.SmallMover.join U₀ f.ker T (Nat.card E.Carrier ^ 2)
  let := finite_stabilizer d.radical a
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hTS : Q d.radical t ≤ S := by
    change Q d.radical t ≤ stabilizer d.radical a
    rw [←hjr,←hjR]
    exact map_le_range j _
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hQeq : f.ker = (Q d.radical a).subgroupOf S := by
    apply Subgroup.map_injective S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1)]
  have hkT : f.ker ≤ T := by rw [hQeq]; exact comap_mono hQT
  have hUK : U₀ ≤ centralizer (f.ker : Set S) := by
    intro u hu k hk
    apply Subtype.val_injective
    have hkQ : k.val ∈ Q d.radical a := hfQ ▸ mem_map_of_mem S.subtype hk
    exact ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha))
      (U_le_Z a hu) k.val hkQ)
  have hUT : U₀.map S.subtype = U d.radical a := map_subgroupOf_eq_of_le hUS
  have hTT : T.map S.subtype = Q d.radical t := map_subgroupOf_eq_of_le hTS
  have hjoin : J.map S.subtype = Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2) := by
    rw [Subgroup.SmallMover.join_map S.subtype S.subtype_injective,hUT,hfQ,hTT,hcard]
  have hJsub : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F ^ 2)).subgroupOf S = J := by
    rw [←hjoin]
    exact comap_map_eq_self (by rw [S.subtype.ker_eq_bot S.subtype_injective]; exact bot_le)
  have hES₁ := hE₁.trans hTS
  have hES₂ := hE₂.trans hTS
  have hc (A : Subgroup (FreeAmalgam d.radical)) (hAS : A ≤ S) :
      f.ker.relIndex (A.subgroupOf S) = (Q d.radical a).relIndex A := by
    rw [hQeq,relIndex_subgroupOf hAS]
  have hi (A : Subgroup (FreeAmalgam d.radical)) (hAS : A ≤ S) :
      (centralizer (A.subgroupOf S : Set S)).relIndex U₀ =
        (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    rw [←Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective,
      hUT,map_subgroupOf_eq_of_le hAS]
  have hp : (J : Set S) ⊆ (E₁.subgroupOf S : Set S) * (E₂.subgroupOf S : Set S) := by
    intro x hx
    obtain ⟨y,hy,z,hz,he⟩ := hprod (hjoin ▸ mem_map_of_mem S.subtype hx)
    exact ⟨⟨y,hES₁ hy⟩,hy,⟨z,hES₂ hz⟩,hz,Subtype.ext he⟩
  obtain ⟨s₁,s₂,hs₁,hs₂,hJ,heq⟩ := Degree.Quotient.root_product_join_eq U₀ T f
    unipotent.subtype Subtype.val_injective hkT hUK
    (by simpa only [range_subtype] using hTf) hidx
    (E₁.subgroupOf S) (E₂.subgroupOf S) (comap_mono hE₁) (comap_mono hE₂)
    (by rw [hc E₁ hES₁,hcard,hc₁]) (by rw [hi E₁ hES₁,hcard,hi₁])
    (by rw [hc E₂ hES₂,hcard,hc₂]) (by rw [hi E₂ hES₂,hcard,hi₂]) hp
  have hm (A : Subgroup S) (hAT : A ≤ T) :
      (Degree.Quotient.coordinates f unipotent.subtype A).map unipotent.subtype = A.map f :=
    Degree.Quotient.coordinates_map f unipotent.subtype A
      (by simpa only [range_subtype] using (map_mono hAT).trans hTf)
  refine ⟨E,hE,f,hf,hfQ,hglobal,s₁,s₂,?_,?_,?_,?_⟩
  · exact (hm (E₁.subgroupOf S) (comap_mono hE₁)).symm.trans
      (congrArg (Subgroup.map unipotent.subtype) hs₁)
  · exact (hm (E₂.subgroupOf S) (comap_mono hE₂)).symm.trans
      (congrArg (Subgroup.map unipotent.subtype) hs₂)
  · rw [hJsub,←hm _ (Subgroup.SmallMover.join_le _ _ _ _),hJ]
  · have hh := congrArg (fun A : Subgroup S => A.map S.subtype) heq
    rwa [hjoin,Subgroup.map_sup,map_subgroupOf_eq_of_le hES₁,
      map_subgroupOf_eq_of_le hES₂] at hh


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
