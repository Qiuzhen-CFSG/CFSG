module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductBaumann
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.DegreeRootProduct
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.RootPairEnvelope

/-!
# The exact root product and its rank-one overgroup on the replacement

A failed source root-product exclusion identifies each image with a full
transvection root, and identifies the entire small-mover join with their
join. Explicit symplectic conjugations put this image in standard position.
The first hyperbolic-plane SL₂, together with the other root when needed,
then supplies a rank-one overgroup. Its full preimage has the original
small-mover join as its Sylow subgroup and quotient SL₂ at the original
field degree. Mapping back to the free-amalgam stabilizer retains the
whole original Q-kernel.

This proves the exact root configuration and clauses (i)--(ii) for F in
MS93 (5.1), printed p.913. The Thompson central-omega noncentrality clause,
the parabolic generation witnesses, the Baumann-Sylow subgroup F₀ and the
Niles conclusion remain to be proved. Consequently this module does not
assert (5.1)'s exclusion or the requested distance-two witness.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
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

/-- The original product premise gives full root coordinates and equality
of the actual small-mover join with the two original subgroups' join. -/
theorem Input.replacement_root_product_coordinates
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
      ∃ s₁ s₂ : Option E.Carrier,
        ((E₁.subgroupOf (stabilizer d.radical a)).map f) = (rootFamily s₁).map unipotent.subtype ∧
        ((E₂.subgroupOf (stabilizer d.radical a)).map f) = (rootFamily s₂).map unipotent.subtype ∧
        (((Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t)
          (Nat.card F ^ 2)).subgroupOf (stabilizer d.radical a)).map f) =
            (rootFamily s₁ ⊔ rootFamily s₂).map unipotent.subtype ∧
        Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t)
          (Nat.card F ^ 2) = E₁ ⊔ E₂ := by
  obtain ⟨E,hE,f,hf,hfQ,hTf,hidx⟩ := h.replacement_small_mover_coordinates d geometry hb ha hat
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
    apply map_injective S.subtype_injective
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
  refine ⟨E,hE,f,hf,hfQ,s₁,s₂,?_,?_,?_,?_⟩
  · exact (hm (E₁.subgroupOf S) (comap_mono hE₁)).symm.trans
      (congrArg (Subgroup.map unipotent.subtype) hs₁)
  · exact (hm (E₂.subgroupOf S) (comap_mono hE₂)).symm.trans
      (congrArg (Subgroup.map unipotent.subtype) hs₂)
  · rw [hJsub,←hm _ (Subgroup.SmallMover.join_le _ _ _ _),hJ]
  · have hh := congrArg (fun A : Subgroup S => A.map S.subtype) heq
    rwa [hjoin,Subgroup.map_sup,map_subgroupOf_eq_of_le hES₁,
      map_subgroupOf_eq_of_le hES₂] at hh

/-- The source root-product premise constructs a genuine rank-one subgroup
of the original vertex stabilizer, with the entire maximum-small-mover
join as a Sylow subgroup. This is F, not yet the Baumann-Sylow subgroup F₀. -/
theorem Input.replacement_root_product_rank_one
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
      ∃ I : Subgroup (FreeAmalgam d.radical), I ≤ stabilizer d.radical a ∧
      ∃ S : Sylow 2 I,
        (S : Subgroup I).map I.subtype =
          Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t)
            (Nat.card F ^ 2) ∧
        Nonempty ((I ⧸ pCore 2 I) ≃* Matrix.SpecialLinearGroup (Fin 2) E.Carrier) := by
  obtain ⟨E,hE,f,hf,hfQ,s₁,s₂,hs₁,hs₂,hJimage,hJE⟩ :=
    h.replacement_root_product_coordinates d geometry hb ha hat E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  let V := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2)
  let J₀ := J.subgroupOf V
  let := finite_stabilizer d.radical a
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hTS : Q d.radical t ≤ V := by
    change Q d.radical t ≤ stabilizer d.radical a
    rw [←hjr,←hjR]
    exact map_le_range j _
  have hJS : J ≤ V := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  have hQJ : Q d.radical a ≤ J := by
    have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
      (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
      (Nat.card F ^ 2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
      (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
        (h.replacement_two_group d) (h.replacement_core_le d)))
    rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh
  have hkJ : f.ker ≤ J₀ := by
    intro x hx
    exact hQJ (hfQ ▸ mem_map_of_mem V.subtype hx)
  have hk : IsPGroup 2 f.ker := by
    have hq : IsPGroup 2 (Q d.radical a) := hjQ ▸
      (show IsPGroup 2 (pCore 2 d.overgroup) from pCore_isPGroup).map j
    have hqm : IsPGroup 2 (f.ker.map V.subtype) := hfQ ▸ hq
    let e := f.ker.equivMapOfInjective V.subtype V.subtype_injective
    exact hqm.of_injective e.toMonoidHom e.injective
  have hJi : J₀.map f = rootImage s₁ ⊔ rootImage s₂ := by
    simpa only [Subgroup.map_sup] using hJimage
  obtain ⟨I,hJI,P,hP,⟨eP⟩⟩ := RootEnvelope.exists_root_pair_preimage_envelope
    f hf hk J₀ hkJ s₁ s₂ hJi
  let e := I.equivMapOfInjective V.subtype V.subtype_injective
  let : Finite (I.map V.subtype) := Finite.of_surjective e e.surjective
  let S : Sylow 2 (I.map V.subtype) := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hs : (S : Subgroup (I.map V.subtype)).map (I.map V.subtype).subtype = J := by
    change ((P : Subgroup I).map e.toMonoidHom).map (I.map V.subtype).subtype = _
    rw [Subgroup.map_map]
    change (P : Subgroup I).map (V.subtype.comp I.subtype) = _
    rw [←Subgroup.map_map,hP,map_subgroupOf_eq_of_le hJS]
  let eqQ := e.symm.toMonoidHom.pCoreQuotientEquiv e.symm.surjective
    (IsPGroup.ker_isPGroup_of_injective (p := 2) e.symm.injective)
  exact ⟨E,hE,I.map V.subtype,map_subtype_le _,S,hs,⟨eqQ.trans eP⟩⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
