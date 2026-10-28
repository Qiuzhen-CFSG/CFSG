module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductAction
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.RootPairPlacement

/-!
# The source rank-one subgroup moves the original Thompson central omega

The exact root coordinates and all natural indices share a single quotient
marking. The root-pair envelope moves the full Sylow fixed subgroup by its
two-residual. The ordinary Thompson containment puts that fixed subgroup
inside the original Thompson central omega, proving clause (iii) along
with the rank-one quotient and Sylow clauses (i)--(ii). Thompson heredity
identifies both the central omega and Baumann subgroup of that Sylow with
the originals. The same full-kernel marking places F in a concrete point
parabolic.

Every subgroup is mapped through the literal vertex inclusion and retains
all of Q. The field degree remains n. Source: MS93 (5.1), printed p.913.
The selected-path parabolic alignment and generation, Baumann-Sylow construction F₀,
Niles application and distance-two exclusion remain further obligations.
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

/-- Source (5.1), clauses (i)--(iii): the actual rank-one overgroup has the
full small-mover Sylow and its two-residual moves the original Thompson
central omega. It contains Q and lies in a marked point parabolic; its
Sylow has the original Baumann subgroup and Thompson central omega.
This is F; the Baumann-Sylow subgroup F₀ remains separate. -/
theorem Input.replacement_root_product_moving_rank_one
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
      ∃ I : Subgroup (FreeAmalgam d.radical), I ≤ stabilizer d.radical a ∧ Q d.radical a ≤ I ∧
      ∃ S : Sylow 2 I,
        (S : Subgroup I).map I.subtype =
          Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t)
            (Nat.card F ^ 2) ∧
        Nonempty ((I ⧸ pCore 2 I) ≃* Matrix.SpecialLinearGroup (Fin 2) E.Carrier) ∧
        ⁅U d.radical a ⊓ centralizer
            (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t)
              (Nat.card F ^ 2) : Set (FreeAmalgam d.radical)),
          (pResidual 2 I).map I.subtype⁆ ≠ ⊥ ∧
        ⁅omegaCenterIn (thompsonSubgroup (Q d.radical t)),
          (pResidual 2 I).map I.subtype⁆ ≠ ⊥ ∧
        (Glauberman.baumannSubgroup (S : Subgroup I)).map I.subtype =
          Glauberman.baumannSubgroup (Q d.radical t) ∧
        (omegaCenterIn (thompsonSubgroup (S : Subgroup I))).map I.subtype =
          omegaCenterIn (thompsonSubgroup (Q d.radical t)) ∧
        ∃ κ : stabilizer d.radical a →* Sp E.Carrier,
          Function.Surjective κ ∧
          κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
          (I.subgroupOf (stabilizer d.radical a)).map κ ≤
            Theory.SpecificGroups.SymplecticFour.stabilizer (E.Carrier ∙ Theory.SpecificGroups.SymplecticFour.e 1) := by
  obtain ⟨E,hE,f,hf,hfQ,hindex,s₁,s₂,hs₁,hs₂,hJimage,hJE⟩ :=
    h.replacement_root_product_action_coordinates d geometry hb ha hat E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
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
  let U₀ := (U d.radical a).subgroupOf V
  obtain ⟨I,hJI,P,hP,⟨eP⟩,hmoves,g,hplace⟩ := RootEnvelope.exists_moving_root_pair_envelope_in_point_parabolic
    f hf hk U₀ J₀ hkJ s₁ s₂ hJi hindex
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
  have hUS : U d.radical a ≤ V := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hUT : U₀.map V.subtype = U d.radical a := map_subgroupOf_eq_of_le hUS
  have hJm : J₀.map V.subtype = J := map_subgroupOf_eq_of_le hJS
  have hmoves' : ⁅U d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical)),
      (pResidual 2 (I.map V.subtype)).map (I.map V.subtype).subtype⁆ ≠ ⊥ := by
    intro hz
    apply hmoves
    apply (Subgroup.map_eq_bot_iff_of_injective _ V.subtype_injective).mp
    rw [map_commutator,←map_inf_centralizer_of_injective V.subtype V.subtype_injective,
      hUT,hJm,map_embedded_pResidual,hz]
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hUQ : U d.radical a ≤ Q d.radical a := (U_le_Z a).trans
    (Z_le_Q_of_dist_lt d.radical a (geometry.exists_critical a ha) (by
      rw [SimpleGraph.dist_self,geometry.distance_constant a ha]
      change 0 < geometry.b d.radical
      omega))
  let T := (Q d.radical t).subgroupOf V
  have hTT : T.map V.subtype = Q d.radical t := map_subgroupOf_eq_of_le hTS
  obtain ⟨M,hM,hJM,hTh,hBa,hne,hn₁,hn₂⟩ := h.replacement_root_product_baumann_control
    d geometry hb ha hat E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  have hThJ : thompsonSubgroup (Q d.radical t) ≤ J := by
    change thompsonSubgroup (Q d.radical t) ≤ Subgroup.SmallMover.join _ _ _ _
    rw [hJM]
    exact hTh
  have hTh₀ : thompsonSubgroup T ≤ J₀ := by
    apply (map_le_map_iff_of_injective V.subtype_injective).mp
    rw [Glauberman.thompson_map_injective T V.subtype V.subtype_injective,hTT,hJm]
    exact hThJ
  let : IsElementaryAbelian 2 (Z d.radical a) := geometry.Z_elementary (by omega) a ha
  let : IsElementaryAbelian 2 (U d.radical a) := IsElementaryAbelian.of_le (U_le_Z a)
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.subgroupOf hUS
  have hfixed := Glauberman.smallMover_fixed_le_thompson_omega U₀ T J₀
    (comap_mono (hUQ.trans hQT)) hTh₀
  have hfixed' := map_mono (f := V.subtype) hfixed
  rw [←map_inf_centralizer_of_injective V.subtype V.subtype_injective,hUT,hJm,
    Glauberman.omegaCenterIn_map_injective _ V.subtype V.subtype_injective,
    Glauberman.thompson_map_injective T V.subtype V.subtype_injective,hTT] at hfixed'
  have hThEq : thompsonSubgroup J₀ = thompsonSubgroup T :=
    thompsonSubgroup_eq_of_le (comap_mono (Subgroup.SmallMover.join_le _ _ _ _)) hTh₀
  have hThEq' := congrArg (Subgroup.map V.subtype) hThEq
  rw [Glauberman.thompson_map_injective J₀ V.subtype V.subtype_injective,
    Glauberman.thompson_map_injective T V.subtype V.subtype_injective,hJm,hTT] at hThEq'
  have hBaJ : Glauberman.baumannSubgroup (Q d.radical t) ≤ J := by
    change Glauberman.baumannSubgroup (Q d.radical t) ≤ Subgroup.SmallMover.join _ _ _ _
    rw [hJM]
    exact hBa
  have hBJ : Glauberman.baumannSubgroup J = Glauberman.baumannSubgroup (Q d.radical t) := by
    unfold Glauberman.baumannSubgroup
    rw [hThEq']
    exact le_antisymm (inf_le_inf_right _ (Subgroup.SmallMover.join_le _ _ _ _))
      (le_inf hBaJ inf_le_right)
  refine ⟨E,hE,I.map V.subtype,map_subtype_le _,hQJ.trans (hs ▸ map_subtype_le _),
    S,hs,⟨eqQ.trans eP⟩,hmoves',?_,?_,?_,?_⟩
  · intro hz
    exact hmoves' (bot_unique ((commutator_mono hfixed' le_rfl).trans_eq hz))
  · rw [Glauberman.baumann_map_injective _ _ (I.map V.subtype).subtype_injective,hs,hBJ]
  · rw [Glauberman.omegaCenterIn_map_injective _ _ (I.map V.subtype).subtype_injective,
      Glauberman.thompson_map_injective _ _ (I.map V.subtype).subtype_injective,hs,hThEq']
  · let κ := (MulAut.conj g).toMonoidHom.comp f
    have hkκ : κ.ker = f.ker := by
      ext x
      change (MulAut.conj g) (f x)=1 ↔ f x=1
      exact (MulAut.conj g).map_eq_one_iff
    refine ⟨κ,(MulAut.conj g).surjective.comp hf,by rw [hkκ]; exact hfQ,?_⟩
    have hpre : (I.map V.subtype).subgroupOf V = I :=
      comap_map_eq_self (by rw [V.subtype.ker_eq_bot V.subtype_injective]; exact bot_le)
    rw [hpre]
    exact hplace

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
