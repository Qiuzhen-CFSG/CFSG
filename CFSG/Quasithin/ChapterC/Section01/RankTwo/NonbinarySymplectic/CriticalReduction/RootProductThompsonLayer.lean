module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductClosure
public import Glauberman.AllAbelianBaumannReplacement
public import Glauberman.SymplecticSharpReplacement

/-!
# The full all-abelian Baumann layer on the actual replacement

The source q² small-mover bound makes every maximum abelian offender sharp.
Each replacement (A intersect Q_alpha) U_alpha has the same maximum order,
so the full maximum family of Q_alpha is retained in T_beta. The central
omega of J(T_beta) and the whole natural layer lie in the central omega
of J(Q_alpha). Their join is elementary and normal in the original vertex
stabilizer: the nontrivial Thompson image normally generates its simple
symplectic quotient. In particular this entire enlarged layer lies in
Q_alpha. All central attachments and the original field degree are retained.

These are all-abelian preparations for the Baumann step in MS93 (5.1),
printed p.913. They do not identify the Sylow of the Baumann normal closure
with the Baumann subgroup; F₀ and the subsequent Niles exclusion remain open.
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

/-- The full ordinary Thompson replacement and enlarged central omega layer
under the source small-mover bound, on the original replacement graph. -/
theorem Input.replacement_thompson_omega_layer
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (hbound : (Q d.radical a).relIndex
      (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t)
        (Nat.card F ^ 2)) ≤ Nat.card F ^ 2) :
    (∀ A ∈ thompsonAbelianSubgroups (Q d.radical t),
      (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) =
        (Q d.radical a).relIndex A ∧
      A ⊓ Q d.radical a ⊔ U d.radical a ∈ thompsonAbelianSubgroups (Q d.radical t)) ∧
    thompsonAbelianSubgroups (Q d.radical a) ⊆ thompsonAbelianSubgroups (Q d.radical t) ∧
    U d.radical a ≤ omegaCenterIn (thompsonSubgroup (Q d.radical a)) ∧
    omegaCenterIn (thompsonSubgroup (Q d.radical t)) ≤
      omegaCenterIn (thompsonSubgroup (Q d.radical a)) ∧
    IsElementaryAbelian 2
      (omegaCenterIn (thompsonSubgroup (Q d.radical t)) ⊔ U d.radical a : Subgroup _) ∧
    stabilizer d.radical a ≤ normalizer
      ((omegaCenterIn (thompsonSubgroup (Q d.radical t)) ⊔ U d.radical a : Subgroup _) : Set _) ∧
    omegaCenterIn (thompsonSubgroup (Q d.radical t)) ⊔ U d.radical a ≤ Q d.radical a ∧
    ⁅omegaCenterIn (thompsonSubgroup (Q d.radical t)) ⊔ U d.radical a,
      Ltilde d.radical a⁆ ≤ U d.radical a ∧
    ⁅omegaCenterIn (thompsonSubgroup (Q d.radical a)),Ltilde d.radical a⁆ = U d.radical a := by
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
  have hUQ : U d.radical a ≤ Q d.radical a := (U_le_Z a).trans
    (Z_le_Q_of_dist_lt d.radical a (geometry.exists_critical a ha) (by
      rw [SimpleGraph.dist_self,geometry.distance_constant a ha]
      change 0 < geometry.b d.radical
      omega))
  have hUk : U₀ ≤ f.ker := by rw [hQeq]; exact comap_mono hUQ
  let : IsElementaryAbelian 2 (Z d.radical a) := geometry.Z_elementary (by omega) a ha
  let : IsElementaryAbelian 2 (U d.radical a) := IsElementaryAbelian.of_le (U_le_Z a)
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.subgroupOf hUS
  let : U₀.Normal := (normal_subgroupOf_iff_le_normalizer hUS).mpr (U_normalized a)
  have hUT : U₀.map S.subtype = U d.radical a := map_subgroupOf_eq_of_le hUS
  have hTT : T.map S.subtype = Q d.radical t := map_subgroupOf_eq_of_le hTS
  have hjoin : J.map S.subtype = Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2) := by
    rw [Subgroup.SmallMover.join_map S.subtype S.subtype_injective,hUT,hfQ,hTT,hcard]
  have hbound' : f.ker.relIndex J ≤ Nat.card E.Carrier ^ 2 := by
    rw [←relIndex_map_map_of_injective f.ker J S.subtype_injective,hfQ,hjoin,hcard]
    exact hbound
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 3<2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hsharp : ∀ A ∈ thompsonAbelianSubgroups T,
      (centralizer (A : Set S)).relIndex U₀ = f.ker.relIndex A :=
    Degree.Quotient.maximum_abelian_sharp_of_smallMover_bound U₀ T f
      unipotent.subtype Subtype.val_injective hkT hUk hUK
      (by simpa only [range_subtype] using hTf) hidx (by omega) hbound'
  have hcontrol := Glauberman.thompson_omega_replacement_control T f.ker U₀ hkT hUk hUK hsharp
  have hTh : ¬ thompsonSubgroup T ≤ f.ker := by
    intro hh
    have hh' := map_mono (f := S.subtype) hh
    rw [Glauberman.thompson_map_injective _ _ S.subtype_injective,hTT,hfQ] at hh'
    apply h.replacement_all_abelian_thompson_not_le d
    apply (map_le_map_iff_of_injective hj).mp
    rw [Glauberman.thompson_map_injective _ j hj,hjR,hjQ]
    exact hh'
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hlarge
  let : IsSimpleGroup (Sp E.Carrier) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  let W := omegaCenterIn (thompsonSubgroup T) ⊔ U₀
  let : W.Normal := Glauberman.thompson_omega_enlargement_normal_of_simple_image
    T U₀ f hf hkT hUk hUK hTh hsharp
  let : IsElementaryAbelian 2 W := hcontrol.2.2.2
  have hWm : W.map S.subtype = omegaCenterIn (thompsonSubgroup (Q d.radical t)) ⊔ U d.radical a := by
    rw [Subgroup.map_sup,Glauberman.omegaCenterIn_map_injective _ _ S.subtype_injective,
      Glauberman.thompson_map_injective _ _ S.subtype_injective,hTT,hUT]
  have hAm : (omegaCenterIn (thompsonSubgroup T)).map S.subtype =
      omegaCenterIn (thompsonSubgroup (Q d.radical t)) := by
    rw [Glauberman.omegaCenterIn_map_injective _ _ S.subtype_injective,
      Glauberman.thompson_map_injective _ _ S.subtype_injective,hTT]
  have hQm : (omegaCenterIn (thompsonSubgroup f.ker)).map S.subtype =
      omegaCenterIn (thompsonSubgroup (Q d.radical a)) := by
    rw [Glauberman.omegaCenterIn_map_injective _ _ S.subtype_injective,
      Glauberman.thompson_map_injective _ _ S.subtype_injective,hfQ]
  have hnorm : S ≤ normalizer (W.map S.subtype : Set (FreeAmalgam d.radical)) := by
    have hh := W.le_normalizer_map S.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  have hWQ : W.map S.subtype ≤ Q d.radical a := by
    let j' : d.overgroup →* S := j.codRestrict S (fun x => by
      change j x ∈ stabilizer d.radical a
      rw [←hjr]
      exact ⟨x,rfl⟩)
    have hj' : Function.Injective j' := fun x y he => hj (congrArg Subtype.val he)
    have hsurj : Function.Surjective j' := by
      intro x
      obtain ⟨y,hy⟩ := (show x.val ∈ j.range from hjr.symm ▸ x.property)
      exact ⟨y,Subtype.ext hy⟩
    have hpre : W.comap j' ≤ pCore 2 d.overgroup :=
      le_sSup ⟨inferInstance,(IsElementaryAbelian.isPGroup 2 W).comap_of_injective j' hj'⟩
    have hm := map_mono (f := j') hpre
    rw [map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr hsurj]; exact le_top)] at hm
    have hh := map_mono (f := S.subtype) hm
    rw [Subgroup.map_map] at hh
    change W.map S.subtype ≤ (pCore 2 d.overgroup).map j at hh
    rwa [hjQ] at hh
  have hk : IsPGroup 2 f.ker := by
    have hp : IsPGroup 2 (Q d.radical a) := hjQ ▸ pCore_isPGroup.map j
    exact (hfQ.symm ▸ hp).of_injective
      (f.ker.equivMapOfInjective S.subtype S.subtype_injective).toMonoidHom
      (f.ker.equivMapOfInjective S.subtype S.subtype_injective).injective
  have hres := Glauberman.thompson_omega_residual_control T U₀ f hf hk
    hkT hUk hUK hTh hsharp
  have hres' := map_mono (f := S.subtype) hres.2
  rw [map_commutator,hWm,hUT] at hres'
  have hkernel := map_mono (f := S.subtype) hres.1
  rw [map_commutator,hQm,hUT] at hkernel
  have hZQ : Z d.radical a ≤ Q d.radical a :=
    Z_le_Q_of_dist_lt d.radical a (geometry.exists_critical a ha) (by
      rw [SimpleGraph.dist_self,geometry.distance_constant a ha]
      change 0 < geometry.b d.radical
      omega)
  let Z₀ := (Z d.radical a).subgroupOf S
  let : IsElementaryAbelian 2 Z₀ := IsElementaryAbelian.subgroupOf (Z_le_stabilizer d.radical a)
  have hZk : Z₀ ≤ f.ker := by rw [hQeq]; exact comap_mono hZQ
  have hZc : Z₀ ≤ centralizer (f.ker : Set S) := by
    intro z hz k hk
    apply Subtype.val_injective
    exact ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha))
      hz k.val (hfQ ▸ mem_map_of_mem S.subtype hk))
  have hZa := Glauberman.smallMover_fixed_le_thompson_omega Z₀ f.ker f.ker hZk
    (thompsonSubgroup_le f.ker)
  rw [inf_eq_left.mpr hZc] at hZa
  have hZa' := map_mono (f := S.subtype) hZa
  rw [map_subgroupOf_eq_of_le (Z_le_stabilizer d.radical a),hQm] at hZa'
  have hexact : ⁅omegaCenterIn (thompsonSubgroup (Q d.radical a)),Ltilde d.radical a⁆ = U d.radical a :=
    le_antisymm hkernel (commutator_mono hZa' le_rfl)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,hres',hexact⟩
  · intro A hA
    have hAS := hA.1.trans hTS
    have hmap : (A.subgroupOf S).map S.subtype = A := map_subgroupOf_eq_of_le hAS
    have hA₀ : A.subgroupOf S ∈ thompsonAbelianSubgroups T :=
      (Glauberman.maximum_abelian_map_iff_of_injective S.subtype S.subtype_injective).mp
        (by rw [hmap,hTT]; exact hA)
    have hs := hsharp _ hA₀
    have hfixed : (centralizer (A.subgroupOf S : Set S)).relIndex U₀ =
        (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
      rw [←inf_relIndex_left U₀,←relIndex_map_map_of_injective _ _ S.subtype_injective,
        ←map_inf_centralizer_of_injective S.subtype S.subtype_injective,hUT,hmap,inf_relIndex_left]
    have hi : f.ker.relIndex (A.subgroupOf S) = (Q d.radical a).relIndex A := by
      rw [hQeq,relIndex_subgroupOf hAS]
    refine ⟨by rwa [hfixed,hi] at hs,?_⟩
    have hr := (Glauberman.maximum_abelian_replacement_of_sharp hA₀ hkT hUk
      inferInstance hUK (hsharp _ hA₀)).1
    have hm := Glauberman.maximum_abelian_map_of_injective S.subtype S.subtype_injective hr
    rwa [Subgroup.map_sup,Subgroup.map_inf _ _ _ S.subtype_injective,hmap,hfQ,hUT,hTT] at hm
  · intro A hA
    have hAS := hA.1.trans (hQT.trans hTS)
    have hmap : (A.subgroupOf S).map S.subtype = A := map_subgroupOf_eq_of_le hAS
    have hA₀ : A.subgroupOf S ∈ thompsonAbelianSubgroups f.ker :=
      (Glauberman.maximum_abelian_map_iff_of_injective S.subtype S.subtype_injective).mp
        (by rw [hmap,hfQ]; exact hA)
    have hm := Glauberman.maximum_abelian_map_of_injective S.subtype S.subtype_injective (hcontrol.1 hA₀)
    rwa [hmap,hTT] at hm
  · have hh := map_mono (f := S.subtype) hcontrol.2.1
    rwa [hUT,hQm] at hh
  · have hh := map_mono (f := S.subtype) hcontrol.2.2.1
    rwa [hAm,hQm] at hh
  · rw [←hWm]
    exact IsElementaryAbelian.map S.subtype
  · simpa only [hWm] using hnorm
  · simpa only [hWm] using hWQ

/-- The literal root-product premise supplies the entire enlarged omega layer
and identifies the moved part of the ordinary Thompson omega of Q_alpha.
No Sylow assertion about the original edge or its Baumann closure is assumed. -/
theorem Input.replacement_root_product_thompson_layer
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
    thompsonAbelianSubgroups (Q d.radical a) ⊆ thompsonAbelianSubgroups (Q d.radical t) ∧
    IsElementaryAbelian 2
      (omegaCenterIn (thompsonSubgroup (Q d.radical t)) ⊔ U d.radical a : Subgroup _) ∧
    stabilizer d.radical a ≤ normalizer
      ((omegaCenterIn (thompsonSubgroup (Q d.radical t)) ⊔ U d.radical a : Subgroup _) : Set _) ∧
    omegaCenterIn (thompsonSubgroup (Q d.radical t)) ⊔ U d.radical a ≤ Q d.radical a ∧
    ⁅omegaCenterIn (thompsonSubgroup (Q d.radical t)) ⊔ U d.radical a,
      Ltilde d.radical a⁆ ≤ U d.radical a ∧
    ⁅omegaCenterIn (thompsonSubgroup (Q d.radical a)),Ltilde d.radical a⁆ = U d.radical a := by
  obtain ⟨J,_,hJ,hbound,_,_⟩ := h.replacement_root_product_unique_maximum d geometry hb
    ha hat E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  have hh := h.replacement_thompson_omega_layer d geometry hb ha hat (by rwa [hJ])
  exact ⟨hh.2.1,hh.2.2.2.2⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
