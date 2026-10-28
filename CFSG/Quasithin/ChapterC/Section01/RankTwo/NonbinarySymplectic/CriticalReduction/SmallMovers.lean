module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.NaturalIndex
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.DegreeQuotient

/-!
# The actual replacement small-mover family at every nonbinary degree

A containing Sylow subgroup supplies coordinates for the replacement edge
image; no Sylow property of the replacement edge is assumed. Exact indices
on the full U-layer identify its maximum small movers with the arbitrary-
degree model. Thus either there is one maximum mover, or there are exactly
q+1, their join is the whole original edge kernel, and that edge has relative
order q³ modulo the original vertex kernel.

This proves the multiple-maximum branch of MS93 (5.4), printed p.915, on
the actual Section 7 replacement. The unique branch still requires (5.1)
and the source's maximizing parabolic choice before invoking (5.5)--(5.6).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
open CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The same quotient marking puts the actual edge in a containing Sylow
and computes all of its full centralizer indices. -/
theorem Input.replacement_small_mover_coordinates
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp E.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
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
  refine ⟨E,hE,f',(MulAut.conj g).surjective.comp hf,by rw [hker]; exact hfQ,hTf,?_⟩
  intro A hAT
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

omit h d in
private theorem maximal_map_bijective {G J : Type*} [Group G] [Group J]
    (U Q T : Subgroup G) (b : ℕ) (i : G →* J) (hi : Function.Injective i) :
    Function.Bijective (fun E : Subgroup.SmallMover.Maximal U Q T b =>
      (⟨E.val.map i,(Subgroup.SmallMover.maximal_map_iff i hi U Q T E.val b).mpr E.property⟩ :
        Subgroup.SmallMover.Maximal (U.map i) (Q.map i) (T.map i) b)) := by
  constructor
  · intro E A he
    exact Subtype.ext (map_injective hi (congrArg Subtype.val he))
  · intro A
    have hAi : A.val ≤ i.range := A.property.1.1.trans (map_le_range i T)
    have hm : (A.val.comap i).map i = A.val := map_comap_eq_self hAi
    have hA : A.val.comap i ∈ Subgroup.SmallMover.Maximal U Q T b :=
      (Subgroup.SmallMover.maximal_map_iff i hi U Q T _ b).mp (hm.symm ▸ A.property)
    exact ⟨⟨A.val.comap i,hA⟩,Subtype.ext hm⟩

/-- The maximum family in the literal replacement edge is either unique,
or has q+1 members and generates that full edge, with relative order q³. -/
theorem Input.replacement_small_mover_dichotomy
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    (∃ E, Subgroup.SmallMover.Maximal (U d.radical a) (Q d.radical a) (Q d.radical t)
        (Nat.card F ^ 2) = {E} ∧
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2) = E) ∨
    (Nat.card (Subgroup.SmallMover.Maximal (U d.radical a) (Q d.radical a) (Q d.radical t)
        (Nat.card F ^ 2)) = Nat.card F + 1 ∧
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2) = Q d.radical t ∧
      (Q d.radical a).relIndex (Q d.radical t) = Nat.card F ^ 3) := by
  obtain ⟨E,hE,f,hf,hfQ,hTf,hidx⟩ := h.replacement_small_mover_coordinates d geometry hb ha hat
  have hcard : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  let S := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S
  let T := (Q d.radical t).subgroupOf S
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
  have hKmap : f.ker.map S.subtype = Q d.radical a := hfQ
  have hUT : U₀.map S.subtype = U d.radical a := map_subgroupOf_eq_of_le hUS
  have hTT : T.map S.subtype = Q d.radical t := map_subgroupOf_eq_of_le hTS
  have hfamily := maximal_map_bijective U₀ f.ker T (Nat.card F ^ 2) S.subtype S.subtype_injective
  have hfamilycard := Nat.card_congr (Equiv.ofBijective _ hfamily)
  rw [hUT,hKmap,hTT] at hfamilycard
  have hjoin := Subgroup.SmallMover.join_map S.subtype S.subtype_injective U₀ f.ker T (Nat.card E.Carrier ^ 2)
  rw [hUT,hKmap,hTT,hcard] at hjoin
  have hmodel := Degree.Quotient.maximal_singleton_or_point_radical U₀ T f
    (unipotent (F := E.Carrier)).subtype Subtype.val_injective hkT hUK
    (by simpa only [range_subtype] using hTf) hidx
  rw [hcard] at hmodel
  rcases hmodel with ⟨A,hA,hJA⟩ | ⟨hpoint,hcount,hJT,horder⟩
  · have hsingle : Subgroup.SmallMover.Maximal (U d.radical a) (Q d.radical a) (Q d.radical t)
        (Nat.card F ^ 2) = {A.map S.subtype} := by
      ext C
      constructor
      · intro hC
        have hC' : C ∈ Subgroup.SmallMover.Maximal (U₀.map S.subtype) (f.ker.map S.subtype)
            (T.map S.subtype) (Nat.card F ^ 2) := by simpa only [hUT,hKmap,hTT] using hC
        obtain ⟨D,hD⟩ := hfamily.surjective ⟨C,hC'⟩
        have he : D.val = A := Set.mem_singleton_iff.mp (hA ▸ D.property)
        exact Set.mem_singleton_iff.mpr ((congrArg Subtype.val hD).symm.trans (congrArg (Subgroup.map S.subtype) he))
      · rintro rfl
        simpa only [hUT,hKmap,hTT] using (Subgroup.SmallMover.maximal_map_iff S.subtype S.subtype_injective
          U₀ f.ker T A (Nat.card F ^ 2)).mpr (hA ▸ Set.mem_singleton A)
    exact Or.inl ⟨A.map S.subtype,hsingle,by simp only [Subgroup.SmallMover.join,hsingle,sSup_singleton]⟩
  · right
    refine ⟨hfamilycard.symm.trans hcount,?_,?_⟩
    · rw [hJT] at hjoin
      exact hjoin.symm.trans hTT
    · have hi := relIndex_map_map_of_injective f.ker T S.subtype_injective
      rw [hfQ,hTT] at hi
      exact hi.trans horder

/-- With two distinct maximum movers, the original edge image is the
literal point radical under the same whole-vertex symplectic marking. -/
theorem Input.replacement_multiple_movers_point_image
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    {A B : Subgroup (FreeAmalgam d.radical)}
    (hA : A ∈ Subgroup.SmallMover.Maximal (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2))
    (hB : B ∈ Subgroup.SmallMover.Maximal (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2))
    (hne : A ≠ B) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp E.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f =
          (CentralRootGeometry.wing (F := E.Carrier) false).map unipotent.subtype := by
  obtain ⟨E,hE,f,hf,hfQ,hTf,hidx⟩ := h.replacement_small_mover_coordinates d geometry hb ha hat
  have hcard : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  let S := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S
  let T := (Q d.radical t).subgroupOf S
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
  have hKmap : f.ker.map S.subtype = Q d.radical a := hfQ
  have hUT : U₀.map S.subtype = U d.radical a := map_subgroupOf_eq_of_le hUS
  have hTT : T.map S.subtype = Q d.radical t := map_subgroupOf_eq_of_le hTS
  have hTi : T.map f ≤ (unipotent (F := E.Carrier)).subtype.range := by
    simpa only [range_subtype] using hTf
  have hpre (C : Subgroup (FreeAmalgam d.radical))
      (hC : C ∈ Subgroup.SmallMover.Maximal (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2)) :
      C.subgroupOf S ∈ Subgroup.SmallMover.Maximal U₀ f.ker T (Nat.card E.Carrier ^ 2) := by
    apply (Subgroup.SmallMover.maximal_map_iff S.subtype S.subtype_injective U₀ f.ker T _ _).mp
    simpa only [hUT,hKmap,hTT,map_subgroupOf_eq_of_le (hC.1.1.trans hTS),hcard] using hC
  have hAc := Degree.Quotient.maximal_coordinates U₀ T f unipotent.subtype
    Subtype.val_injective hkT hUK hTi hidx (hpre A hA)
  have hBc := Degree.Quotient.maximal_coordinates U₀ T f unipotent.subtype
    Subtype.val_injective hkT hUK hTi hidx (hpre B hB)
  have hbij := Degree.Quotient.maximal_coordinates_bijective U₀ T f unipotent.subtype
    Subtype.val_injective hkT hUK hTi hidx
  have hne' : Degree.Quotient.coordinates f unipotent.subtype (A.subgroupOf S) ≠
      Degree.Quotient.coordinates f unipotent.subtype (B.subgroupOf S) := by
    intro he
    have hh : (⟨A.subgroupOf S,hpre A hA⟩ : Subgroup.SmallMover.Maximal U₀ f.ker T (Nat.card E.Carrier ^ 2)) =
        ⟨B.subgroupOf S,hpre B hB⟩ := hbij.injective (Subtype.ext he)
    have hm := congrArg (fun C => C.val.map S.subtype) hh
    rw [map_subgroupOf_eq_of_le (hA.1.1.trans hTS),map_subgroupOf_eq_of_le (hB.1.1.trans hTS)] at hm
    exact hne hm
  have hpoint := Degree.two_maximal_force_point_wing hAc hBc hne'
  refine ⟨E,hE,f,hf,hfQ,?_⟩
  rw [←Degree.Quotient.coordinates_map f unipotent.subtype T hTi,hpoint]

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
