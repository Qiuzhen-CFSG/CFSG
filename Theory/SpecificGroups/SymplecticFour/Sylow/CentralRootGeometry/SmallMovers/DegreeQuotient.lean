module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.Degree
public import Theory.GroupTheory.SmallMoverFamily

/-!
# Transport of arbitrary-degree small movers through a full kernel

The exact centralizer index identifies small movers with the coordinate
family in a containing symplectic Sylow subgroup. Maximum order saturates
the whole quotient kernel. The resulting bijection preserves the entire
family and its join, so the point-radical branch lifts to the original
edge group. The edge group itself need not be Sylow.

Source: MS93 (5.4), printed p.915. The replacement consumer constructs the
quotient marking, the containing Sylow, and the centralizer-index equality.
-/

@[expose] public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree.Quotient
variable {F G D : Type*} [Field F] [CharP F 2] [Finite F]
  [Group G] [Finite G] [Group D]
variable (U T : Subgroup G) (q : G →* D) (i : unipotent (F := F) →* D)
  (hi : Function.Injective i)

noncomputable def coordinates (E : Subgroup G) : Subgroup (unipotent (F := F)) :=
  (E.map q).comap i

omit [CharP F 2] [Finite F] [Finite G] in
theorem coordinates_map (E : Subgroup G) (hE : E.map q ≤ i.range) :
    (coordinates q i E).map i = E.map q := map_comap_eq_self hE

variable (hkT : q.ker ≤ T) (hUT : U ≤ centralizer (q.ker : Set G))
  (hTi : T.map q ≤ i.range)
  (hindex : ∀ E : Subgroup G, E ≤ T →
    (centralizer (E : Set G)).relIndex U = movingIndex (coordinates q i E))

omit [CharP F 2] [Finite F] in
include hi hkT hUT hTi hindex in
theorem maximal_coordinates {E : Subgroup G}
    (hE : E ∈ Subgroup.SmallMover.Maximal U q.ker T (Nat.card F ^ 2)) :
    coordinates q i E ∈ Degree.Maximal (coordinates q i T) := by
  have he := (Subgroup.SmallMover.maximal_iff_image_maximal q U T _ hkT hUT E).mp hE
  have hEi := (map_mono hE.1.1).trans hTi
  have hcE : Nat.card (E.map q) = Nat.card (coordinates q i E) := by
    rw [←coordinates_map q i E hEi,card_map_of_injective hi]
  refine ⟨comap_mono (map_mono hE.1.1),?_,?_⟩
  · constructor
    · rw [←hindex E hE.1.1,←hcE,←relIndex_ker]
      exact hE.1.2.1
    · rw [←hindex E hE.1.1]
      exact hE.1.2.2
  · intro A hA hs
    have hm : A.map i ≤ T.map q := (map_mono hA).trans_eq (coordinates_map q i T hTi)
    let E' := (A.map i).comap q
    have hET : E' ≤ T := (comap_mono hm).trans_eq (comap_map_eq_self hkT)
    have hEm : E'.map q = A.map i := map_comap_eq_self (hm.trans (map_le_range q T))
    have hEc : coordinates q i E' = A := by
      change (E'.map q).comap i = A
      rw [hEm,comap_map_eq_self (by rw [i.ker_eq_bot hi]; exact bot_le)]
    have hc : Nat.card (E'.map q) = Nat.card A := by rw [hEm,card_map_of_injective hi]
    have ha : Subgroup.SmallMover.Admissible U q.ker T (Nat.card F ^ 2) E' := by
      refine ⟨hET,?_,?_⟩
      · rw [hindex E' hET,hEc,relIndex_ker,hc]
        exact hs.1
      · rw [hindex E' hET,hEc]
        exact hs.2
    have hh := he.2.2 E' ha
    rwa [hc,hcE] at hh

omit [CharP F 2] [Finite F] in
include hi hkT hUT hTi hindex in
theorem maximal_of_coordinates {E : Subgroup G} (hEk : q.ker ≤ E) (hET : E ≤ T)
    (hE : coordinates q i E ∈ Degree.Maximal (coordinates q i T)) :
    E ∈ Subgroup.SmallMover.Maximal U q.ker T (Nat.card F ^ 2) := by
  have hc (A : Subgroup G) (hA : A ≤ T) : Nat.card (A.map q) = Nat.card (coordinates q i A) := by
    rw [←coordinates_map q i A ((map_mono hA).trans hTi),card_map_of_injective hi]
  apply (Subgroup.SmallMover.maximal_iff_image_maximal q U T _ hkT hUT E).mpr
  refine ⟨⟨hET,?_,?_⟩,hEk,?_⟩
  · rw [hindex E hET,relIndex_ker,hc E hET]
    exact hE.2.1.1
  · rw [hindex E hET]
    exact hE.2.1.2
  · intro A hA
    rw [hc A hA.1,hc E hET]
    apply hE.2.2 _ (comap_mono (map_mono hA.1))
    change Degree.Small (coordinates q i A)
    constructor
    · rw [←hindex A hA.1,←hc A hA.1,←relIndex_ker]
      exact hA.2.1
    · rw [←hindex A hA.1]
      exact hA.2.2

omit [CharP F 2] [Finite F] in
include hi hkT hUT hTi hindex in
theorem maximal_coordinates_bijective :
    Function.Bijective (fun E : Subgroup.SmallMover.Maximal U q.ker T (Nat.card F ^ 2) =>
      (⟨coordinates q i E.val,maximal_coordinates U T q i hi hkT hUT hTi hindex E.property⟩ :
        Degree.Maximal (coordinates q i T))) := by
  constructor
  · intro E A he
    apply Subtype.ext
    have hEk := (Subgroup.SmallMover.maximal_iff_image_maximal q U T _ hkT hUT E.val).mp E.property |>.2.1
    have hAk := (Subgroup.SmallMover.maximal_iff_image_maximal q U T _ hkT hUT A.val).mp A.property |>.2.1
    have hm := congrArg (fun B => B.map i) (congrArg Subtype.val he)
    rw [coordinates_map q i E.val ((map_mono E.property.1.1).trans hTi),
      coordinates_map q i A.val ((map_mono A.property.1.1).trans hTi)] at hm
    have hc := congrArg (fun B => B.comap q) hm
    simpa only [comap_map_eq_self hEk,comap_map_eq_self hAk] using hc
  · intro A
    let E := (A.val.map i).comap q
    have hm : A.val.map i ≤ T.map q :=
      (map_mono A.property.1).trans_eq (coordinates_map q i T hTi)
    have hET : E ≤ T := (comap_mono hm).trans_eq (comap_map_eq_self hkT)
    have hEk : q.ker ≤ E := by
      intro x hx
      change q x ∈ A.val.map i
      rw [MonoidHom.mem_ker.mp hx]
      exact one_mem _
    have heq : coordinates q i E = A.val := by
      change (E.map q).comap i = A.val
      rw [map_comap_eq_self (hm.trans (map_le_range q T)),
        comap_map_eq_self (by rw [i.ker_eq_bot hi]; exact bot_le)]
    exact ⟨⟨E,maximal_of_coordinates U T q i hi hkT hUT hTi hindex hEk hET
      (heq.symm ▸ A.property)⟩,Subtype.ext heq⟩

omit [CharP F 2] [Finite F] in
include hi hkT hUT hTi hindex in
theorem coordinates_join :
    coordinates q i (Subgroup.SmallMover.join U q.ker T (Nat.card F ^ 2)) =
      Degree.join (coordinates q i T) := by
  let J := Subgroup.SmallMover.join U q.ker T (Nat.card F ^ 2)
  have hJi : J.map q ≤ i.range := (map_mono (Subgroup.SmallMover.join_le _ _ _ _)).trans hTi
  apply map_injective hi
  rw [coordinates_map q i J hJi]
  apply le_antisymm
  · change (sSup (Subgroup.SmallMover.Maximal U q.ker T (Nat.card F ^ 2))).map q ≤ _
    rw [sSup_eq_iSup,Subgroup.map_iSup]
    apply iSup_le
    intro E
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hE
    rw [←coordinates_map q i E ((map_mono hE.1.1).trans hTi)]
    exact map_mono (le_sSup (maximal_coordinates U T q i hi hkT hUT hTi hindex hE))
  · change (sSup (Degree.Maximal (coordinates q i T))).map i ≤ J.map q
    rw [sSup_eq_iSup,Subgroup.map_iSup]
    apply iSup_le
    intro B
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hB
    obtain ⟨C,hC⟩ := (maximal_coordinates_bijective U T q i hi hkT hUT hTi hindex).surjective ⟨B,hB⟩
    have heq : coordinates q i C.val = B := congrArg Subtype.val hC
    rw [←heq,coordinates_map q i C.val ((map_mono C.property.1.1).trans hTi)]
    exact map_mono (le_sSup C.property)

include hi hkT hUT hTi hindex in
/-- The entire maximum family is either a singleton or the lifted q+1 planes.
In the latter case its join is the original T, including the full kernel. -/
theorem maximal_singleton_or_point_radical :
    (∃ E, Subgroup.SmallMover.Maximal U q.ker T (Nat.card F ^ 2) = {E} ∧
      Subgroup.SmallMover.join U q.ker T (Nat.card F ^ 2) = E) ∨
    (coordinates q i T = wing false ∧
      Nat.card (Subgroup.SmallMover.Maximal U q.ker T (Nat.card F ^ 2)) = Nat.card F + 1 ∧
      Subgroup.SmallMover.join U q.ker T (Nat.card F ^ 2) = T ∧
      q.ker.relIndex T = Nat.card F ^ 3) := by
  have hbij := maximal_coordinates_bijective U T q i hi hkT hUT hTi hindex
  rcases Degree.maximal_singleton_or_point_wing (coordinates q i T) with ⟨A,hA,hjoin⟩ | ⟨hT,hfamily,hcard,hjoin⟩
  · obtain ⟨E,hE⟩ := hbij.surjective ⟨A,hA ▸ Set.mem_singleton A⟩
    have hsingle : Subgroup.SmallMover.Maximal U q.ker T (Nat.card F ^ 2) = {E.val} := by
      ext C
      constructor
      · intro hC
        have hc : coordinates q i C = A := Set.mem_singleton_iff.mp
          (hA ▸ maximal_coordinates U T q i hi hkT hUT hTi hindex hC)
        have hec : (⟨C,hC⟩ : Subgroup.SmallMover.Maximal U q.ker T (Nat.card F ^ 2)) = E :=
          hbij.injective (Subtype.ext (hc.trans (congrArg Subtype.val hE).symm))
        exact Set.mem_singleton_iff.mpr (congrArg Subtype.val hec)
      · rintro rfl
        exact E.property
    exact Or.inl ⟨E.val,hsingle,by simp only [Subgroup.SmallMover.join,hsingle,sSup_singleton]⟩
  · right
    refine ⟨hT,(Nat.card_congr (Equiv.ofBijective _ hbij)).trans hcard,?_,?_⟩
    · let J := Subgroup.SmallMover.join U q.ker T (Nat.card F ^ 2)
      have hJT : J ≤ T := Subgroup.SmallMover.join_le _ _ _ _
      have hkJ : q.ker ≤ J := Subgroup.SmallMover.kernel_le_join U q.ker T _
        (Nat.one_le_pow _ _ (Nat.card_pos (α := F))) hkT hUT
      have hc := coordinates_join U T q i hi hkT hUT hTi hindex
      rw [hjoin] at hc
      have hm := congrArg (fun A => A.map i) hc
      rw [coordinates_map q i J ((map_mono hJT).trans hTi),coordinates_map q i T hTi] at hm
      have he := congrArg (fun A => A.comap q) hm
      simpa only [comap_map_eq_self hkJ,comap_map_eq_self hkT] using he
    · rw [relIndex_ker,←coordinates_map q i T hTi,card_map_of_injective hi,hT,card_wing]

end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree.Quotient
