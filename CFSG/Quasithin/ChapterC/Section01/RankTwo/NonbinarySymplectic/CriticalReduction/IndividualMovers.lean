module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.CrossSelection
public import Theory.GroupTheory.SmallMoverEqualOrder
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.LargeMovement

/-!
# Individual unequal movers on the original natural layer

The two neighboring movers have the same order. The original mover contains
the full Q-kernel and has at least q squared images. Consequently the other
mover also has at least that many images, without assuming that it contains
Q. If its fixed index were small, maximum order would make it equal to the
original mover. Thus each unequal mover individually has large movement.

In one marking of the original vertex quotient, every such mover therefore
has fixed space exactly the standard point and fixed index q cubed on the
whole U-layer. It is nonquadratic and is normalized by the actual edge image.
The full-Sylow normalization asserted here belongs to the edge, not to the
individual neighboring mover. Equality of these indices also proves that the individual mover and the
edge fix exactly the same subgroup of the whole U-layer. No central
attachment is removed.

This strengthens the cross-join separation used in MS93 (5.5), printed
pp.915--917. Individual residual generation, smaller-J contained large-image
selection, the trapped-root and terminal exclusions, and the distance-two
replacement witness remain to be proved.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Equal orders and the large maximum-small-mover bound force every
individual unequal neighboring mover above the small fixed-index bound.
The quotient-image lower bound does not require kernel containment in it. -/
theorem Input.replacement_unequal_individual_indices
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t c : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2)) :
    Nat.card F^2 ≤ (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical c)
      (Q d.radical c) (Q d.radical t) (Nat.card F^2)) ∧
    Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical c)
      (Q d.radical c) (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) := by
  let S := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S
  let Q₀ := (Q d.radical a).subgroupOf S
  let T := (Q d.radical t).subgroupOf S
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let E := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)
  let J₀ := J.subgroupOf S
  let E₀ := E.subgroupOf S
  let := finite_stabilizer d.radical a
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hQS : Q d.radical a ≤ S := fun _ hx => hx.1
  have hTS : Q d.radical t ≤ S := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hJT : J ≤ Q d.radical t := Subgroup.SmallMover.join_le _ _ _ _
  have hET : E ≤ Q d.radical t := Subgroup.SmallMover.join_le _ _ _ _
  have hJS : J ≤ S := hJT.trans hTS
  have hES : E ≤ S := hET.trans hTS
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hQJ : Q d.radical a ≤ J := by
    have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
      (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
      (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
      (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
        (h.replacement_two_group d) (h.replacement_core_le d)))
    rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh
  have hjoin : Subgroup.SmallMover.join U₀ Q₀ T (Nat.card F^2) = J₀ := by
    apply map_injective S.subtype_injective
    rw [Subgroup.SmallMover.join_map S.subtype S.subtype_injective,
      map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hQS,
      map_subgroupOf_eq_of_le hTS,map_subgroupOf_eq_of_le hJS]
  have hcard : Nat.card J₀ = Nat.card E₀ := by
    rw [←card_map_of_injective S.subtype_injective (K := J₀),
      ←card_map_of_injective S.subtype_injective (K := E₀),
      map_subgroupOf_eq_of_le hJS,map_subgroupOf_eq_of_le hES]
    exact small_mover_neighbor_card_eq d.radical hat hct _
  have hlarge : Nat.card F^2 ≤ Q₀.relIndex J₀ := by
    have hh := relIndex_map_map_of_injective Q₀ J₀ S.subtype_injective
    rw [map_subgroupOf_eq_of_le hQS,map_subgroupOf_eq_of_le hJS] at hh
    rw [←hh]
    exact h.replacement_small_mover_join_index d geometry hb ha hat
  have hElarge : Nat.card F^2 ≤ Q₀.relIndex E₀ :=
    hlarge.trans (Subgroup.SmallMover.relIndex_le_of_card_eq_of_le Q₀ J₀ E₀
      (comap_mono hQJ) hcard)
  refine ⟨?_,?_⟩
  · have hh := relIndex_map_map_of_injective Q₀ E₀ S.subtype_injective
    rw [map_subgroupOf_eq_of_le hQS,map_subgroupOf_eq_of_le hES] at hh
    rw [hh]
    exact hElarge
  by_contra hn
  have hi : (centralizer (E₀ : Set S)).relIndex U₀ ≤ Nat.card F^2 := by
    have hh := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective U₀ E₀
    rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hES] at hh
    rw [←hh]
    exact le_of_not_gt hn
  have he := Subgroup.SmallMover.eq_join_of_card_eq_of_index_le U₀ Q₀ T (Nat.card F^2)
    (Nat.one_le_pow _ _ Nat.card_pos) (hjoin.symm ▸ comap_mono hQJ)
    (hjoin.symm ▸ hlarge) E₀ (comap_mono hET) (hjoin.symm ▸ hcard) hi
  rw [hjoin] at he
  have hh := congrArg (Subgroup.map S.subtype) he
  rw [map_subgroupOf_eq_of_le hES,map_subgroupOf_eq_of_le hJS] at hh
  exact hne hh

/-- One original-degree marking simultaneously identifies every individual
unequal neighboring mover. Its full-layer fixed index is exactly q cubed;
its image fixes precisely the standard point and is nonquadratic. Only the
actual edge image, rather than the full Sylow, is asserted to normalize it. -/
theorem Input.replacement_unequal_individual_coordinates
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ∃ B : BinaryField, B.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        unipotent ≤ normalizer
          (((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f : Set (Sp B.Carrier)) ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
        ∀ c : Vertex d.radical, Adjacent d.radical c t →
          let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
            (Q d.radical t) (Nat.card F^2)
          let E := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
            (Q d.radical t) (Nat.card F^2)
          let E₀ := (E.subgroupOf (stabilizer d.radical a)).map f
          E ≠ J →
            Nat.card B.Carrier^2 ≤ Nat.card E₀ ∧
            E₀ ≤ unipotent ∧
            ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤
              normalizer (E₀ : Set (Sp B.Carrier)) ∧
            (centralizer (E : Set (FreeAmalgam d.radical))).relIndex
              (U d.radical a) = Nat.card F^3 ∧
            fixed (E₀.subgroupOf unipotent) = point B.Carrier ∧
            ¬ IsQuadratic (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) E₀ := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex⟩ :=
    h.replacement_normalized_natural_indices d geometry hb ha hat
  refine ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,?_⟩
  intro c hct
  dsimp only
  let S := stabilizer d.radical a
  let E := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)
  let E₀ := E.subgroupOf S
  let E₁ := (E₀.map f).subgroupOf unipotent
  intro hne
  obtain ⟨hc,hi⟩ := h.replacement_unequal_individual_indices d geometry hb ha hat hct hne
  have hET : E ≤ Q d.radical t := Subgroup.SmallMover.join_le _ _ _ _
  have hTS : Q d.radical t ≤ S := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hES : E ≤ S := hET.trans hTS
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hEf : E₀.map f ≤ unipotent := (map_mono (comap_mono hET)).trans hTf
  have hE₁ : E₁.map unipotent.subtype = E₀.map f := map_subgroupOf_eq_of_le hEf
  have hBF : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  have hcE : Nat.card B.Carrier^2 ≤ Nat.card (E₀.map f) := by
    rw [←relIndex_ker]
    have hh := relIndex_map_map_of_injective f.ker E₀ S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hES] at hh
    rw [←hh,hBF]
    exact hc
  have hmove : movingIndex E₁ =
      (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    rw [←binary_movingIndex]
    change 2 ^ fixedCodim ((restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)).comp unipotent.subtype) E₁ = _
    rw [fixedCodim,fixedSpace_comp_map,hE₁]
    have hh := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
      ((U d.radical a).subgroupOf S) E₀
    rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hES,hindex] at hh
    exact hh.symm
  have hbig : Nat.card B.Carrier^2 < movingIndex E₁ := by rwa [hmove,hBF]
  obtain ⟨hfixed,hcube⟩ := fixed_eq_point_and_movingIndex_of_square_lt E₁ hbig
  refine ⟨hcE,hEf,?_,?_,hfixed,?_⟩
  · have hTc : Q d.radical t ≤ stabilizer d.radical c :=
      fun _ hx => hx.2 c (adjacent_symm d.radical hct)
    have hTE : Q d.radical t ≤ normalizer (E : Set (FreeAmalgam d.radical)) :=
      (le_inf (le_inf (hTc.trans (U_normalized c))
        (hTc.trans (Q_normalized d.radical c))) (Q d.radical t).le_normalizer).trans
        (Subgroup.SmallMover.normalizer_join _ _ _ _)
    have hn : (Q d.radical t).subgroupOf S ≤ normalizer (E₀ : Set S) :=
      (comap_mono hTE).trans (E.le_normalizer_comap S.subtype)
    exact (map_mono hn).trans (E₀.le_normalizer_map f)
  · rw [←hmove,hcube,hBF]
  · intro hquad
    have hbound := quadratic_natural_fixed_index_le_square (E₀.map f) hquad
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hbound
    have hh := hindex E₀
    have he := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
      ((U d.radical a).subgroupOf S) E₀
    rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hES,hh] at he
    change 2 ^ fixedCodim (restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)) (E₀.map f) ≤ Nat.card B.Carrier^2 at hbound
    rw [←he,hBF] at hbound
    exact hi.not_ge hbound


/-- Every unequal neighboring mover fixes exactly the same subgroup of the
entire original U-layer as the replacement edge. The quotient fixed point
is lifted by equality of the exact full-layer indices, keeping the covering
kernel and all central attachments. -/
theorem Input.replacement_unequal_individual_edge_fixed
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t c : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2)) :
    let E := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2)
    (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = Nat.card F^3 ∧
      U d.radical a ⊓ centralizer (E : Set (FreeAmalgam d.radical)) =
        U d.radical a ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
  dsimp only
  let S := stabilizer d.radical a
  let E := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)
  obtain ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,hall⟩ :=
    h.replacement_unequal_individual_coordinates d geometry hb ha hat
  obtain ⟨_,hEf,_,hcube,hfixed,_⟩ := hall c hct hne
  refine ⟨hcube,?_⟩
  let T₀ := (Q d.radical t).subgroupOf S
  let E₀ := E.subgroupOf S
  let T₁ := (T₀.map f).subgroupOf unipotent
  let E₁ := (E₀.map f).subgroupOf unipotent
  have hET : E ≤ Q d.radical t := Subgroup.SmallMover.join_le _ _ _ _
  have hTS : Q d.radical t ≤ S := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hET₁ : E₁ ≤ T₁ := comap_mono (map_mono (comap_mono hET))
  have hfixedT : fixed T₁ = fixed E₁ := by
    apply le_antisymm
    · intro v hv
      apply (mem_fixed_iff E₁ v).mpr
      intro b u w z he
      exact (mem_fixed_iff T₁ v).mp hv b u w z (hET₁ he)
    · rw [hfixed]
      exact standardPoint_le_fixed T₁
  have index (D : Subgroup (FreeAmalgam d.radical)) (hDT : D ≤ Q d.radical t) :
      movingIndex (((D.subgroupOf S).map f).subgroupOf unipotent) =
        (centralizer (D : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    rw [←binary_movingIndex]
    change 2 ^ fixedCodim ((restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)).comp unipotent.subtype)
        (((D.subgroupOf S).map f).subgroupOf unipotent) = _
    have hm : (((D.subgroupOf S).map f).subgroupOf unipotent).map unipotent.subtype =
        (D.subgroupOf S).map f :=
      map_subgroupOf_eq_of_le ((map_mono (comap_mono hDT)).trans hTf)
    rw [fixedCodim,fixedSpace_comp_map,hm]
    have he := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
      ((U d.radical a).subgroupOf S) (D.subgroupOf S)
    rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le (hDT.trans hTS),hindex] at he
    exact he.symm
  have hi : (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) =
      (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    rw [←index _ le_rfl,←index _ hET]
    change movingIndex T₁ = movingIndex E₁
    rw [movingIndex,movingIndex,hfixedT]
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  let CT := (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).subgroupOf (U d.radical a)
  let CE := (centralizer (E : Set (FreeAmalgam d.radical))).subgroupOf (U d.radical a)
  have he : CT = CE := by
    apply eq_of_le_of_card_ge (comap_mono (centralizer_le hET))
    have hCT := CT.card_mul_index
    have hCE := CE.card_mul_index
    change CT.index = CE.index at hi
    rw [hi] at hCT
    exact (Nat.eq_of_mul_eq_mul_right (index_ne_zero_of_finite (H := CE)).bot_lt
      (hCE.trans hCT.symm)).le
  apply le_antisymm
  · intro u hu
    refine ⟨hu.1,?_⟩
    exact (show (⟨u,hu.1⟩ : U d.radical a) ∈ CT from he.symm ▸ hu.2)
  · exact inf_le_inf_left _ (centralizer_le hET)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
