module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.MaximizingParabolic
public import Theory.SpecificGroups.SymplecticFour.QuadraticParabolicPlacement

/-!
# Separating the neighboring small movers

The common vertex stabilizer conjugates any two neighboring small-mover
joins, so they have the same order. The small-index absorption theorem
then shows that distinct joins jointly move more than q² cosets of the
whole U-layer. If the join itself has small fixed index, its quadratic
plane can be moved to the standard plane; maximality forces containment
in the originally chosen parabolic radical.

These arguments prove the opening separation assertion of MS93 (5.5),
printed p.916, for both literal source alternatives. The same maximizing
parabolic retains its actual two-core, whole-layer quadratic action and
all fixed indices. Subsequent selected-path generation is not asserted.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit

section Transport
variable {M : Type*} [Group M] [Finite M] (R : Subgroup M)

/-- Neighboring small-mover joins have exactly the same order, through the
literal inverse-conjugation action of the common vertex stabilizer. -/
theorem small_mover_neighbor_card_eq {a t c : Vertex R}
    (hat : Adjacent R a t) (hct : Adjacent R c t) (bound : ℕ) :
    Nat.card (Subgroup.SmallMover.join (U R a) (Q R a) (Q R t) bound) =
      Nat.card (Subgroup.SmallMover.join (U R c) (Q R c) (Q R t) bound) := by
  obtain ⟨g,hg,hga⟩ := stabilizer_transitive_neighbors R t (adjacent_symm R hat) (adjacent_symm R hct)
  have hgt : act R g t = t := hg
  have htransport : Subgroup.SmallMover.join (U R c) (Q R c) (Q R t) bound =
      (Subgroup.SmallMover.join (U R a) (Q R a) (Q R t) bound).map
        (MulAut.conj g⁻¹).toMonoidHom := by
    conv_lhs => rw [←hga,←hgt]
    rw [U_act,Q_act,Q_act,←Subgroup.SmallMover.join_map _ (MulAut.conj g⁻¹).injective]
  rw [htransport,card_map_of_injective (MulAut.conj g⁻¹).injective]
end Transport

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A small fixed index forces the entire small-mover join into the
chosen maximizing plane radical. The original full kernel is retained. -/
theorem Input.replacement_small_mover_le_maximizing_plane_of_index_le
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hTf : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hmax : let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
      let J := (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)
      ∀ x : Sp B.Carrier,
        Nat.card (J ⊓ (P.map (MulAut.conj x).toMonoidHom).comap f :
          Subgroup (stabilizer d.radical a)) ≤ Nat.card (J ⊓ P.comap f :
            Subgroup (stabilizer d.radical a)))
    (hi : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f := by
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let J₀ := J.subgroupOf S
  let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
  let := finite_stabilizer d.radical a
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hJS : J ≤ S := by
    apply (Subgroup.SmallMover.join_le _ _ _ _).trans
    change Q d.radical t ≤ stabilizer d.radical a
    rw [←hjr,←hjR]
    exact map_le_range j _
  have hJU : J₀.map f ≤ unipotent :=
    (map_mono (comap_mono (Subgroup.SmallMover.join_le _ _ _ _))).trans hTf
  let A := (J₀.map f).subgroupOf unipotent
  have hAm : A.map unipotent.subtype = J₀.map f := map_subgroupOf_eq_of_le hJU
  have hcard : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  have hc : Nat.card B.Carrier^2 ≤ Nat.card A := by
    rw [←card_map_of_injective unipotent.subtype_injective,hAm,←relIndex_ker]
    have hh := relIndex_map_map_of_injective f.ker J₀ S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hJS] at hh
    rw [←hh,hcard]
    exact h.replacement_small_mover_join_index d geometry hb ha hat
  have hm : CentralRootGeometry.SmallMovers.movingIndex A ≤ Nat.card B.Carrier^2 := by
    have hh := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
      ((U d.radical a).subgroupOf S) J₀
    rw [map_subgroupOf_eq_of_le ((U_le_Z a).trans (Z_le_stabilizer d.radical a)),
      map_subgroupOf_eq_of_le hJS,hindex] at hh
    rw [←CentralRootGeometry.SmallMovers.binary_movingIndex]
    change 2 ^ fixedCodim ((restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)).comp unipotent.subtype) A ≤ _
    rw [fixedCodim,fixedSpace_comp_map,hAm]
    change 2 ^ fixedCodim (restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)) (J₀.map f) ≤ _
    rw [←hh,hcard]
    exact hi
  obtain ⟨g,hg⟩ := large_small_conjugate_le_plane A hm hc
  rw [hAm] at hg
  have hback : J₀.map f ≤ P.map (MulAut.conj g⁻¹).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hg
    rw [Subgroup.map_map] at hh
    have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id (Sp B.Carrier) := by
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    rwa [he,Subgroup.map_id] at hh
  have hle := (map_le_iff_le_comap).mp hback
  have hbound := hmax g⁻¹
  change Nat.card (J₀ ⊓ (P.map (MulAut.conj g⁻¹).toMonoidHom).comap f : Subgroup S) ≤
    Nat.card (J₀ ⊓ P.comap f : Subgroup S) at hbound
  rw [inf_eq_left.mpr hle] at hbound
  have he : J₀ ⊓ P.comap f = J₀ := eq_of_le_of_card_ge inf_le_left hbound
  exact (inf_eq_left.mp he)

/-- Unequal neighboring joins cannot jointly have a small fixed index
on the full original U-layer. -/
theorem Input.replacement_unequal_mover_fixed_index
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t c : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2)) :
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    let Jc := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2)
    Nat.card F^2 < (centralizer ((J ⊔ Jc : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) := by
  dsimp only
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let Jc := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)
  by_contra hn
  have hi : (centralizer ((J ⊔ Jc : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ Nat.card F^2 := le_of_not_gt hn
  have he : J ⊔ Jc = J := h.replacement_small_mover_absorbs d geometry hb ha hat
    (J ⊔ Jc) (sup_le (Subgroup.SmallMover.join_le _ _ _ _) (Subgroup.SmallMover.join_le _ _ _ _))
    le_sup_left hi
  have hle : Jc ≤ J := (le_sup_right : Jc ≤ J ⊔ Jc).trans_eq he
  let := finite_stabilizer d.radical t
  let : Finite J := Finite.of_injective
    (inclusion ((Subgroup.SmallMover.join_le _ _ _ _).trans
      (show Q d.radical t ≤ stabilizer d.radical t from fun _ hx => hx.1)))
    (inclusion_injective _)
  exact hne (eq_of_le_of_card_ge hle (small_mover_neighbor_card_eq d.radical hat hct _).le)


/-- The maximizing choice in MS93 (5.0) also satisfies the opening
separation assertion of (5.5), at every neighboring source vertex.
Both source alternatives give fixed index above q squared and a
nonquadratic actor in the same original-degree natural marking. -/
theorem Input.replacement_maximizing_parabolic_separation
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ∃ B : BinaryField, B.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
        (let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
         let Q₁ := P.comap f
         let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
           (Q d.radical t) (Nat.card F^2)
         (planeParabolic.comap f).pCoreIn 2 = Q₁ ∧
         (Q d.radical t).subgroupOf (stabilizer d.radical a) ≤ planeParabolic.comap f ∧
         ⁅⁅(U d.radical a).subgroupOf (stabilizer d.radical a),Q₁⁆,Q₁⁆ = ⊥ ∧
         (∀ x : Sp B.Carrier,
           Nat.card (J.subgroupOf (stabilizer d.radical a) ⊓
             (P.map (MulAut.conj x).toMonoidHom).comap f :
               Subgroup (stabilizer d.radical a)) ≤ Nat.card
                 (J.subgroupOf (stabilizer d.radical a) ⊓ Q₁ :
                   Subgroup (stabilizer d.radical a))) ∧
         ∀ c : Vertex d.radical, Adjacent d.radical c t →
           let Jc := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
             (Q d.radical t) (Nat.card F^2)
           (Jc ≠ J ∨ ¬ J.subgroupOf (stabilizer d.radical a) ≤ Q₁) →
           Nat.card F^2 < (centralizer ((J ⊔ Jc : Subgroup (FreeAmalgam d.radical)) :
             Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ∧
           ¬ IsQuadratic (restrictScalars (k := ZMod 2)
             (symplecticNatural (k := B.Carrier) 2))
             (((J ⊔ Jc).subgroupOf (stabilizer d.radical a)).map f)) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax⟩ :=
    h.replacement_maximizing_parabolic d geometry hb ha hat
  refine ⟨B,hB,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax,?_⟩
  intro c hct
  dsimp only
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let Jc := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)
  intro hcases
  have hbig : Nat.card F^2 < (centralizer ((J ⊔ Jc : Subgroup (FreeAmalgam d.radical)) :
      Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    rcases hcases with hne | hout
    · exact h.replacement_unequal_mover_fixed_index d geometry hb ha hat hct hne
    · by_contra hn
      have hi : (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤
          Nat.card F^2 := by
        let := finite_Z d.radical a
        let : Finite (U d.radical a) := Finite.of_injective (inclusion (U_le_Z a))
          (inclusion_injective _)
        exact (relIndex_le_of_le_left (centralizer_le
          (show J ≤ J ⊔ Jc from le_sup_left)) index_ne_zero_of_finite).trans (le_of_not_gt hn)
      exact hout (h.replacement_small_mover_le_maximizing_plane_of_index_le d
        geometry hb ha hat B hB f hfQ hTf hindex hmax hi)
  refine ⟨hbig,?_⟩
  intro hq
  have hbound := quadratic_natural_fixed_index_le_square
    (((J ⊔ Jc).subgroupOf (stabilizer d.radical a)).map f) hq
  have hAS : J ⊔ Jc ≤ stabilizer d.radical a := by
    have hT : Q d.radical t ≤ stabilizer d.radical a :=
      fun _ hx => hx.2 a (adjacent_symm d.radical hat)
    exact (sup_le (Subgroup.SmallMover.join_le _ _ _ _) (Subgroup.SmallMover.join_le _ _ _ _)).trans hT
  have hi := Subgroup.SmallMover.centralizer_index_map (stabilizer d.radical a).subtype
    (stabilizer d.radical a).subtype_injective
    ((U d.radical a).subgroupOf (stabilizer d.radical a))
    ((J ⊔ Jc).subgroupOf (stabilizer d.radical a))
  rw [map_subgroupOf_eq_of_le ((U_le_Z a).trans (Z_le_stabilizer d.radical a)),
    map_subgroupOf_eq_of_le hAS,hindex] at hi
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hbound
  change 2 ^ fixedCodim (restrictScalars (k := ZMod 2)
    (symplecticNatural (k := B.Carrier) 2))
      (((J ⊔ Jc).subgroupOf (stabilizer d.radical a)).map f) ≤ Nat.card B.Carrier^2 at hbound
  rw [←hi,B.card_eq,hB,←h.field_card] at hbound
  exact hbig.not_ge hbound

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
