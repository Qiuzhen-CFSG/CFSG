module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsPairCoordinatesModel
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.FixedFreeFusion
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections

/-!
# The original Sylow fixes the returned HS pair product

The unchanged action-kernel marking maps a Sylow of C_L(u) onto a Sylow
of the actual nonsingular stabilizer in A8. The model fixed-space bound
therefore gives |C_V(T_u)| at most four. Two distinct nonsingular vectors
fixed by T_u fill that plane. A nonidentity vector in C_V(T) exists by the
two-group center theorem, and cannot be nonsingular. It must consequently
be the product of the original pair.

No nonsingular-centralizer containment or new module marking is assumed.
This is a coordinate consequence of the actual returned pair, leaving the
ambient HS exclusion to its consumer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The selected original point Sylow fixes at most a plane in the full V. -/
theorem OrthogonalMarking.nonsingular_selected_fixed_card_le_four
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (hZ : ZV L V = ⊥)
    (u : V) (hu : D.Nonsingular u)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T (u : G)) (Mv L (u : G))) :
    Nat.card (V ⊓ centralizer (Tv T (u : G) : Set G) : Subgroup G) ≤ 4 := by
  let C := CLv L (u : G)
  let v := (D.fullCoordinates hZ u).toAdd
  let B := EightNonsingular.stabilizer v
  have hCM : C ≤ Mv L (u : G) := inf_le_inf L.le_normalizer le_rfl
  have hn : Mv L (u : G) ≤ normalizer (C : Set G) :=
    le_trans (le_inf inf_le_left (inf_le_right.trans (Gv (u : G)).le_normalizer))
      inf_normalizer_le_normalizer_inf
  let : (C.subgroupOf (Mv L (u : G))).Normal := normal_subgroupOf_of_le_normalizer hn
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl hCM
    (inferInstance : (C.subgroupOf (Mv L (u : G))).Normal).isSubnormal
  let a : C →* alternatingGroup (Fin 8) :=
    D.actorMap.comp (inclusion (show C ≤ L from inf_le_left))
  have ha (c : C) : a c ∈ B := by
    have hm : (⟨c.val,c.property.1⟩ : L) ∈ C.subgroupOf L := c.property
    rw [D.centralizer_preimage chosen u hu] at hm
    change D.actorMap ⟨c.val,c.property.1⟩ ∈ EightNonsingular.stabilizer
      ((D.fullCoordinates hZ u).toAdd)
    rw [D.fullCoordinates_apply]
    exact hm
  let f : C →* B := a.codRestrict B ha
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨l,hl⟩ := D.actorMap_surjective b.val
    have hm : l ∈ C.subgroupOf L := by
      rw [D.centralizer_preimage chosen u hu]
      change D.actorMap l ∈ EightNonsingular.stabilizer _
      rw [hl]
      simpa only [B,v,D.fullCoordinates_apply] using b.property
    exact ⟨⟨l.val,hm⟩,Subtype.ext hl⟩
  let P' := P.mapSurjective (f := f) hf
  let F := V ⊓ centralizer (Tv T (u : G) : Set G)
  let E := D.fullCoordinates hZ
  let F' := fixedSpace (alternatingNaturalRepresentation (Fin 8))
    ((P' : Subgroup B).map B.subtype)
  have hfixed (y : F) : (E ⟨y.val,y.property.1⟩).toAdd ∈ F' := by
    rintro ⟨b,hb⟩
    obtain ⟨c,hc,rfl⟩ := hb
    change c ∈ (P : Subgroup C).map f at hc
    obtain ⟨l,hl,rfl⟩ := hc
    have hlT : (l : G) ∈ Tv T (u : G) := (hP ▸ mem_map_of_mem C.subtype hl).1
    have hy : conjugation L V chosen.normalizes ⟨l.val,l.property.1⟩
        ⟨y.val,y.property.1⟩ = ⟨y.val,y.property.1⟩ := by
      apply Subtype.ext
      change (l:G)*y.val*(l:G)⁻¹ = y.val
      rw [y.property.2 (l:G) hlT,mul_inv_cancel_right]
    exact (D.fullCoordinates_equivariant hZ ⟨l.val,l.property.1⟩
      ⟨y.val,y.property.1⟩).symm.trans (congrArg (fun x : V => (E x).toAdd) hy)
  let j : F → F' := fun y => ⟨(E ⟨y.val,y.property.1⟩).toAdd,hfixed y⟩
  have hj : Function.Injective j := by
    intro y z he
    apply Subtype.ext
    exact congrArg (fun v : V => (v:G)) (E.injective (congrArg Subtype.val he))
  exact (Nat.card_le_card_of_injective j hj).trans
    (OriginalHigmanSimsPairCoordinates.nonsingular_stabilizer_sylow_fixed_card_le_four v
      ((D.fullCoordinates_nonsingular_iff hZ u).mpr hu) P')

private theorem four_fixed_elements (F : Subgroup G) (hF : Nat.card F ≤ 4)
    (u w : F) (hu : u ≠ 1) (hw : w ≠ 1) (huw : u ≠ w)
    (hu2 : u ^ 2 = 1) : ∀ x : F, x = 1 ∨ x = u ∨ x = w ∨ x = u*w := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hi : u⁻¹ = u := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hu2)
  have hm1 : u*w ≠ 1 := by
    intro hh
    have hh' : w = u⁻¹ := eq_inv_of_mul_eq_one_right hh
    exact huw (hh'.trans hi).symm
  have hmu : u*w ≠ u := fun hh => hw (mul_left_cancel (hh.trans (mul_one u).symm))
  have hmw : u*w ≠ w := fun hh => hu (mul_right_cancel (hh.trans (one_mul w).symm))
  let s : Finset F := {1,u,w,u*w}
  have hs : s.card = 4 := by
    simp [s,huw,Ne.symm hu,Ne.symm hw,Ne.symm hm1,Ne.symm hmu,Ne.symm hmw]
  have he : s = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ s) (by
    rw [Finset.card_univ,hs]
    simpa only [Nat.card_eq_fintype_card] using hF)
  intro x
  have hx : x ∈ s := he ▸ Finset.mem_univ x
  simpa only [s,Finset.mem_insert,Finset.mem_singleton] using hx

/-- The product of two distinct original nonsingular vectors fixed by T_u
is fixed by the unchanged full Sylow T. -/
theorem SourceHypothesis.original_nonsingular_pair_product_sylow_fixed
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hZ : ZV L V = ⊥)
    (u w : V) (hu : D.Nonsingular u) (hw : D.Nonsingular w) (huw : u ≠ w)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T (u : G)) (Mv L (u : G)))
    (hfix : Tv T (u : G) ≤ Gv (w : G)) :
    (T : Subgroup G) ≤ Gv ((u : G)*(w : G)) := by
  let F := V ⊓ centralizer (Tv T (u : G) : Set G)
  have huF : (u:G) ∈ F := ⟨u.property,fun t ht =>
    mem_centralizer_singleton_iff.mp ht.2⟩
  have hwF : (w:G) ∈ F := ⟨w.property,fun t ht =>
    mem_centralizer_singleton_iff.mp (hfix ht)⟩
  have hfour := four_fixed_elements F
    (D.nonsingular_selected_fixed_card_le_four H.chosen hZ u hu hSyl)
    ⟨u,huF⟩ ⟨w,hwF⟩
    (fun he => nonsingular_ne_one D hu (Subtype.ext (congrArg (fun a : F => (a:G)) he)))
    (fun he => nonsingular_ne_one D hw (Subtype.ext (congrArg (fun a : F => (a:G)) he)))
    (fun he => huw (Subtype.ext (congrArg (fun a : F => (a:G)) he)))
    (Subtype.ext (congrArg (fun a : V => (a:G))
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V) u)))
  let A := V.subgroupOf (T : Subgroup G)
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer H.chosen.le_sylow).mpr hTV
  have hA : A ≠ ⊥ := by
    intro ha
    apply H.chosen.ne_bot
    rw [←map_subgroupOf_eq_of_le H.chosen.le_sylow]
    change A.map (T : Subgroup G).subtype = ⊥
    rw [ha,Subgroup.map_bot]
  have hn := center_inf_ne_bot_of_normal T.isPGroup' A hA
  obtain ⟨x,hx,hxne⟩ := (center (T : Subgroup G) ⊓ A).bot_or_exists_ne_one.resolve_left hn
  have hTx : (T : Subgroup G) ≤ Gv (x:G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      ((mem_center_iff.mp hx.1) ⟨t,ht⟩))
  have hxF : (x:G) ∈ F := ⟨hx.2,fun t ht =>
    mem_centralizer_singleton_iff.mp (hTx ht.1)⟩
  rcases hfour ⟨x,hxF⟩ with he | he | he | he
  · exact (hxne (Subtype.ext (congrArg (fun a : F => (a:G)) he))).elim
  · have he' : (x:G) = (u:G) := congrArg Subtype.val he
    exact (H.nonsingular_no_ambient_sylow D hTV hTI u hu T (he' ▸ hTx)).elim
  · have he' : (x:G) = (w:G) := congrArg Subtype.val he
    exact (H.nonsingular_no_ambient_sylow D hTV hTI w hw T (he' ▸ hTx)).elim
  · have he' : (x:G) = (u:G)*(w:G) := congrArg Subtype.val he
    exact he' ▸ hTx

end CFSG.Quasithin.Chapter12.Section06
