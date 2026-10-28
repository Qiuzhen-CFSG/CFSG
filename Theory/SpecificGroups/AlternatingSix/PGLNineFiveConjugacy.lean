module
public import Theory.SpecificGroups.AlternatingSix.FivePointCoordinates
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic
public import Theory.SpecificGroups.AlternatingSix.PGLNineOvergroups
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Conjugacy of the actual A₅ subgroups in PGL₂(9)

The six-coset action marks every order-sixty subgroup of A₆ as a point
stabilizer under an automorphism. The natural S₆ has index two in Aut(A₆).
The projective conjugation action crosses its other coset: PGL₂(9) has an
element of order eight, whereas S₆ does not. Consequently the actual
projective conjugation action joins both A₅ classes, with no abstract
subgroup-catalogue or supplied compatibility hypothesis.
-/

public noncomputable section
namespace AlternatingSix.PGLNineFiveConjugacy
open Subgroup Equiv
open Atlas.Comparisons.Exceptional GorensteinWalter
local notation "A6" => alternatingGroup (Fin 6)
local notation "P" => PGL2 Nine.F

private instance : Finite P :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

private theorem odd : IsOddPrimePower (Nat.card Nine.F) := by
  rw [Nine.card]
  exact ⟨3,2,by decide,by decide,by decide,by decide⟩
private theorem large : 3 < Nat.card Nine.F := by rw [Nine.card]; decide

private def inclusion : A6 →* P :=
  Matrix.ProjectiveSpecialLinearGroup.toPGL.comp psl2NineCoordinatesEquivAlt6.symm.toMonoidHom
private def action : P →* MulAut A6 :=
  (MulAut.congr psl2NineCoordinatesEquivAlt6).toMonoidHom.comp
    (pgl2InnerAutPSL2 Nine.F odd large)
private theorem action_injective : Function.Injective action :=
  (MulAut.congr psl2NineCoordinatesEquivAlt6).injective.comp
    (pgl2InnerAutPSL2_injective Nine.F odd large)
private theorem action_inclusion (a : A6) : action (inclusion a) = MulAut.conj a := by
  apply MulEquiv.ext
  intro x
  change psl2NineCoordinatesEquivAlt6
    (pgl2InnerAutPSL2 Nine.F odd large
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (psl2NineCoordinatesEquivAlt6.symm a))
      (psl2NineCoordinatesEquivAlt6.symm x)) = _
  rw [pgl2InnerAutPSL2_toPGL]
  simp [MulAut.conj_apply]
private theorem inclusion_action (p : P) (a : A6) :
    inclusion (action p a) = p * inclusion a * p⁻¹ := by
  change Matrix.ProjectiveSpecialLinearGroup.toPGL
    (psl2NineCoordinatesEquivAlt6.symm
      (psl2NineCoordinatesEquivAlt6
        (pgl2InnerAutPSL2 Nine.F odd large p (psl2NineCoordinatesEquivAlt6.symm a)))) = _
  rw [psl2NineCoordinatesEquivAlt6.symm_apply_apply]
  exact toPGL_pgl2InnerAutPSL2_apply Nine.F odd large p _

private theorem perm_order_ne_eight (s : Perm (Fin 6)) : orderOf s ≠ 8 := by
  intro h
  have hd : orderOf s ∣ 4 := by
    rw [← s.lcm_cycleType,Multiset.lcm_dvd]
    intro n hn
    have hnd : n ∣ 8 := h ▸ Equiv.Perm.dvd_of_mem_cycleType hn
    have hns : n ≤ s.cycleType.sum := Multiset.le_sum_of_mem hn
    have hsum : s.cycleType.sum ≤ 6 := s.sum_cycleType_le
    have hn6 : n ≤ 6 := hns.trans hsum
    interval_cases n <;> norm_num at hnd <;> norm_num
  norm_num [h] at hd

private theorem exists_outside_natural : ∃ p : P, action p ∉ ShadowLocal.natural := by
  obtain ⟨T,_,hcyc,hcard,_⟩ := pgl2_split_torus_reflection_data Nine.F
  let : IsCyclic T := hcyc
  obtain ⟨x,hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := T)
  have ho : orderOf (x : P) = 8 := by rw [Subgroup.orderOf_coe,hx,hcard,Nine.card]
  refine ⟨x,?_⟩
  rintro ⟨s,hs⟩
  apply perm_order_ne_eight s
  change ShadowLocal.permutationAction s = action (x : P) at hs
  have hh := congrArg orderOf hs
  rw [orderOf_injective ShadowLocal.permutationAction ShadowLocal.permutationAction_injective,
    orderOf_injective action action_injective,ho] at hh
  exact hh

private theorem action_moves_to_point (H : Subgroup A6) (hH : Nat.card H = 60) :
    ∃ p : P, ∃ i : Fin 6, H.map (action p).toMonoidHom = MulAction.stabilizer A6 i := by
  obtain ⟨α,i,hα⟩ := FivePointCoordinates.exists_marked_point_automorphism H hH
  obtain ⟨p,hp⟩ := exists_outside_natural
  have hi : ShadowLocal.natural.index = 2 :=
    GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index
  have hfactor : ∃ s : Perm (Fin 6), ∃ q : P,
      α = ShadowLocal.permutationAction s * action q := by
    by_cases hn : α ∈ ShadowLocal.natural
    · obtain ⟨s,hs⟩ := hn
      change ShadowLocal.permutationAction s = α at hs
      exact ⟨s,1,by simpa using hs.symm⟩
    · have hm : α * (action p)⁻¹ ∈ ShadowLocal.natural :=
        (ShadowLocal.natural.mul_mem_iff_of_index_two hi).mpr
          (by simp only [inv_mem_iff]; exact iff_of_false hn hp)
      obtain ⟨s,hs⟩ := hm
      change ShadowLocal.permutationAction s = α * (action p)⁻¹ at hs
      refine ⟨s,p,?_⟩
      rw [hs]
      simp
  obtain ⟨s,q,hq⟩ := hfactor
  refine ⟨q,s⁻¹ i,?_⟩
  have he : (H.map (action q).toMonoidHom).map
      (ShadowLocal.permutationAction s).toMonoidHom = MulAction.stabilizer A6 i := by
    rw [map_map]
    change H.map (ShadowLocal.permutationAction s * action q).toMonoidHom = _
    rw [←hq,hα]
  apply eq_of_le_of_card_ge
  · intro x hx
    have hm : ShadowLocal.permutationAction s x ∈ MulAction.stabilizer A6 i :=
      he ▸ mem_map.mpr ⟨x,hx,rfl⟩
    have hf := MulAction.mem_stabilizer_iff.mp hm
    change s (x.val (s⁻¹ i)) = i at hf
    apply MulAction.mem_stabilizer_iff.mpr
    change x.val (s⁻¹ i) = s⁻¹ i
    apply s.injective
    rw [hf]
    exact (s.apply_symm_apply i).symm
  · rw [card_map_of_injective (action q).injective,hH,
      Nat.card_congr (SmallIndex.pointEquiv (n := 5) (s⁻¹ i)).toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]

/-- Any two literal order-sixty subgroups of A₆ are conjugated by the
actual PGL₂(9) action in the fixed exceptional-isomorphism coordinates. -/
private theorem action_conjugates_sixty (H J : Subgroup A6)
    (hH : Nat.card H = 60) (hJ : Nat.card J = 60) :
    ∃ p : P, H.map (action p).toMonoidHom = J := by
  obtain ⟨p,i,hp⟩ := action_moves_to_point H hH
  obtain ⟨q,k,hq⟩ := action_moves_to_point J hJ
  let : MulAction.IsPretransitive A6 (Fin 6) :=
    alternatingGroup.isPretransitive_of_three_le_card (Fin 6) (by simp)
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq A6 i k
  have hs : (MulAction.stabilizer A6 i).map (MulAut.conj a).toMonoidHom =
      MulAction.stabilizer A6 k := by
    rw [←MulAction.stabilizer_smul_eq_stabilizer_map_conj,ha]
  refine ⟨q⁻¹ * inclusion a * p,?_⟩
  apply (map_injective (f := (action q).toMonoidHom) (action q).injective)
  rw [map_map]
  have he : (action q).toMonoidHom.comp (action (q⁻¹ * inclusion a * p)).toMonoidHom =
      (MulAut.conj a).toMonoidHom.comp (action p).toMonoidHom := by
    change (action q * action (q⁻¹ * inclusion a * p)).toMonoidHom = _
    rw [←map_mul]
    rw [show q * (q⁻¹ * inclusion a * p) = inclusion a * p by group]
    rw [map_mul,action_inclusion]
    rfl
  rw [he,←map_map,hp,hs,hq]

/-- Any two actual A₅ subgroups of PGL₂(9) are conjugate inside that same
projective group. The conclusion retains both original subgroup carriers. -/
theorem five_subgroups_conjugate (H J : Subgroup P)
    (hH : Nonempty (H ≃* alternatingGroup (Fin 5)))
    (hJ : Nonempty (J ≃* alternatingGroup (Fin 5))) :
    ∃ p : P, H.map (MulAut.conj p).toMonoidHom = J := by
  have hi : Function.Injective inclusion :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp
      psl2NineCoordinatesEquivAlt6.symm.injective
  have hr : inclusion.range = Matrix.ProjectiveSpecialLinearGroup.toPGL.range := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨psl2NineCoordinatesEquivAlt6.symm a,rfl⟩
    · rintro ⟨a,rfl⟩
      exact ⟨psl2NineCoordinatesEquivAlt6 a,by simp [inclusion]⟩
  have hc : Nat.card inclusion.range = 360 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hi).toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hP : Nat.card P = 720 := by
    have hh := inclusion.range.card_mul_index
    rw [hc,hr,pgl2_psl2Range_index_eq_two Nine.F odd] at hh
    exact hh.symm
  have card (K : Subgroup P) (hk : Nonempty (K ≃* alternatingGroup (Fin 5))) :
      Nat.card K = 60 := by
    rw [Nat.card_congr hk.some.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have contains (K : Subgroup P) (hk : Nonempty (K ≃* alternatingGroup (Fin 5))) :
      K ≤ inclusion.range := by
    rw [hr]
    apply PGLNineOvergroups.proper_overgroup_le_psl K K hk le_rfl
    intro ht
    have hh := card K hk
    rw [ht,card_top,hP] at hh
    norm_num at hh
  have hmH : (H.comap inclusion).map inclusion = H := map_comap_eq_self (contains H hH)
  have hmJ : (J.comap inclusion).map inclusion = J := map_comap_eq_self (contains J hJ)
  have hcH : Nat.card (H.comap inclusion) = 60 := by
    rw [←card_map_of_injective (f := inclusion) hi,hmH,card H hH]
  have hcJ : Nat.card (J.comap inclusion) = 60 := by
    rw [←card_map_of_injective (f := inclusion) hi,hmJ,card J hJ]
  obtain ⟨p,hp⟩ := action_conjugates_sixty (H.comap inclusion) (J.comap inclusion) hcH hcJ
  refine ⟨p,?_⟩
  have hh := congrArg (fun K : Subgroup A6 => K.map inclusion) hp
  rw [map_map,hmJ] at hh
  rw [←hmH,map_map]
  convert hh using 1
  congr 1
  ext a
  exact (inclusion_action p a).symm

end AlternatingSix.PGLNineFiveConjugacy
