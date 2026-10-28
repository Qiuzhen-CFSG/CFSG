module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.Degree
/-!
# Abelian offenders at every nonbinary symplectic degree

A commuting mixed-coordinate element has only two possible pairs of outside
coordinates, so an abelian subgroup containing it has order at most 2q².
For q > 2, an abelian offender above the q² movement bound must therefore
be the full point radical. Under a q² bound on the maximum-small-mover join,
the explicit plane and root families exclude that radical and put every
abelian offender in the same join.

This is the model calculation for the ordinary Thompson-subgroup step of
Meierfrankenfeld--Stellmacher (1993), (5.1), printed p.913. The literal
quotient consumer is `Glauberman.SymplecticSmallMoverThompson`; no Sylow or
field-linearity assumption is made on the subgroup under consideration.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

omit [Finite F] in
private theorem commuting_mixed_coordinates {b u w v c z t a : F}
    (hb : b ≠ 0) (hv : v ≠ 0)
    (hc : element b u w v * element c z t a = element c z t a * element b u w v) :
    (c = 0 ∧ a = 0) ∨ (c = b ∧ a = v) := by
  rw [element_mul,element_mul,element_eq_iff] at hc
  have h1 : v*c = a*b := by linear_combination hc.2.2.1
  have h2 : b*v*c = c*a*b := by linear_combination hc.2.1
  have hp : c*(c-b)=0 := by
    apply (mul_left_cancel₀ hv)
    linear_combination c*h1-h2
  rcases mul_eq_zero.mp hp with hz | he
  · left
    refine ⟨hz,?_⟩
    rw [hz,mul_zero] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_right hb
  · right
    have he : c=b := sub_eq_zero.mp he
    refine ⟨he,?_⟩
    rw [he,mul_comm v b,mul_comm a b] at h1
    exact ((mul_left_cancel₀ hb) h1).symm

private noncomputable def coords : unipotent (F := F) ≃ (F × F × F × F) :=
  (Equiv.ofBijective (fun x : F × F × F × F => element x.1 x.2.1 x.2.2.1 x.2.2.2)
    ⟨element_injective,element_surjective⟩).symm

private theorem coords_spec (x : unipotent (F := F)) :
    element (coords x).1 (coords x).2.1 (coords x).2.2.1 (coords x).2.2.2 = x :=
  (coords (F := F)).symm_apply_apply x

/-- A mixed-coordinate element has at most two possible outside-coordinate
pairs in its centralizer; the two central coordinates remain arbitrary. -/
theorem abelian_card_le_two_square_of_mixed
    (A : Subgroup (unipotent (F := F))) [IsMulCommutative A]
    {b u w v : F} (hx : element b u w v ∈ A) (hb : b ≠ 0) (hv : v ≠ 0) :
    Nat.card A ≤ 2 * Nat.card F ^ 2 := by
  classical
  have hpair (x : A) :
      ((coords x.val).1 = 0 ∧ (coords x.val).2.2.2 = 0) ∨
      ((coords x.val).1 = b ∧ (coords x.val).2.2.2 = v) := by
    apply commuting_mixed_coordinates hb hv
    rw [coords_spec]
    exact setLike_mul_comm hx x.property
  let f : A → Bool × F × F := fun x =>
    (decide ((coords x.val).1 = 0),(coords x.val).2.1,(coords x.val).2.2.1)
  have hf : Function.Injective f := by
    intro x y he
    have hbxy : (coords x.val).1=0 ↔ (coords y.val).1=0 := by
      have hh := congrArg Prod.fst he
      change decide ((coords x.val).1=0)=decide ((coords y.val).1=0) at hh
      simpa only [decide_eq_decide] using hh
    have huxy := congrArg (fun z : Bool × F × F => z.2.1) he
    have hwxy := congrArg (fun z : Bool × F × F => z.2.2) he
    apply Subtype.ext
    apply (coords (F := F)).injective
    rcases hpair x with hzero | hnonzero <;> rcases hpair y with hzero' | hnonzero'
    · exact Prod.ext (hzero.1.trans hzero'.1.symm)
        (Prod.ext huxy (Prod.ext hwxy (hzero.2.trans hzero'.2.symm)))
    · exact False.elim (hb (hnonzero'.1.symm.trans (hbxy.mp hzero.1)))
    · exact False.elim (hb (hnonzero.1.symm.trans (hbxy.mpr hzero'.1)))
    · exact Prod.ext (hnonzero.1.trans hnonzero'.1.symm)
        (Prod.ext huxy (Prod.ext hwxy (hnonzero.2.trans hnonzero'.2.symm)))
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_prod,show Nat.card Bool = 2 from by simp [Nat.card_eq_fintype_card],pow_two,mul_assoc] using hc

/-- An abelian subgroup larger than 2q² lies in an elementary radical. -/
theorem abelian_le_wing_of_large
    (A : Subgroup (unipotent (F := F))) [IsMulCommutative A]
    (hlarge : 2 * Nat.card F ^ 2 < Nat.card A) : A ≤ wing true ∨ A ≤ wing false := by
  have hm (b u w v : F) (hx : element b u w v ∈ A) : b=0 ∨ v=0 := by
    by_cases hb : b=0
    · exact Or.inl hb
    · right
      by_contra hv
      exact hlarge.not_ge (abelian_card_le_two_square_of_mixed A hx hb hv)
  by_cases hw : A ≤ wing true
  · exact Or.inl hw
  · right
    obtain ⟨x,hx,hxb⟩ := SetLike.not_le_iff_exists.mp hw
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
    have hb : b ≠ 0 := by simpa only [element_mem_wing,↓reduceIte] using hxb
    have hv : v=0 := (hm b u w v hx).resolve_left hb
    subst v
    intro y hy
    obtain ⟨⟨c,z,t,a⟩,rfl⟩ := element_surjective y
    change element c z t a ∈ wing false
    apply (element_mem_wing _ _ _ _ _).mpr
    change a=0
    rcases hm c z t a hy with hc | ha
    · have hprod := A.mul_mem hx hy
      rw [element_mul] at hprod
      rcases hm _ _ _ _ hprod with hz | hz
      · simp only [hc,add_zero] at hz
        exact False.elim (hb hz)
      · simpa using hz
    · exact ha

/-- At q > 2 the only abelian offender above the small-mover cutoff is
exactly the full point radical, in the same Sylow coordinates. -/
theorem abelian_offender_small_or_point
    (hq : 2 < Nat.card F) (A : Subgroup (unipotent (F := F)))
    [IsMulCommutative A] (hoff : movingIndex A ≤ Nat.card A) :
    Small A ∨ A = wing false := by
  by_cases hs : movingIndex A ≤ Nat.card F ^ 2
  · exact Or.inl ⟨hoff,hs⟩
  have hd : 3 ≤ Module.finrank F (Vector (F := F) ⧸ fixed A) := by
    by_contra hn
    exact hs (Nat.pow_le_pow_right Nat.card_pos (by omega))
  have hc : Nat.card F ^ 3 ≤ Nat.card A :=
    (Nat.pow_le_pow_right Nat.card_pos hd).trans hoff
  have hlarge : 2 * Nat.card F ^ 2 < Nat.card A := by
    have hp : 0 < Nat.card F ^ 2 := pow_pos Nat.card_pos _
    have hh : 2 * Nat.card F ^ 2 < Nat.card F * Nat.card F ^ 2 :=
      Nat.mul_lt_mul_of_pos_right hq hp
    have hcube : Nat.card F * Nat.card F ^ 2 = Nat.card F ^ 3 := by ring
    exact (hh.trans_eq hcube).trans_le hc
  rcases abelian_le_wing_of_large A hlarge with hw | hw
  · exact False.elim (hs (movingIndex_le_field_sq_of_le_wing A hw))
  · exact Or.inr (eq_of_le_of_card_ge hw (by rw [card_wing]; exact hc))
/-- If the maximum-small-mover join has order at most q², every small mover is contained in the join of the maximum-order
family; maximum here refers to order, so this requires the model geometry. -/
theorem small_le_join_of_card_le_square {T A : Subgroup (unipotent (F := F))}
    (hbound : Nat.card (join T) ≤ Nat.card F ^ 2)
    (hAT : A ≤ T) (hA : Small A) : A ≤ join T := by
  obtain ⟨E,hE⟩ := maximal_nonempty T
  have hEJ : E ≤ join T := le_sSup hE
  have hcard : Nat.card A ≤ Nat.card E := hE.2.2 A hAT hA
  rcases small_classification E hE.2.1 with hbot | ⟨s,rfl⟩ | ⟨hwing,hlarge⟩ | ⟨l,rfl⟩
  · rw [hbot,card_bot] at hcard
    exact (A.eq_bot_of_card_le hcard).le.trans bot_le
  · rcases small_classification A hA with hbot | ⟨t,rfl⟩ | ⟨_,hlarge⟩ | ⟨l,rfl⟩
    · exact hbot.le.trans bot_le
    · by_cases hst : s=t
      · exact hst ▸ hEJ
      · have hs := small_of_le_wing_of_large (rootFamily s ⊔ rootFamily t)
          (sup_le (rootFamily_le_wing s) (rootFamily_le_wing t))
          (rootFamily_sup_card hst).ge
        have hb := hE.2.2 _ (sup_le hE.1 hAT) hs
        rw [rootFamily_sup_card hst,card_rootFamily] at hb
        have hq : 1 < Nat.card F := Finite.one_lt_card
        have hsq : Nat.card F < Nat.card F ^ 2 := by nlinarith
        exact False.elim (hsq.not_ge hb)
    · rw [card_rootFamily] at hcard
      have hq : 1 < Nat.card F := Finite.one_lt_card
      have hsq : Nat.card F < Nat.card F ^ 2 := by nlinarith
      exact False.elim (hsq.not_ge (hlarge.trans hcard))
    · rw [card_finitePlane,card_rootFamily] at hcard
      have hq : 1 < Nat.card F := Finite.one_lt_card
      have hsq : Nat.card F < Nat.card F ^ 2 := by nlinarith
      exact False.elim (hsq.not_ge hcard)
  · have hEe := maximal_large_wing_eq_inf hE hwing hlarge
    rcases small_classification_nonstandard A hA with hAw | ⟨l,rfl⟩
    · exact (le_inf hAT hAw).trans_eq hEe.symm |>.trans hEJ
    · by_cases heq : Nat.card E = Nat.card F ^ 2
      · apply le_sSup
        refine ⟨hAT,small_finitePlane l,?_⟩
        intro B hBT hB
        simpa only [card_finitePlane,heq] using hE.2.2 B hBT hB
      · have hecap : Nat.card E ≤ Nat.card F ^ 2 := (card_le_of_le hEJ).trans hbound
        exact False.elim (heq (le_antisymm hecap hlarge))
  · have hTw := le_point_wing_of_maximal_finitePlane T l hE
    rcases small_classification A hA with hbot | ⟨s,rfl⟩ | ⟨_,hlarge⟩ | ⟨m,rfl⟩
    · exact hbot.le.trans bot_le
    · cases s with
      | none =>
        exact (show root (F := F) ≤ finitePlane l from
          (finitePlane_inf_center l).symm.trans_le inf_le_left).trans hEJ
      | some s =>
        have hh := hTw (hAT (show element 0 (s^2) s 1 ∈ finiteRoot s from
          (element_mem_finiteRoot _ _ _ _ _).mpr (by simp)))
        have hh : (1:F)=0 := (element_mem_wing _ _ _ _ _).mp hh
        exact False.elim (one_ne_zero hh)
    · apply le_sSup
      refine ⟨hAT,hA,?_⟩
      intro B hBT hB
      exact (hE.2.2 B hBT hB).trans (by rw [card_finitePlane]; exact hlarge)
    · apply le_sSup
      refine ⟨hAT,small_finitePlane m,?_⟩
      intro B hBT hB
      simpa only [card_finitePlane] using hE.2.2 B hBT hB

/-- The full point radical cannot lie in an edge whose maximum-small-mover
join has order at most q². Both distinct plane subgroups remain visible. -/
theorem not_point_le_of_join_card_le_square
    (T : Subgroup (unipotent (F := F))) (hbound : Nat.card (join T) ≤ Nat.card F ^ 2) :
    ¬ wing false ≤ T := by
  intro hpoint
  have h1 := small_le_join_of_card_le_square hbound
    ((plane_le_wing (F := F) none).trans hpoint) (small_plane (F := F) none)
  have h2 := small_le_join_of_card_le_square hbound
    ((plane_le_wing (F := F) (some 0)).trans hpoint) (small_plane (F := F) (some 0))
  have hle : wing false ≤ join T :=
    (plane_sup (F := F) (s := none) (t := some 0) (by simp)).symm.trans_le (sup_le h1 h2)
  have hc := (card_le_of_le hle).trans hbound
  rw [card_wing] at hc
  exact (pow_lt_pow_right₀ (Finite.one_lt_card : 1 < Nat.card F) (by decide : 2<3)).not_ge hc

/-- All abelian offenders lie in the small-mover join under the source
root-product order bound, at every nonbinary field degree. -/
theorem abelian_offender_le_join_of_card_le_square
    (hq : 2 < Nat.card F) (T A : Subgroup (unipotent (F := F)))
    [IsMulCommutative A] (hbound : Nat.card (join T) ≤ Nat.card F ^ 2)
    (hAT : A ≤ T) (hoff : movingIndex A ≤ Nat.card A) : A ≤ join T := by
  rcases abelian_offender_small_or_point hq A hoff with hs | he
  · exact small_le_join_of_card_le_square hbound hAT hs
  · exact False.elim (not_point_le_of_join_card_le_square T hbound (he ▸ hAT))

end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree
