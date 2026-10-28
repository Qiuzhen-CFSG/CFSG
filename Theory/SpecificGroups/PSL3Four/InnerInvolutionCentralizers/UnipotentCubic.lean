module

public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Cubic fixed points in UT₃(F₄)

For the literal multiplication `(x,y,c)(x',y',c') =
(x+x',y+y',c+c'+xy')`, a nonidentity automorphism of order three fixing
`(0,0,1)` has fixed subgroup exactly the order-four center.

An automorphism permutes the two maximal exponent-two root planes; its cube
being the identity forces it to preserve each plane. On the four-element center,
fixing both the identity and the marked involution forces a cubic permutation
to be trivial. The cross-commutator pairing then relates the two quotient
coordinate actions. If either action has a nonzero fixed coordinate, both
are trivial. An automorphism trivial on both quotients and on the center
has square one, so a cubic such automorphism is the identity.

This is the local calculation for the inner involution and cubic common
centralizer in Aschbacher--Smith, *The Classification of Quasithin Groups*,
proof of 15.3.38, printed p.1137 (PDF p.1154). The root-plane geometry is
§5.3.5--5.3.7, printed p.660 (PDF p.677), in `refs/quasithin.pdf`.
-/

public section

open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3Four.InnerInvolutionCentralizers.UnipotentCubic
noncomputable section

private theorem cube_apply (β : MulAut (U F)) (hβ : β ^ 3 = 1) (a : U F) :
    β (β (β a)) = a := by
  have h := congrArg (fun γ : MulAut (U F) => γ a) hβ
  simpa only [pow_succ, pow_zero, MulAut.mul_apply, MulAut.one_apply] using h

/-- A cubic permutation of four points fixing two distinct points is trivial. -/
private theorem four_fixed {T : Type*} [Finite T] (hc : Nat.card T = 4)
    (f : T → T) (hi : Function.Injective f) (h3 : ∀ x, f (f (f x)) = x)
    (a b : T) (hab : a ≠ b) (ha : f a = a) (hb : f b = b) : ∀ x, f x = x := by
  classical
  let := Fintype.ofFinite T
  intro x
  by_contra hx
  have hxa : x ≠ a := by intro h; subst x; exact hx ha
  have hxb : x ≠ b := by intro h; subst x; exact hx hb
  have hfa : f x ≠ a := by intro h; exact hxa (hi (h.trans ha.symm))
  have hfb : f x ≠ b := by intro h; exact hxb (hi (h.trans hb.symm))
  have hffa : f (f x) ≠ a := by intro h; exact hfa (hi (h.trans ha.symm))
  have hffb : f (f x) ≠ b := by intro h; exact hfb (hi (h.trans hb.symm))
  have hffx : f (f x) ≠ x := by
    intro h
    have h' := congrArg f h
    rw [h3] at h'
    exact hx h'.symm
  have hfffx : f (f x) ≠ f x := fun h => hx (hi h)
  have hsize : ({a,b,x,f x,f (f x)} : Finset T).card = 5 := by
    simp [hab, hxa, hxb, hfa, hfb, hffa, hffb, hffx, hfffx, hx, Ne.symm]
  have hle := Finset.card_le_univ ({a,b,x,f x,f (f x)} : Finset T)
  rw [hsize, ← Nat.card_eq_fintype_card, hc] at hle
  omega

private theorem fixes_center (β : MulAut (U F)) (h3 : β ^ 3 = 1)
    (h1 : β ⟨0,0,1⟩ = ⟨0,0,1⟩) (c : F) : β ⟨0,0,c⟩ = ⟨0,0,c⟩ := by
  let e := Subgroup.centerCongr β
  have hz (c : F) : (⟨0,0,c⟩ : U F) ∈ Subgroup.center (U F) := by
    rw [← Z_eq_center, mem_Z]; exact ⟨rfl,rfl⟩
  have hc : Nat.card (Subgroup.center (U F)) = 4 := by rw [← Z_eq_center, card_Z, card_F]
  have hall := four_fixed hc e e.injective (fun x => Subtype.ext (cube_apply β h3 x))
    1 ⟨⟨0,0,1⟩, hz 1⟩ (by
      intro h
      have h' := congrArg (fun z : Subgroup.center (U F) => (z : U F).c) h
      exact zero_ne_one h') (map_one e) (Subtype.ext h1)
  exact congrArg Subtype.val (hall ⟨⟨0,0,c⟩, hz c⟩)

private theorem plane_image (β : MulAut (U F)) (P : Subgroup (U F))
    (hcard : Nat.card P = 16) (hexp : ∀ a ∈ P, a ^ 2 = 1) :
    P.map β.toMonoidHom = V₁ F ∨ P.map β.toMonoidHom = V₂ F := by
  have hs : Nat.card (P.map β.toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective β.injective, hcard]
  rcases le_plane_of_exponent_two F (P.map β.toMonoidHom) (by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hexp a ha, map_one]) with h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [hs, card_V₁, card_F]; decide))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (by rw [hs, card_V₂, card_F]; decide))

private theorem preserves_planes (β : MulAut (U F)) (h3 : β ^ 3 = 1) :
    (V₁ F).map β.toMonoidHom = V₁ F ∧ (V₂ F).map β.toMonoidHom = V₂ F := by
  have h₁ := plane_image β (V₁ F) (by rw [card_V₁, card_F]; rfl) (by
    intro a ha; exact (square_eq_one_iff F a).mpr (.inr ((mem_V₁ F a).mp ha)))
  have h₂ := plane_image β (V₂ F) (by rw [card_V₂, card_F]; rfl) (by
    intro a ha; exact (square_eq_one_iff F a).mpr (.inl ((mem_V₂ F a).mp ha)))
  have hne : V₁ F ≠ V₂ F := by
    intro h
    have hm : (⟨1,0,0⟩ : U F) ∈ V₂ F := h ▸ ((mem_V₁ F _).mpr rfl)
    exact one_ne_zero ((mem_V₂ F _).mp hm)
  have hmapne : (V₁ F).map β.toMonoidHom ≠ (V₂ F).map β.toMonoidHom :=
    fun h => hne (Subgroup.map_injective β.injective h)
  rcases h₁ with h₁ | h₁
  · exact ⟨h₁, h₂.resolve_left (fun h₂ => hmapne (h₁.trans h₂.symm))⟩
  · have h₂ := h₂.resolve_right (fun h₂ => hmapne (h₁.trans h₂.symm))
    have hmem : ∀ a, a ∈ V₁ F → β (β (β a)) ∈ V₂ F := by
      intro a ha
      have ha₁ : β a ∈ V₂ F := h₁ ▸ Subgroup.mem_map_of_mem β.toMonoidHom ha
      have ha₂ : β (β a) ∈ V₁ F := h₂ ▸ Subgroup.mem_map_of_mem β.toMonoidHom ha₁
      exact h₁ ▸ Subgroup.mem_map_of_mem β.toMonoidHom ha₂
    have hm := hmem ⟨1,0,0⟩ ((mem_V₁ F _).mpr rfl)
    rw [cube_apply β h3] at hm
    exact (one_ne_zero ((mem_V₂ F _).mp hm)).elim


private theorem plane_coordinates (β : MulAut (U F)) (h3 : β ^ 3 = 1) :
    (∀ a : U F, a.y = 0 → (β a).y = 0) ∧
    (∀ a : U F, a.x = 0 → (β a).x = 0) := by
  obtain ⟨h₁,h₂⟩ := preserves_planes β h3
  constructor
  · intro a ha
    apply (mem_V₁ F _).mp
    rw [← h₁]
    exact Subgroup.mem_map_of_mem β.toMonoidHom ((mem_V₁ F a).mpr ha)
  · intro a ha
    apply (mem_V₂ F _).mp
    rw [← h₂]
    exact Subgroup.mem_map_of_mem β.toMonoidHom ((mem_V₂ F a).mpr ha)

/-- Equivariance of the literal cross-commutator, after fixing the center. -/
private theorem cross_pairing (β : MulAut (U F)) (h3 : β ^ 3 = 1)
    (h1 : β ⟨0,0,1⟩ = ⟨0,0,1⟩) (x y : F) :
    (β ⟨x,0,0⟩).x * (β ⟨0,y,0⟩).y = x * y := by
  have hrel : (⟨x,0,0⟩ : U F) * ⟨0,y,0⟩ =
      (⟨0,y,0⟩ : U F) * ⟨x,0,0⟩ * ⟨0,0,x*y⟩ := by
    apply U.ext <;> simp [mul_x, mul_y, mul_c]
  have h := congrArg (fun a : U F => (β a).c) hrel
  rw [map_mul, map_mul, map_mul, fixes_center β h3 h1] at h
  have hx := (plane_coordinates β h3).1 ⟨x,0,0⟩ rfl
  have hy := (plane_coordinates β h3).2 ⟨0,y,0⟩ rfl
  simp only [mul_c, mul_x, hx, hy, mul_zero, add_zero, zero_add] at h
  rw [add_comm (β ⟨0,y,0⟩).c (β ⟨x,0,0⟩).c] at h
  exact add_left_cancel h

private theorem image_coordinates (β : MulAut (U F)) (h3 : β ^ 3 = 1)
    (h1 : β ⟨0,0,1⟩ = ⟨0,0,1⟩) (a : U F) :
    (β a).x = (β ⟨a.x,0,0⟩).x ∧ (β a).y = (β ⟨0,a.y,0⟩).y := by
  have hdec : a = (⟨0,a.y,0⟩ : U F) * ⟨a.x,0,0⟩ * ⟨0,0,a.c⟩ := by
    apply U.ext <;> simp
  have hmap : β a = β ⟨0,a.y,0⟩ * β ⟨a.x,0,0⟩ * ⟨0,0,a.c⟩ := by
    conv_lhs => rw [hdec, map_mul, map_mul, fixes_center β h3 h1]
  rw [hmap]
  have hx := (plane_coordinates β h3).1 ⟨a.x,0,0⟩ rfl
  have hy := (plane_coordinates β h3).2 ⟨0,a.y,0⟩ rfl
  simp [hx,hy]

/-- The central shear kernel has exponent two and contains no nontrivial cubic. -/
private theorem eq_one_of_coordinates (β : MulAut (U F)) (h3 : β ^ 3 = 1)
    (h1 : β ⟨0,0,1⟩ = ⟨0,0,1⟩)
    (hxy : ∀ a, (β a).x = a.x ∧ (β a).y = a.y) : β = 1 := by
  have hsq (a : U F) : β (β a) = a := by
    let z : U F := ⟨0,0,(β a).c + a.c⟩
    have hform : β a = a * z := by
      apply U.ext (by simpa [z] using (hxy a).1) (by simpa [z] using (hxy a).2)
      change (β a).c = a.c + ((β a).c + a.c) + a.x * 0
      rw [mul_zero, add_zero, add_left_comm, CharTwo.add_self_eq_zero, add_zero]
    have hz : β z = z := fixes_center β h3 h1 _
    have hz2 : z * z = 1 := by
      apply U.ext <;> simp [z, CharTwo.add_self_eq_zero]
    calc
      β (β a) = β (a * z) := congrArg β hform
      _ = (a * z) * z := by rw [map_mul, hform, hz]
      _ = a := by rw [mul_assoc, hz2, mul_one]
  ext a : 1
  exact (hsq (β a)).symm.trans (cube_apply β h3 a)

private theorem fixed_mem_center (β : MulAut (U F)) (hne : β ≠ 1) (h3 : β ^ 3 = 1)
    (h1 : β ⟨0,0,1⟩ = ⟨0,0,1⟩) (a : U F) (ha : β a = a) : a ∈ Z F := by
  have hpair := cross_pairing β h3 h1
  have hcoords := image_coordinates β h3 h1
  have hax : (β ⟨a.x,0,0⟩).x = a.x := (hcoords a).1.symm.trans (congrArg U.x ha)
  have hay : (β ⟨0,a.y,0⟩).y = a.y := (hcoords a).2.symm.trans (congrArg U.y ha)
  rw [mem_Z]
  by_contra h
  have hxy : ∀ t, (β t).x = t.x ∧ (β t).y = t.y := by
    by_cases hx : a.x = 0
    · have hy : a.y ≠ 0 := fun hy => h ⟨hx,hy⟩
      have hX (x : F) : (β ⟨x,0,0⟩).x = x :=
        mul_right_cancel₀ hy (by simpa only [hay] using hpair x a.y)
      have hY (y : F) : (β ⟨0,y,0⟩).y = y := by
        simpa only [hX, one_mul] using hpair 1 y
      intro t
      exact ⟨(hcoords t).1.trans (hX t.x), (hcoords t).2.trans (hY t.y)⟩
    · have hY (y : F) : (β ⟨0,y,0⟩).y = y :=
        mul_left_cancel₀ hx (by simpa only [hax] using hpair a.x y)
      have hX (x : F) : (β ⟨x,0,0⟩).x = x := by
        simpa only [hY, mul_one] using hpair x 1
      intro t
      exact ⟨(hcoords t).1.trans (hX t.x), (hcoords t).2.trans (hY t.y)⟩
  exact hne (eq_one_of_coordinates β h3 h1 hxy)

/-- A nonidentity cubic automorphism fixing the marked central involution has
exactly the center as its fixed subgroup. -/
theorem fixedSubgroup_eq_center (β : MulAut (U F)) (hne : β ≠ 1) (h3 : β ^ 3 = 1)
    (h1 : β ⟨0,0,1⟩ = ⟨0,0,1⟩) : β.fixedSubgroup = Z F := by
  ext a
  rw [MulAut.mem_fixedSubgroup]
  constructor
  · exact fixed_mem_center β hne h3 h1 a
  · intro ha
    obtain ⟨hx,hy⟩ := (mem_Z F a).mp ha
    have he : a = ⟨0,0,a.c⟩ := U.ext hx hy rfl
    rw [he]
    exact fixes_center β h3 h1 a.c

/-- The fixed subgroup of the marked nonidentity cubic has order four. -/
theorem card_fixedSubgroup (β : MulAut (U F)) (hne : β ≠ 1) (h3 : β ^ 3 = 1)
    (h1 : β ⟨0,0,1⟩ = ⟨0,0,1⟩) : Nat.card β.fixedSubgroup = 4 := by
  rw [fixedSubgroup_eq_center β hne h3 h1, card_Z, card_F]

/-- The local UT₃(F₄) bound used in the cubic common-centralizer calculation. -/
theorem card_fixedSubgroup_le (β : MulAut (U F)) (hne : β ≠ 1) (h3 : β ^ 3 = 1)
    (h1 : β ⟨0,0,1⟩ = ⟨0,0,1⟩) : Nat.card β.fixedSubgroup ≤ 4 :=
  (card_fixedSubgroup β hne h3 h1).le

end
end Matrix.PSL3Four.InnerInvolutionCentralizers.UnipotentCubic
