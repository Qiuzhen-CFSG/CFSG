module

public import Theory.Representation.BinaryNaturalDual.FourActors.A2Module.Actors
public import Theory.Representation.BinaryTransvectionGroups.Duality

/-!
# The three axes and common fixed plane of the mixed actor

The three marked transvections in the actual inner actor have pairwise
nontransvection products. Commutation fixes each transvection's nonzero
center. Equal centers or equal axes would make a nonidentity pair product
a transvection, so the centers and axes are distinct. Two centers therefore
span a plane of common fixed vectors; the fixed dimension of a pair product
bounds the common fixed space above by two. The rank-one formulas and axis
generation place the entire inner actor in this plane's radical.

The exceptional transvection marking and universal fixed dimensions for
transvections and other involutions remain explicit inputs. The resulting
subspace identities, hyperplane sums and radical containment are the natural
geometry used in Aschbacher–Smith, H.9.3(6), printed pp.391–392
(PDF pp.402–403 of the combined 1 March 2004 manuscript).
-/

public section

namespace BinaryNaturalDual.FourActors.A2Module
open BinaryLinear BinaryLinear.OuterCyclic Submodule

private theorem transvection_fixedSpace {w : X} {f : Module.Dual (ZMod 2) X}
    (hw : w ≠ 0) (hfw : f w = 0) :
    BinaryNaturalDual.fixedSpace (transvection w f hfw) = f.ker := by
  ext x
  rw [mem_fixedSpace]
  change x + f x • w = x ↔ f x = 0
  rw [add_eq_left, smul_eq_zero]
  simp [hw]

private theorem transvection_of_ne_one {w : X} {f : Module.Dual (ZMod 2) X}
    {hfw : f w = 0} (ht : transvection w f hfw ≠ 1) :
    IsTransvection (transvection w f hfw) := by
  refine ⟨w, f, ?_, ?_, hfw, rfl⟩
  · intro hw
    apply ht
    apply LinearEquiv.ext
    intro x
    change x + f x • w = x
    simp [hw]
  · intro hf
    apply ht
    apply LinearEquiv.ext
    intro x
    change x + f x • w = x
    simp [hf]

private theorem commuting_fixes_center {w : X} {f : Module.Dual (ZMod 2) X}
    (hw : w ≠ 0) (hf : f ≠ 0) (hfw : f w = 0)
    (e : G) (he : Commute e (transvection w f hfw)) : e w = w := by
  have h (x : X) : f x • e w = f (e x) • w := by
    have hx := congrArg (fun t : G => t x) he.eq
    change e (x + f x • w) = e x + f (e x) • w at hx
    simpa only [map_add, map_smul, add_right_inj] using hx
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra! h
    exact hf (LinearMap.ext h)
  have hx1 : f x = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hx
  have hx' := h x
  rw [hx1, one_smul] at hx'
  have hfx : f (e x) = 1 := by
    apply (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1)
    intro hz
    exact hw (e.map_eq_zero_iff.mp (by simpa [hz] using hx'))
  simpa [hfx] using hx'

private theorem same_center_product {w : X} {f l : Module.Dual (ZMod 2) X}
    (hfw : f w = 0) (hlw : l w = 0)
    (h : transvection w f hfw * transvection w l hlw ≠ 1) :
    IsTransvection (transvection w f hfw * transvection w l hlw) := by
  have hf : (f + l) w = 0 := by simp [hfw, hlw]
  have he : transvection w f hfw * transvection w l hlw =
      transvection w (f + l) hf := by
    apply LinearEquiv.ext
    intro x
    change (x + l x • w) + f (x + l x • w) • w = x + (f + l) x • w
    simp only [map_add, map_smul, hfw, smul_zero, add_zero, LinearMap.add_apply,
      add_smul]
    abel
  rw [he] at h ⊢
  exact transvection_of_ne_one h

private theorem same_form_product {v w : X} {f : Module.Dual (ZMod 2) X}
    (hfv : f v = 0) (hfw : f w = 0)
    (h : transvection v f hfv * transvection w f hfw ≠ 1) :
    IsTransvection (transvection v f hfv * transvection w f hfw) := by
  have hf : f (v + w) = 0 := by simp [hfv, hfw]
  have he : transvection v f hfv * transvection w f hfw =
      transvection (v + w) f hf := by
    apply LinearEquiv.ext
    intro x
    change (x + f x • w) + f (x + f x • w) • v = x + f x • (v + w)
    simp only [map_add, map_smul, hfw, smul_zero, add_zero, smul_add]
    abel
  rw [he] at h ⊢
  exact transvection_of_ne_one h

private theorem axisLinear_mul_ne_one {i j : Fin 3} (hij : i ≠ j) :
    axisLinear i * axisLinear j ≠ 1 := by
  intro h
  have hs : axisLinear j * axisLinear j = 1 := by
    simpa only [pow_two] using axisLinear_square j
  exact hij (axisLinear_injective (mul_right_cancel (h.trans hs.symm)))

private theorem center_mem_naturalFixed {i : Fin 3} {w : X} {f : Module.Dual (ZMod 2) X}
    (hw : w ≠ 0) (hf : f ≠ 0) (hfw : f w = 0)
    (hi : axisLinear i = transvection w f hfw) : w ∈ naturalFixed B2 := by
  apply (mem_naturalFixed_B2_iff w).mpr
  intro j
  apply commuting_fixes_center hw hf hfw
  rw [← hi]
  exact axisLinear_commute j i

variable (hmark : ∀ g : G, IsTransvection g ↔
  (linearAlternatingEquiv g).val.cycleType = {2, 2, 2, 2})
include hmark

/-- The three transvection axes are pairwise different as actual subspaces. -/
theorem axisLinear_fixedSpace_injective :
    Function.Injective (fun i : Fin 3 => BinaryNaturalDual.fixedSpace (axisLinear i)) := by
  intro i j he
  by_contra hij
  obtain ⟨v, f, hv, hf, hfv, hi⟩ := axisLinear_isTransvection hmark i
  obtain ⟨w, l, hw, hl, hlw, hj⟩ := axisLinear_isTransvection hmark j
  have heker : f.ker = l.ker := by
    simpa only [hi, hj, transvection_fixedSpace hv, transvection_fixedSpace hw] using he
  have hfl := BinaryTransvectionGroups.eq_of_ker_eq hf heker
  subst l
  apply axisLinear_mul_not_transvection hmark hij
  rw [hi, hj]
  exact same_form_product hfv hlw (by simpa only [← hi, ← hj] using axisLinear_mul_ne_one hij)

/-- The mixed inner actor fixes at least a plane, obtained from two different centers. -/
theorem two_le_finrank_naturalFixed_B2 :
    2 ≤ Module.finrank (ZMod 2) (naturalFixed B2) := by
  obtain ⟨v, f, hv, hf, hfv, hi⟩ := axisLinear_isTransvection hmark 0
  obtain ⟨w, l, hw, hl, hlw, hj⟩ := axisLinear_isTransvection hmark 1
  have hvw : v ≠ w := by
    intro he
    subst w
    apply axisLinear_mul_not_transvection hmark (by decide : (0 : Fin 3) ≠ 1)
    rw [hi, hj]
    exact same_center_product hfv hlw
      (by simpa only [← hi, ← hj] using axisLinear_mul_ne_one (by decide : (0 : Fin 3) ≠ 1))
  have hvW := center_mem_naturalFixed hv hf hfv hi
  have hwW := center_mem_naturalFixed hw hl hlw hj
  have hline : Submodule.span (ZMod 2) {v} ≤ naturalFixed B2 :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hvW
  have hwnot : w ∉ Submodule.span (ZMod 2) {v} := by
    intro hm
    rcases (BinaryTransvectionGroups.mem_centerLine_iff v w).mp hm with he | he
    · exact hw he
    · exact hvw he.symm
  have hlt : Submodule.span (ZMod 2) {v} < naturalFixed B2 :=
    lt_of_le_of_ne hline (by intro he; exact hwnot (he.symm ▸ hwW))
  have hd := Submodule.finrank_lt_finrank_of_lt hlt
  rw [finrank_span_singleton hv] at hd
  exact Nat.succ_le_of_lt hd

/-- Generation by the three transvections puts the entire actor in the plane radical. -/
theorem innerPreimage_B2_le_radical :
    innerPreimage B2 ≤ BinaryLinear.radical (naturalFixed B2) := by
  rw [innerPreimage_B2_eq_closure]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i, rfl⟩
  obtain ⟨w, f, hw, hf, hfw, hi⟩ := axisLinear_isTransvection hmark i
  have hwW := center_mem_naturalFixed hw hf hfw hi
  refine ⟨?_, ?_⟩
  · intro x hx
    exact (mem_naturalFixed_B2_iff x).mp hx i
  · intro x
    rw [hi]
    change (x + f x • w) - x ∈ naturalFixed B2
    simpa only [add_sub_cancel_left] using (naturalFixed B2).smul_mem (f x) hwW


variable (hN : ∀ g : G, g ^ 2 = 1 → g ≠ 1 → ¬ IsTransvection g →
  Module.finrank (ZMod 2) (BinaryNaturalDual.fixedSpace g) = 2)

omit hmark in
/-- Common fixed vectors are fixed by each actual inner actor. -/
theorem naturalFixed_B2_le_fixedSpace {g : G} (hg : g ∈ innerPreimage B2) :
    naturalFixed B2 ≤ BinaryNaturalDual.fixedSpace g := by
  intro x hx
  exact (mem_fixedSpace g x).mpr ((mem_naturalFixed B2 x).mp hx g hg)

include hN in
/-- The common natural fixed space of the mixed inner actor is a plane. -/
theorem naturalFixed_B2_finrank :
    Module.finrank (ZMod 2) (naturalFixed B2) = 2 := by
  have hg : axisLinear 0 * axisLinear 1 ∈ innerPreimage B2 :=
    (innerPreimage B2).mul_mem (conj_axisLinear_mem 0) (conj_axisLinear_mem 1)
  have hd := other_fixedSpace_finrank hN hg
    (axisLinear_mul_ne_one (by decide : (0 : Fin 3) ≠ 1))
    (axisLinear_mul_not_transvection hmark (by decide : (0 : Fin 3) ≠ 1))
  apply le_antisymm _ (two_le_finrank_naturalFixed_B2 hmark)
  have hle := Submodule.finrank_mono (naturalFixed_B2_le_fixedSpace hg)
  rwa [hd] at hle

include hN in
/-- Every remaining nonidentity element has exactly the common fixed plane. -/
theorem other_fixedSpace_eq_naturalFixed {g : G} (hg : g ∈ innerPreimage B2)
    (hg1 : g ≠ 1) (hgt : ¬ IsTransvection g) :
    BinaryNaturalDual.fixedSpace g = naturalFixed B2 := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq (naturalFixed_B2_le_fixedSpace hg)
  rw [naturalFixed_B2_finrank hmark hN, other_fixedSpace_finrank hN hg hg1 hgt]

variable (hT : ∀ g : G, IsTransvection g →
  Module.finrank (ZMod 2) (BinaryNaturalDual.fixedSpace g) = 3)
include hT

/-- Each of the three axes has dimension three in the natural four-space. -/
theorem axisLinear_fixedSpace_finrank (i : Fin 3) :
    Module.finrank (ZMod 2) (BinaryNaturalDual.fixedSpace (axisLinear i)) = 3 :=
  hT _ (axisLinear_isTransvection hmark i)

/-- The displayed axes are hyperplanes, as well as having the expected dimension. -/
theorem axisLinear_fixedSpace_isCoatom (i : Fin 3) :
    IsCoatom (BinaryNaturalDual.fixedSpace (axisLinear i)) := by
  have hdim : Module.finrank (ZMod 2) X = 4 := by simp [X]
  have hi := axisLinear_fixedSpace_finrank hmark hT i
  constructor
  · intro he
    rw [he, finrank_top, hdim] at hi
    contradiction
  · intro U hU
    apply Submodule.eq_of_le_of_finrank_eq le_top
    have hu := Submodule.finrank_lt_finrank_of_lt hU
    have hub := Submodule.finrank_le U
    rw [hi] at hu
    rw [hdim] at hub
    rw [finrank_top, hdim]
    omega

/-- Any two distinct transvection axes together span the whole natural module. -/
theorem axisLinear_fixedSpace_sup {i j : Fin 3} (hij : i ≠ j) :
    BinaryNaturalDual.fixedSpace (axisLinear i) ⊔
      BinaryNaturalDual.fixedSpace (axisLinear j) = ⊤ :=
  (axisLinear_fixedSpace_isCoatom hmark hT i).sup_eq_top_of_ne
    (axisLinear_fixedSpace_isCoatom hmark hT j)
    (fun he => hij (axisLinear_fixedSpace_injective hmark he))

include hN in
/-- Each pair of distinct axes meets in exactly the common natural fixed plane. -/
theorem naturalFixed_B2_eq_inf {i j : Fin 3} (hij : i ≠ j) :
    naturalFixed B2 = BinaryNaturalDual.fixedSpace (axisLinear i) ⊓
      BinaryNaturalDual.fixedSpace (axisLinear j) := by
  apply Submodule.eq_of_le_of_finrank_eq
    (le_inf (naturalFixed_B2_le_fixedSpace (conj_axisLinear_mem i))
      (naturalFixed_B2_le_fixedSpace (conj_axisLinear_mem j)))
  have hd := Submodule.finrank_sup_add_finrank_inf_eq
    (BinaryNaturalDual.fixedSpace (axisLinear i))
    (BinaryNaturalDual.fixedSpace (axisLinear j))
  rw [axisLinear_fixedSpace_sup hmark hT hij, finrank_top,
    axisLinear_fixedSpace_finrank hmark hT i,
    axisLinear_fixedSpace_finrank hmark hT j] at hd
  have hdim : Module.finrank (ZMod 2) X = 4 := by simp [X]
  rw [hdim] at hd
  rw [naturalFixed_B2_finrank hmark hN]
  have hd' : 4 + Module.finrank (ZMod 2)
      ↥(BinaryNaturalDual.fixedSpace (axisLinear i) ⊓
        BinaryNaturalDual.fixedSpace (axisLinear j)) = 4 + 2 := hd
  exact (Nat.add_left_cancel hd').symm

end BinaryNaturalDual.FourActors.A2Module
