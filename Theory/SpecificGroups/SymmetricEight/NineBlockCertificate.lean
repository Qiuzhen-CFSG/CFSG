module
public import Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction
public import Mathlib.GroupTheory.Perm.Fin
/-!
# An even two-core normalized by two disjoint cubics

Commutators with the two standard disjoint three-cycles reduce the images
of each moved triple to 21 possibilities. Six successive swaps reconstruct
the permutation, up to the transposition of the two remaining points. The
resulting 882 completions are checked in 21 small kernel certificates, using
the parity of the constructing swaps. This avoids enumerating S₈.

The exported element calculation feeds `NineBlockContainment`, where subgroup
closure and Sylow conjugacy give the actual four-block containment required
in Aschbacher--Smith 12.6.19, printed p.828 of the 1 March 2004 manuscript.
-/

@[expose] public section
open Subgroup Equiv.Perm
namespace Theory.SpecificGroups.SymmetricEight.NineBlockCertificate
open Theory.SpecificGroups.SymmetricEight
open FourBlockCoreAction
abbrev S8 := Equiv.Perm (Fin 8)
def leftCubic : S8 := Equiv.swap 0 1 * Equiv.swap 1 2
def rightCubic : S8 := Equiv.swap 4 5 * Equiv.swap 5 6
def switch : S8 := Equiv.swap 3 7
def comm (x y : S8) : S8 := x*y*x⁻¹*y⁻¹
private def triple : Fin 21 → Fin 3 → Fin 8 := ![
 ![0,1,2], ![0,2,3], ![0,2,7], ![0,3,1], ![0,7,1],
 ![1,0,3], ![1,0,7], ![1,2,0], ![1,3,2], ![1,7,2],
 ![2,0,1], ![2,1,3], ![2,1,7], ![2,3,0], ![2,7,0],
 ![3,0,2], ![3,1,0], ![3,2,1], ![7,0,2], ![7,1,0], ![7,2,1]]
private def exchange : S8 := Equiv.swap 0 4 * Equiv.swap 1 5 * Equiv.swap 2 6

private def adjust (s : S8) (p v : Fin 8) : S8 := Equiv.swap (s p) v * s

private def complete (i j : Fin 21) : S8 :=
 let a := triple i
 let b := exchange ∘ triple j
 let s := adjust 1 0 (a 0)
 let s := adjust s 1 (a 1)
 let s := adjust s 2 (a 2)
 let s := adjust s 4 (b 0)
 let s := adjust s 5 (b 1)
 adjust s 6 (b 2)
private def completed (i j : Fin 21) (b : Bool) : S8 := complete i j * if b then switch else 1

private def candidate (g : S8) : Prop :=
 (∃ a b : Fin 4, g = kleinPerm a b) ∨
 (∃ a b : Fin 4, g = switch * kleinPerm a b * switch⁻¹)
private instance (g : S8) : Decidable (candidate g) := by unfold candidate; infer_instance

private theorem triple_certificate : ∀ a b c : Fin 8,
 a ≠ b → a ≠ c → b ≠ c →
 let h := (Equiv.swap a b * Equiv.swap b c) * leftCubic⁻¹
 h^8 = 1 → (comm h rightCubic)^8 = 1 →
 ∃ i, a = triple i 0 ∧ b = triple i 1 ∧ c = triple i 2 := by
 decide +kernel

private def align (f : Fin 8 → Fin 8) : List (Fin 8) → S8
 | [] => 1
 | p::ps => adjust (align f ps) p (f p)

private def values (i j : Fin 21) : Fin 8 → Fin 8 :=
 ![triple i 0,triple i 1,triple i 2,3,
   exchange (triple j 0),exchange (triple j 1),exchange (triple j 2),7]

private def alignParity (f : Fin 8 → Fin 8) : List (Fin 8) → ℤˣ
 | [] => 1
 | p::ps => (if align f ps p = f p then 1 else -1) * alignParity f ps

private theorem sign_align (f : Fin 8 → Fin 8) (ps : List (Fin 8)) :
 sign (align f ps) = alignParity f ps := by
 induction ps with
 | nil => rfl
 | cons p ps ih =>
   simp only [align,adjust,map_mul,Equiv.Perm.sign_swap',ih,alignParity]

private def parity (i j : Fin 21) (b : Bool) : ℤˣ :=
 alignParity (values i j) [6,5,4,2,1,0] * if b then -1 else 1

private theorem sign_completed (i j : Fin 21) (b : Bool) :
 sign (completed i j b) = parity i j b := by
 change sign (align (values i j) [6,5,4,2,1,0] * _) = _
 rw [map_mul,sign_align]
 congr 1
 cases b <;> decide

private theorem completion_0 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 0 j b
 parity 0 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_1 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 1 j b
 parity 1 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_2 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 2 j b
 parity 2 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_3 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 3 j b
 parity 3 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_4 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 4 j b
 parity 4 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_5 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 5 j b
 parity 5 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_6 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 6 j b
 parity 6 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_7 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 7 j b
 parity 7 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_8 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 8 j b
 parity 8 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_9 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 9 j b
 parity 9 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_10 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 10 j b
 parity 10 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_11 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 11 j b
 parity 11 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_12 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 12 j b
 parity 12 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_13 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 13 j b
 parity 13 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_14 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 14 j b
 parity 14 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_15 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 15 j b
 parity 15 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_16 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 16 j b
 parity 16 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_17 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 17 j b
 parity 17 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_18 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 18 j b
 parity 18 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_19 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 19 j b
 parity 19 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_20 : ∀ j : Fin 21, ∀ b : Bool,
 let g := completed 20 j b
 parity 20 j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by decide +kernel

private theorem completion_certificate : ∀ i j : Fin 21, ∀ b : Bool,
 let g := completed i j b
 parity i j b = 1 → g^8 = 1 → (comm g (leftCubic*rightCubic))^8 = 1 →
 candidate g := by
 intro i
 fin_cases i
 · exact completion_0
 · exact completion_1
 · exact completion_2
 · exact completion_3
 · exact completion_4
 · exact completion_5
 · exact completion_6
 · exact completion_7
 · exact completion_8
 · exact completion_9
 · exact completion_10
 · exact completion_11
 · exact completion_12
 · exact completion_13
 · exact completion_14
 · exact completion_15
 · exact completion_16
 · exact completion_17
 · exact completion_18
 · exact completion_19
 · exact completion_20

private theorem adjust_agree (s g : S8) (p q : Fin 8) (hs : s q = g q) :
    adjust s p (g p) q = g q := by
  by_cases hpq : p = q
  · subst p
    simp [adjust,hs]
  · have hsq : s q ≠ s p := s.injective.ne (Ne.symm hpq)
    have hgq : g q ≠ g p := g.injective.ne (Ne.symm hpq)
    change Equiv.swap (s p) (g p) (s q) = g q
    rw [Equiv.swap_apply_of_ne_of_ne hsq (hs ▸ hgq),hs]

private theorem align_agree (g : S8) (xs : List (Fin 8)) (q : Fin 8) (hq : q ∈ xs) :
    align g xs q = g q := by
  induction xs with
  | nil => simp at hq
  | cons p ps ih =>
    rcases List.mem_cons.mp hq with rfl | hq
    · simp [align,adjust]
    · exact adjust_agree _ g p q (ih hq)

private theorem seven_fixed (g : S8) (hg : ∀ a : Fin 8, a ≠ 7 → g a = a) : g = 1 := by
  have h7 : g 7 = 7 := by
    by_contra h
    exact h (g.injective (hg (g 7) h))
  apply Equiv.ext
  intro a
  change g a = a
  by_cases h : a = 7
  · simpa [h] using h7
  · exact hg a h

private theorem six_fixed (g : S8) (hg : ∀ a : Fin 8, a ∈ ([0,1,2,4,5,6] : List (Fin 8)) →
    g a = a) : g = 1 ∨ g = switch := by
  have h3 : g 3 = 3 ∨ g 3 = 7 := by
    have hh (a : Fin 8) (ha : a ∈ ([0,1,2,4,5,6] : List (Fin 8))) : g 3 ≠ a := by
      rw [←hg a ha]
      apply g.injective.ne
      intro he
      subst a
      simp at ha
    have h0 := hh 0 (by decide)
    have h1 := hh 1 (by decide)
    have h2 := hh 2 (by decide)
    have h4 := hh 4 (by decide)
    have h5 := hh 5 (by decide)
    have h6 := hh 6 (by decide)
    revert h0 h1 h2 h4 h5 h6
    generalize g 3 = v
    fin_cases v <;> simp
  rcases h3 with h3 | h3
  · left
    apply seven_fixed
    intro a ha
    fin_cases a <;> first | exact hg _ (by decide) | exact h3 | contradiction
  · right
    have he : switch * g = 1 := by
      apply seven_fixed
      intro a ha
      fin_cases a
      all_goals change switch (g _) = _
      all_goals first
        | contradiction
        | (rw [hg _ (by decide)]; rfl)
        | (change switch (g 3) = 3; rw [h3]; rfl)
    have hi : switch * switch = 1 := by decide
    exact mul_left_cancel (he.trans hi.symm)

private theorem completion_exists (g : S8) (i j : Fin 21)
    (hi : g 0 = triple i 0 ∧ g 1 = triple i 1 ∧ g 2 = triple i 2)
    (hj : g 4 = exchange (triple j 0) ∧ g 5 = exchange (triple j 1) ∧
      g 6 = exchange (triple j 2)) : ∃ b, g = completed i j b := by
  have he : align g [6,5,4,2,1,0] = complete i j := by
    simp only [align,complete,hi.1,hi.2.1,hi.2.2,hj.1,hj.2.1,hj.2.2,Function.comp_apply]
  have hf : ∀ a : Fin 8, a ∈ ([0,1,2,4,5,6] : List (Fin 8)) →
      ((complete i j)⁻¹ * g) a = a := by
    intro a ha
    have hm : a ∈ ([6,5,4,2,1,0] : List (Fin 8)) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
      tauto
    have hh := align_agree g [6,5,4,2,1,0] a hm
    rw [he] at hh
    change (complete i j).symm (g a) = a
    rw [←hh]
    exact (complete i j).symm_apply_apply a
  rcases six_fixed _ hf with hh | hh
  · refine ⟨false,?_⟩
    simpa [completed] using (inv_mul_eq_one.mp hh).symm
  · refine ⟨true,?_⟩
    exact (eq_mul_of_inv_mul_eq hh)

private theorem comm_map (f : S8 →* S8) (x y : S8) : f (comm x y) = comm (f x) (f y) := by
 simp only [comm,map_mul,map_inv]

private theorem conj_cubic (g : S8) :
 g * leftCubic * g⁻¹ = Equiv.swap (g 0) (g 1) * Equiv.swap (g 1) (g 2) := by
 calc
  _ = (g * Equiv.swap 0 1 * g⁻¹) * (g * Equiv.swap 1 2 * g⁻¹) := by
    simp only [leftCubic]; group
  _ = _ := by
    rw [Equiv.mul_swap_eq_swap_mul,Equiv.mul_swap_eq_swap_mul]
    simp

private theorem left_images (g : S8) (h : (comm g leftCubic)^8 = 1)
    (hh : (comm (comm g leftCubic) rightCubic)^8 = 1) :
    ∃ i, g 0 = triple i 0 ∧ g 1 = triple i 1 ∧ g 2 = triple i 2 := by
 have he : comm g leftCubic =
     (Equiv.swap (g 0) (g 1) * Equiv.swap (g 1) (g 2)) * leftCubic⁻¹ := by
   rw [comm,conj_cubic]
 exact triple_certificate (g 0) (g 1) (g 2) (g.injective.ne (by decide))
   (g.injective.ne (by decide)) (g.injective.ne (by decide)) (he ▸ h) (he ▸ hh)

private theorem right_images (g : S8) (h : (comm g rightCubic)^8 = 1)
    (hh : (comm (comm g rightCubic) leftCubic)^8 = 1) :
    ∃ j, g 4 = exchange (triple j 0) ∧ g 5 = exchange (triple j 1) ∧
      g 6 = exchange (triple j 2) := by
 let f := (MulAut.conj exchange).toMonoidHom
 have he : f leftCubic = rightCubic ∧ f rightCubic = leftCubic := by decide
 have h₁ : (comm (f g) leftCubic)^8 = 1 := by
   rw [←he.2,←comm_map,←map_pow,h,map_one]
 have h₂ : (comm (comm (f g) leftCubic) rightCubic)^8 = 1 := by
   calc
     _ = f ((comm (comm g rightCubic) leftCubic)^8) := by
       simp only [map_pow,comm_map,he.1,he.2]
     _ = 1 := by rw [hh,map_one]
 obtain ⟨j,h0,h1,h2⟩ := left_images (f g) h₁ h₂
 have hex : ∀ x : Fin 8, exchange (exchange x) = x := by decide
 refine ⟨j,?_,?_,?_⟩
 · change exchange (g 4) = triple j 0 at h0
   simpa only [hex] using congrArg exchange h0
 · change exchange (g 5) = triple j 1 at h1
   simpa only [hex] using congrArg exchange h1
 · change exchange (g 6) = triple j 2 at h2
   simpa only [hex] using congrArg exchange h2

theorem element_certificate (g : S8) (he : sign g = 1) (h8 : g^8 = 1)
    (hl : (comm g leftCubic)^8 = 1)
    (hlr : (comm (comm g leftCubic) rightCubic)^8 = 1)
    (hr : (comm g rightCubic)^8 = 1)
    (hrl : (comm (comm g rightCubic) leftCubic)^8 = 1)
    (hlr' : (comm g (leftCubic*rightCubic))^8 = 1) :
    (∃ a b : Fin 4, g = kleinPerm a b) ∨
      (∃ a b : Fin 4, g = switch * kleinPerm a b * switch⁻¹) := by
 obtain ⟨i,hi⟩ := left_images g hl hlr
 obtain ⟨j,hj⟩ := right_images g hr hrl
 obtain ⟨b,rfl⟩ := completion_exists g i j hi hj
 exact completion_certificate i j b ((sign_completed i j b) ▸ he) h8 hlr'

end Theory.SpecificGroups.SymmetricEight.NineBlockCertificate
