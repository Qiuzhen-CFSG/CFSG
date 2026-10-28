module

public import Theory.SpecificGroups.LinearHigher.RootCalculus
public import Theory.SpecificGroups.HigherClassicalCovers.Linear.Projection

/-!
# Positive-root faithfulness and defining-prime index in degree four

The six positive elementary roots collect in descending row order. The six
strictly upper matrix entries recover their parameters, and a scalar upper
unitriangular matrix is the identity. Thus the elementary presentation is
faithful on its positive subgroup, including after projectivization. Its
order is |F|⁶. The actual PSL₄ order formula then gives index prime to p
when |F| = p.

This is only local faithfulness: no global presentation theorem or covering
universality is asserted. The local section consumer is `LocalSection`.
Source: Steinberg, *Lectures on Chevalley Groups*, §6, Lemma 36 (positive-root
collection), `refs/KGroup/GLS3/Chapter2St1.tex`; the multiplier application is
Aschbacher–Smith I.1.4(1),(3), printed pp.407–408, citing GLS3 §6.1.
-/

@[expose] public section

open Theory.SpecificGroups.LinearHigher
open scoped MatrixGroups
namespace Theory.SpecificGroups.HigherClassicalCovers.Linear.DefiningPrime
variable {F : Type*} [Field F]
abbrev x01 (a : F) := generator (root (0 : Fin 4) 1 (by decide)) a
abbrev x02 (a : F) := generator (root (0 : Fin 4) 2 (by decide)) a
abbrev x03 (a : F) := generator (root (0 : Fin 4) 3 (by decide)) a
abbrev x12 (a : F) := generator (root (1 : Fin 4) 2 (by decide)) a
abbrev x13 (a : F) := generator (root (1 : Fin 4) 3 (by decide)) a
abbrev x23 (a : F) := generator (root (2 : Fin 4) 3 (by decide)) a
private theorem swap {r s : Root 4} (hrs : r.val.2 ≠ s.val.1)
    (hsr : s.val.2 ≠ r.val.1) (a b : F) :
    generator r a * generator s b = generator s b * generator r a :=
  (generator_relations.commute r s a b hrs hsr).eq
private theorem exchange (i j k : Fin 4) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : F) :
    generator (root i j hij) a * generator (root j k hjk) b =
      generator (root j k hjk) b * generator (root i k hik) (a*b) *
        generator (root i j hij) a := by
  have h := generator_relations.conj_chain i j k hij hjk hik a b
  rw [(generator_relations.commute (root i k hik) (root j k hjk) (a*b) b
    hjk.symm hik.symm).eq] at h
  exact mul_inv_eq_iff_eq_mul.mp h

def normal (a b c d e f : F) : SteinbergGroup 4 F :=
  x23 f * x13 e * x12 d * x03 c * x02 b * x01 a

private theorem normal_zero : normal (0 : F) 0 0 0 0 0 = 1 := by
  simp [normal, x01, x02, x03, x12, x13, x23, generator_relations.zero]
private theorem normal_mul_01 (a b c d e f t : F) :
    normal a b c d e f * x01 t = normal (a+t) b c d e f := by
  simp only [normal, mul_assoc, x01, generator_relations.add]
private theorem normal_mul_02 (a b c d e f t : F) :
    normal a b c d e f * x02 t = normal a (b+t) c d e f := by
  simp only [normal, mul_assoc]
  rw [swap (r := root 0 1 (by decide)) (s := root 0 2 (by decide))
    (by decide) (by decide) a t, ← mul_assoc (x02 b), generator_relations.add]
private theorem normal_mul_03 (a b c d e f t : F) :
    normal a b c d e f * x03 t = normal a b (c+t) d e f := by
  simp only [normal, mul_assoc]
  rw [swap (r := root 0 1 (by decide)) (s := root 0 3 (by decide))
    (by decide) (by decide) a t, ← mul_assoc (x02 b),
    swap (r := root 0 2 (by decide)) (s := root 0 3 (by decide))
    (by decide) (by decide) b t]
  simp only [mul_assoc]
  rw [← mul_assoc (x03 c), generator_relations.add]
private theorem normal_mul_12 (a b c d e f t : F) :
    normal a b c d e f * x12 t = normal a (b+a*t) c (d+t) e f := by
  simp only [normal, mul_assoc]
  rw [exchange 0 1 2 (by decide) (by decide) (by decide) a t]
  simp only [mul_assoc]
  rw [← mul_assoc (x02 b), swap (r := root 0 2 (by decide)) (s := root 1 2 (by decide))
    (by decide) (by decide) b t]
  simp only [mul_assoc]
  rw [← mul_assoc (x03 c), swap (r := root 0 3 (by decide)) (s := root 1 2 (by decide))
    (by decide) (by decide) c t]
  simp only [mul_assoc]
  rw [← mul_assoc (x12 d), generator_relations.add,
    ← mul_assoc (x02 b), generator_relations.add]
private theorem normal_mul_13 (a b c d e f t : F) :
    normal a b c d e f * x13 t = normal a b (c+a*t) d (e+t) f := by
  simp only [normal, mul_assoc]
  rw [exchange 0 1 3 (by decide) (by decide) (by decide) a t]
  simp only [mul_assoc]
  rw [← mul_assoc (x02 b), swap (r := root 0 2 (by decide)) (s := root 1 3 (by decide))
    (by decide) (by decide) b t]
  simp only [mul_assoc]
  rw [← mul_assoc (x03 c), swap (r := root 0 3 (by decide)) (s := root 1 3 (by decide))
    (by decide) (by decide) c t]
  simp only [mul_assoc]
  rw [← mul_assoc (x12 d), swap (r := root 1 2 (by decide)) (s := root 1 3 (by decide))
    (by decide) (by decide) d t]
  simp only [mul_assoc]
  rw [← mul_assoc (x13 e), generator_relations.add,
    ← mul_assoc (x02 b), swap (r := root 0 2 (by decide)) (s := root 0 3 (by decide))
    (by decide) (by decide) b (a*t)]
  simp only [mul_assoc]
  rw [← mul_assoc (x03 c), generator_relations.add]
private theorem normal_mul_23 (a b c d e f t : F) :
    normal a b c d e f * x23 t = normal a b (c+b*t) d (e+d*t) (f+t) := by
  simp only [normal, mul_assoc]
  rw [swap (r := root 0 1 (by decide)) (s := root 2 3 (by decide))
    (by decide) (by decide) a t]
  rw [← mul_assoc (x02 b), exchange 0 2 3 (by decide) (by decide) (by decide) b t]
  simp only [mul_assoc]
  rw [← mul_assoc (x03 c), swap (r := root 0 3 (by decide)) (s := root 2 3 (by decide))
    (by decide) (by decide) c t]
  simp only [mul_assoc]
  rw [← mul_assoc (x12 d), exchange 1 2 3 (by decide) (by decide) (by decide) d t]
  simp only [mul_assoc]
  rw [← mul_assoc (x13 e), swap (r := root 1 3 (by decide)) (s := root 2 3 (by decide))
    (by decide) (by decide) e t]
  simp only [mul_assoc]
  rw [← mul_assoc (x23 f), generator_relations.add,
    ← mul_assoc (x13 e), generator_relations.add,
    ← mul_assoc (x03 c), generator_relations.add]

def upper (F : Type*) [Field F] : Subgroup (SteinbergGroup 4 F) :=
  Subgroup.closure {g | ∃ (r : Root 4) (a : F), r.val.1 < r.val.2 ∧ g = generator r a}

theorem exists_normal {g : SteinbergGroup 4 F} (hg : g ∈ upper F) :
    ∃ a b c d e f : F, g = normal a b c d e f := by
  have step (g : SteinbergGroup 4 F) (ih : ∃ a b c d e f : F, g = normal a b c d e f)
      (r : Root 4) (hr : r.val.1 < r.val.2) (t : F) :
      ∃ a b c d e f : F, g * generator r t = normal a b c d e f := by
    obtain ⟨a,b,c,d,e,f,rfl⟩ := ih
    obtain ⟨⟨i,j⟩,hij⟩ := r
    fin_cases i <;> fin_cases j <;> first
    | exact (by contradiction)
    | exact ⟨a+t,b,c,d,e,f,normal_mul_01 a b c d e f t⟩
    | exact ⟨a,b+t,c,d,e,f,normal_mul_02 a b c d e f t⟩
    | exact ⟨a,b,c+t,d,e,f,normal_mul_03 a b c d e f t⟩
    | exact ⟨a,b+a*t,c,d+t,e,f,normal_mul_12 a b c d e f t⟩
    | exact ⟨a,b,c+a*t,d,e+t,f,normal_mul_13 a b c d e f t⟩
    | exact ⟨a,b,c+b*t,d,e+d*t,f+t,normal_mul_23 a b c d e f t⟩
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨0,0,0,0,0,0,normal_zero.symm⟩
  | mul_right g _ y hy ih =>
    obtain ⟨r,a,hr,rfl⟩ := hy
    exact step g ih r hr a
  | mul_inv_cancel g _ y hy ih =>
    obtain ⟨r,a,hr,rfl⟩ := hy
    rw [← generator_relations.neg]
    exact step g ih r hr (-a)

theorem matrix_normal (a b c d e f : F) :
    (matrixMap (normal a b c d e f) : Matrix (Fin 4) (Fin 4) F) =
      !![1,a,b,c; 0,1,d,e; 0,0,1,f; 0,0,0,1] := by
  simp only [normal, x01, x02, x03, x12, x13, x23, map_mul, matrixMap_generator,
    Matrix.SpecialLinearGroup.coe_mul, matrixRoot,
    Matrix.SpecialLinearGroup.transvection_coe]
  simp [root, mul_add, add_mul, Matrix.single_mul_single_of_ne]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single]

theorem generator_mem_upper {r : Root 4} (hr : r.val.1 < r.val.2) (a : F) :
    generator r a ∈ upper F := Subgroup.subset_closure ⟨r,a,hr,rfl⟩

theorem normal_mem_upper (a b c d e f : F) : normal a b c d e f ∈ upper F := by
  unfold normal
  repeat apply (upper F).mul_mem
  all_goals exact generator_mem_upper (by decide) _

def coordinates (v : Fin 6 → F) : upper F :=
  ⟨normal (v 0) (v 1) (v 2) (v 3) (v 4) (v 5), normal_mem_upper _ _ _ _ _ _⟩

theorem coordinates_surjective : Function.Surjective (coordinates (F := F)) := by
  intro g
  obtain ⟨a,b,c,d,e,f,hg⟩ := exists_normal g.property
  exact ⟨![a,b,c,d,e,f], Subtype.ext hg.symm⟩

theorem coordinates_injective : Function.Injective (coordinates (F := F)) := by
  intro v w h
  have hm := congrArg (fun g : upper F =>
    (matrixMap g.val : Matrix (Fin 4) (Fin 4) F)) h
  change (matrixMap (normal (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) : Matrix (Fin 4) (Fin 4) F) =
    (matrixMap (normal (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)) : Matrix (Fin 4) (Fin 4) F) at hm
  rw [matrix_normal, matrix_normal] at hm
  funext i
  fin_cases i
  · exact congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 1) hm
  · exact congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 2) hm
  · exact congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 3) hm
  · exact congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 1 2) hm
  · exact congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 1 3) hm
  · exact congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 2 3) hm

instance [Finite F] : Finite (upper F) :=
  Finite.of_surjective coordinates coordinates_surjective

theorem card_upper [Finite F] : Nat.card (upper F) = Nat.card F ^ 6 := by
  rw [← Nat.card_congr (Equiv.ofBijective coordinates
    ⟨coordinates_injective, coordinates_surjective⟩)]
  simp [Nat.card_fun]

def upperProjection : upper F →* PSL(4, F) :=
  projectiveMap.comp (upper F).subtype

theorem upperProjection_injective : Function.Injective (upperProjection (F := F)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  have hprojective : projectiveMap g.val = 1 := hg
  rw [projectiveMap_eq] at hprojective
  have hcenter : matrixMap g.val ∈ Subgroup.center SL(4, F) :=
    (QuotientGroup.eq_one_iff _).mp hprojective
  obtain ⟨a,b,c,d,e,f,hg⟩ := exists_normal g.property
  have hm := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hcenter (0 : Fin 4)
  rw [hg, matrix_normal] at hm
  have ha : a = 0 := (congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 1) hm).symm
  have hb : b = 0 := (congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 2) hm).symm
  have hc : c = 0 := (congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 3) hm).symm
  have hd : d = 0 := (congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 1 2) hm).symm
  have he : e = 0 := (congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 1 3) hm).symm
  have hf : f = 0 := (congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 2 3) hm).symm
  change g = 1
  apply Subtype.ext
  simpa only [hg, ha, hb, hc, hd, he, hf, Subgroup.coe_one] using (normal_zero (F := F))

def projectiveUpper (F : Type*) [Field F] : Subgroup PSL(4, F) :=
  (upperProjection (F := F)).range

noncomputable def upperEquivProjective : upper F ≃* projectiveUpper F :=
  MonoidHom.ofInjective upperProjection_injective

theorem card_projectiveUpper [Finite F] :
    Nat.card (projectiveUpper F) = Nat.card F ^ 6 := by
  rw [← Nat.card_congr (upperEquivProjective (F := F)).toEquiv, card_upper]


theorem prime_not_dvd_projectiveUpper_index [Finite F] {p : ℕ}
    (hp : p.Prime) (hF : Nat.card F = p) :
    ¬ p ∣ (projectiveUpper F).index := by
  have horder := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
  rw [← (projectiveUpper F).card_mul_index, card_projectiveUpper, hF] at horder
  norm_num [Fin.prod_univ_succ] at horder
  have h41 : p^4 - p = p * (p^3 - 1) := by rw [Nat.mul_sub]; ring_nf
  have h42 : p^4 - p^2 = p^2 * (p^2 - 1) := by rw [Nat.mul_sub]; ring_nf
  have h43 : p^4 - p^3 = p^3 * (p - 1) := by rw [Nat.mul_sub]; ring_nf
  rw [h41, h42, h43] at horder
  have he : p^6 * ((projectiveUpper F).index * Nat.gcd 4 (p-1) * (p-1)) =
      p^6 * ((p^4-1) * (p^3-1) * (p^2-1) * (p-1)) := by
    calc
      _ = p^6 * (projectiveUpper F).index * Nat.gcd 4 (p-1) * (p-1) := by ring
      _ = _ := horder
      _ = _ := by ring
  have he' := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 6) he
  have hn (n : ℕ) (hn : 0 < n) : ¬ p ∣ p^n - 1 := by
    intro hd
    exact hp.not_dvd_one ((Nat.dvd_sub_iff_right (Nat.one_le_pow n p hp.pos)
      (dvd_pow_self p (by omega : n ≠ 0))).mp hd)
  intro hd
  have hm := dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd (Nat.gcd 4 (p-1))) (p-1)
  rw [he'] at hm
  exact hp.not_dvd_mul
    (hp.not_dvd_mul (hp.not_dvd_mul (hn 4 (by decide)) (hn 3 (by decide)))
      (hn 2 (by decide))) (by simpa using hn 1 (by decide)) hm


end Theory.SpecificGroups.HigherClassicalCovers.Linear.DefiningPrime
