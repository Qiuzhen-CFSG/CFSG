module

public import Theory.SpecificGroups.Frobenius21.Recognition
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Cubic generators of exceptional factors

Every cubic subgroup normally generates a nonabelian group of order 21.
Distinct cubic subgroups do not commute and generate the whole group.
These statements retain the actual ambient subgroups and their conjugates,
for the compatibility step in the normal-closure theorem used in E.6.24.
-/

public section
namespace Frobenius21
open Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Composition of the literal ambient conjugation maps. -/
theorem conjugate_map_mul (C : Subgroup G) (a b : G) :
    (C.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      C.map (MulAut.conj (a*b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext c
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

/-- Normal generation by any cubic subgroup of the actual factor. -/
theorem conjugateSpanBy_eq_of_card_twenty_one {C B : Subgroup G}
    (hCB : C ≤ B) (hC : Nat.card C = 3) (hB : Nat.card B = 21)
    (hnab : ¬ ∀ x y : B, x*y=y*x) : conjugateSpanBy C B = B := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_card_eq hB hnab
  let D := (C.subgroupOf B).map e.toMonoidHom
  have hD : Nat.card D = 3 := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCB).toEquiv, hC]
  have hn := normalClosure_eq_top_of_card_three D hD
  have ht : normalClosure (C.subgroupOf B : Set B) = ⊤ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_top_of_surjective _ e.surjective,
      Subgroup.map_normalClosure _ _ e.surjective]
    exact hn
  rw [normalClosure_subgroupOf_eq_conjugateSpanBy C B hCB] at ht
  exact le_antisymm (conjugateSpanBy_le_self hCB) (subgroupOf_eq_top.mp ht)

/-- Commuting cubic subgroups in a group of order 21 coincide. -/
theorem cubic_eq_of_commuting {C D B : Subgroup G}
    (hCB : C ≤ B) (hDB : D ≤ B) (hC : Nat.card C = 3)
    (hD : Nat.card D = 3) (hB : Nat.card B = 21)
    (hcomm : ∀ c ∈ C, ∀ d ∈ D, Commute c d) : C = D := by
  have hn : D ≤ normalizer (C : Set G) :=
    (show D ≤ centralizer (C : Set G) from
      fun d hd => mem_centralizer_iff.mpr fun c hc => (hcomm c hc d hd).eq).trans
      (centralizer_le_normalizer _)
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes C D hn
  rw [hC, hD] at hp
  have hpos := Nat.card_pos (α := ↥(C ⊓ D))
  have hdiv : Nat.card ↥(C ⊔ D) ∣ 21 := hB ▸ card_dvd_of_le (sup_le hCB hDB)
  have hdiv3 : 3 ∣ Nat.card ↥(C ⊔ D) := hC ▸ card_dvd_of_le (le_sup_left : C ≤ C ⊔ D)
  obtain ⟨k, hk⟩ := hdiv3
  rw [hk] at hdiv
  have hk7 : k ∣ 7 := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 3)).mp hdiv
  have hsmall : Nat.card ↥(C ⊔ D) ≤ 9 := by nlinarith
  have hcs : Nat.card ↥(C ⊔ D) = 3 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hk7 with he | he <;> omega
  exact (eq_of_le_of_card_ge le_sup_left (by rw [hC, hcs])).trans
    (eq_of_le_of_card_ge le_sup_right (by rw [hD, hcs])).symm

/-- Distinct cubic subgroups of an order-21 factor generate it. -/
theorem sup_eq_of_distinct_cubic {C D B : Subgroup G}
    (hCB : C ≤ B) (hDB : D ≤ B) (hC : Nat.card C = 3)
    (hD : Nat.card D = 3) (hB : Nat.card B = 21) (hne : C ≠ D) : C ⊔ D = B := by
  have hdiv : Nat.card ↥(C ⊔ D) ∣ 21 := hB ▸ card_dvd_of_le (sup_le hCB hDB)
  have hdiv3 : 3 ∣ Nat.card ↥(C ⊔ D) := hC ▸ card_dvd_of_le (le_sup_left : C ≤ C ⊔ D)
  obtain ⟨k, hk⟩ := hdiv3
  rw [hk] at hdiv
  have hk7 : k ∣ 7 := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 3)).mp hdiv
  rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hk7 with he | he
  · have hcs : Nat.card ↥(C ⊔ D) = 3 := by omega
    exact False.elim (hne ((eq_of_le_of_card_ge le_sup_left (by rw [hC, hcs])).trans
      (eq_of_le_of_card_ge le_sup_right (by rw [hD, hcs])).symm))
  · exact eq_of_le_of_card_ge (sup_le hCB hDB) (by rw [hB, hk, he])

/-- A cubic subgroup has a distinct conjugate inside its nonabelian factor. -/
theorem exists_distinct_cubic_conjugate {C B : Subgroup G}
    (hCB : C ≤ B) (hC : Nat.card C = 3) (hB : Nat.card B = 21)
    (hnab : ¬ ∀ x y : B, x*y=y*x) :
    ∃ b : B, C.map (MulAut.conj (b : G)).toMonoidHom ≠ C := by
  classical
  by_contra! he
  have hg := conjugateSpanBy_eq_of_card_twenty_one hCB hC hB hnab
  rw [conjugateSpanBy_eq_iSup_conj] at hg
  simp only [he, iSup_const] at hg
  have hh := congrArg (fun K : Subgroup G => Nat.card K) hg
  rw [hC, hB] at hh
  omega

/-- If every ambient cubic conjugate belongs to B or centralizes B, the
distinct conjugates of B commute. Normal generation retains the actual B. -/
theorem commuting_conjugates_of_actor_dichotomy {C B : Subgroup G}
    (hCB : C ≤ B) (hC : Nat.card C = 3) (hB : Nat.card B = 21)
    (hnab : ¬ ∀ x y : B, x*y=y*x)
    (hdich : ∀ a : G, C.map (MulAut.conj a).toMonoidHom ≤ B ∨
      C.map (MulAut.conj a).toMonoidHom ≤ centralizer (B : Set G))
    (a : G) (hne : B.map (MulAut.conj a).toMonoidHom ≠ B) :
    ∀ b ∈ B, ∀ d ∈ B.map (MulAut.conj a).toMonoidHom, Commute b d := by
  classical
  let K := B.map (MulAut.conj a).toMonoidHom
  let D (b : B) := C.map (MulAut.conj (a*(b : G))).toMonoidHom
  have hKcard : Nat.card K = 21 :=
    (card_map_of_injective (MulAut.conj a).injective).trans hB
  have hgen : K = ⨆ b : B, D b := by
    have hh := congrArg (fun H : Subgroup G => H.map (MulAut.conj a).toMonoidHom)
      (conjugateSpanBy_eq_of_card_twenty_one hCB hC hB hnab)
    rw [conjugateSpanBy_eq_iSup_conj, map_iSup] at hh
    simp_rw [conjugate_map_mul] at hh
    exact hh.symm
  have hDK (b : B) : D b ≤ K := (le_iSup D b).trans hgen.ge
  have hDcard (b : B) : Nat.card (D b) = 3 :=
    (card_map_of_injective (MulAut.conj (a*(b : G))).injective).trans hC
  have hall : ∀ b : B, ¬ D b ≤ B := by
    intro b hb
    have hKB : K ≤ B := by
      rw [hgen]
      apply iSup_le
      intro d
      rcases hdich (a*(d : G)) with hd | hd
      · exact hd
      · have he : D b = D d := cubic_eq_of_commuting (hDK b) (hDK d)
          (hDcard b) (hDcard d) hKcard (by
            intro x hx y hy
            exact mem_centralizer_iff.mp (hd hy) x (hb hx))
        exact he ▸ hb
    exact hne (eq_of_le_of_card_ge hKB (by rw [hB, hKcard]))
  have hKC : K ≤ centralizer (B : Set G) := by
    rw [hgen]
    exact iSup_le fun b => (hdich (a*(b : G))).resolve_left (hall b)
  intro b hb d hd
  exact mem_centralizer_iff.mp (hKC hd) b hb

end Frobenius21
