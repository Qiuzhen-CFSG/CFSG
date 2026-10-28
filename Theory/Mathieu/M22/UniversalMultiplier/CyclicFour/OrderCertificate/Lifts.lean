module

public import Theory.Mathieu.M22.UniversalMultiplier.CyclicFour.Kernel
public import Theory.GroupTheory.SubgroupEnumeration

/-!
# Literal lifts of the native M₂₂ Schreier chain

The positive letters lift the published native words, and the negative letters
are their actual inverses. This distinction matters: a word representing an
involution in M₂₂ need not represent an involution in its paired cover.
The representatives and transition factors are exactly those of the native
chain. `Step0`–`Step3` request equalities in the paired group, with an explicit
power of the distinguished word as correction. `Terminal` requests its final
cubic relation. None of these certificate predicates is asserted here.

The order-certificate reduction consumes precisely these finite identities.
The source application is Aschbacher–Smith I.1.1 and I.1.3(4), printed p.407;
permutation provenance is recorded in the parent `source/README.md`.
-/

namespace Sporadic.Mathieu.M22CyclicFour.OrderCertificate

open Theory.GroupTheory
open Theory.GroupTheory.SubgroupEnumeration

@[expose] public section

/-- The two marked generators of the actual paired group. -/
noncomputable def positive0 : Fin 2 → Model
  | 0 => generatorA
  | 1 => generatorB

noncomputable def gen0 : Fin 4 → Model := symmGen positive0

/-- Positive native level-1 words, evaluated in the preceding lifted alphabet. -/
noncomputable def positive1 (i : Fin 3) : Model :=
  evalWord gen0 (m22L1GenWord (Fin.castAdd 3 i))

noncomputable def gen1 : Fin 6 → Model := symmGen positive1

/-- Positive native level-2 words, evaluated in the preceding lifted alphabet. -/
noncomputable def positive2 (i : Fin 4) : Model :=
  evalWord gen1 (m22L2GenWord (Fin.castAdd 4 i))

noncomputable def gen2 : Fin 8 → Model := symmGen positive2

/-- Positive native level-3 words, evaluated in the preceding lifted alphabet. -/
noncomputable def positive3 (i : Fin 3) : Model :=
  evalWord gen2 (m22L3GenWord (Fin.castAdd 3 i))

noncomputable def gen3 : Fin 6 → Model := symmGen positive3

/-- Positive native level-4 words, evaluated in the preceding lifted alphabet. -/
noncomputable def positive4 (i : Fin 1) : Model :=
  evalWord gen3 (m22L4GenWord (Fin.castAdd 1 i))

noncomputable def gen4 : Fin 2 → Model := symmGen positive4

theorem gen0_inv (i : Fin 4) :
    gen0 (symmInv (n := 2) i) = (gen0 i)⁻¹ := symmGen_inv positive0 i

theorem gen1_inv (i : Fin 6) :
    gen1 (symmInv (n := 3) i) = (gen1 i)⁻¹ := symmGen_inv positive1 i

theorem gen2_inv (i : Fin 8) :
    gen2 (symmInv (n := 4) i) = (gen2 i)⁻¹ := symmGen_inv positive2 i

theorem gen3_inv (i : Fin 6) :
    gen3 (symmInv (n := 3) i) = (gen3 i)⁻¹ := symmGen_inv positive3 i

theorem gen4_inv (i : Fin 2) :
    gen4 (symmInv (n := 1) i) = (gen4 i)⁻¹ := symmGen_inv positive4 i

/-- Word evaluation commutes with every homomorphism, with the same word order. -/
theorem map_evalWord {G H : Type*} [Group G] [Group H] {n : ℕ}
    (f : G →* H) (g : Fin n → G) (w : List (Fin n)) :
    f (evalWord g w) = evalWord (fun i => f (g i)) w := by
  induction w with
  | nil => exact f.map_one
  | cons i w ih => simp only [evalWord, map_mul, ih]

/-- The symmetric lifted alphabet projects to the original native alphabet. -/
theorem projection_gen0 (i : Fin 4) : ambientProjection (gen0 i) = m22L0Gen i := by
  fin_cases i
  · exact m22GeneratorA_eq_m22L0G0
  · exact m22GeneratorB_eq_m22L0G1
  · change ambientProjection (generatorA⁻¹) = _
    rw [map_inv]
    exact congrArg Inv.inv m22GeneratorA_eq_m22L0G0
  · change ambientProjection (generatorB⁻¹) = _
    rw [map_inv]
    exact congrArg Inv.inv m22GeneratorB_eq_m22L0G1


theorem projection_gen1 (i : Fin 6) : ambientProjection (gen1 i) = m22L1Gen i := by
  have hpos (j : Fin 3) : ambientProjection (positive1 j) =
      m22L1Gen (Fin.castAdd 3 j) := by
    rw [positive1, map_evalWord]
    simp only [projection_gen0]
    exact (m22L1Gen_eq_word _).symm
  fin_cases i
  · exact hpos 0
  · exact hpos 1
  · exact hpos 2
  · exact (map_inv ambientProjection (positive1 0)).trans (congrArg Inv.inv (hpos 0))
  · exact (map_inv ambientProjection (positive1 1)).trans (congrArg Inv.inv (hpos 1))
  · exact (map_inv ambientProjection (positive1 2)).trans (congrArg Inv.inv (hpos 2))

theorem projection_gen2 (i : Fin 8) : ambientProjection (gen2 i) = m22L2Gen i := by
  have hpos (j : Fin 4) : ambientProjection (positive2 j) =
      m22L2Gen (Fin.castAdd 4 j) := by
    rw [positive2, map_evalWord]
    simp only [projection_gen1]
    exact (m22L2Gen_eq_word _).symm
  fin_cases i
  · exact hpos 0
  · exact hpos 1
  · exact hpos 2
  · exact hpos 3
  · exact (map_inv ambientProjection (positive2 0)).trans (congrArg Inv.inv (hpos 0))
  · exact (map_inv ambientProjection (positive2 1)).trans (congrArg Inv.inv (hpos 1))
  · exact (map_inv ambientProjection (positive2 2)).trans (congrArg Inv.inv (hpos 2))
  · exact (map_inv ambientProjection (positive2 3)).trans (congrArg Inv.inv (hpos 3))

theorem projection_gen3 (i : Fin 6) : ambientProjection (gen3 i) = m22L3Gen i := by
  have hpos (j : Fin 3) : ambientProjection (positive3 j) =
      m22L3Gen (Fin.castAdd 3 j) := by
    rw [positive3, map_evalWord]
    simp only [projection_gen2]
    exact (m22L3Gen_eq_word _).symm
  fin_cases i
  · exact hpos 0
  · exact hpos 1
  · exact hpos 2
  · exact (map_inv ambientProjection (positive3 0)).trans (congrArg Inv.inv (hpos 0))
  · exact (map_inv ambientProjection (positive3 1)).trans (congrArg Inv.inv (hpos 1))
  · exact (map_inv ambientProjection (positive3 2)).trans (congrArg Inv.inv (hpos 2))

theorem projection_gen4 (i : Fin 2) : ambientProjection (gen4 i) = m22L4Gen i := by
  have hpos (j : Fin 1) : ambientProjection (positive4 j) =
      m22L4Gen (Fin.castAdd 1 j) := by
    rw [positive4, map_evalWord]
    simp only [projection_gen3]
    exact (m22L4Gen_eq_word _).symm
  fin_cases i
  · exact hpos 0
  · exact (map_inv ambientProjection (positive4 0)).trans (congrArg Inv.inv (hpos 0))

noncomputable def rep0 (r : Fin 22) : Model :=
  evalWord gen0 (m22L0RepWord r)

theorem rep0_one : rep0 0 = 1 := rfl

theorem projection_rep0 (r : Fin 22) : ambientProjection (rep0 r) = m22L0Rep r := by
  rw [rep0, map_evalWord]
  simp only [projection_gen0]
  exact (m22L0Rep_eq_word r).symm

/-- A finite family of literal paired-group identities, not just native identities. -/
def Step0 : Prop := ∀ i r, ∃ k : Fin 4,
  gen0 i * rep0 r =
    rep0 (m22L0Act i r) * evalWord gen1 (m22L0Factor i r) * centralWord ^ k.val

noncomputable def rep1 (r : Fin 21) : Model :=
  evalWord gen1 (m22L1RepWord r)

theorem rep1_one : rep1 0 = 1 := rfl

theorem projection_rep1 (r : Fin 21) : ambientProjection (rep1 r) = m22L1Rep r := by
  rw [rep1, map_evalWord]
  simp only [projection_gen1]
  exact (m22L1Rep_eq_word r).symm

/-- A finite family of literal paired-group identities, not just native identities. -/
def Step1 : Prop := ∀ i r, ∃ k : Fin 4,
  gen1 i * rep1 r =
    rep1 (m22L1Act i r) * evalWord gen2 (m22L1Factor i r) * centralWord ^ k.val

noncomputable def rep2 (r : Fin 20) : Model :=
  evalWord gen2 (m22L2RepWord r)

theorem rep2_one : rep2 0 = 1 := rfl

theorem projection_rep2 (r : Fin 20) : ambientProjection (rep2 r) = m22L2Rep r := by
  rw [rep2, map_evalWord]
  simp only [projection_gen2]
  exact (m22L2Rep_eq_word r).symm

/-- A finite family of literal paired-group identities, not just native identities. -/
def Step2 : Prop := ∀ i r, ∃ k : Fin 4,
  gen2 i * rep2 r =
    rep2 (m22L2Act i r) * evalWord gen3 (m22L2Factor i r) * centralWord ^ k.val

noncomputable def rep3 (r : Fin 16) : Model :=
  evalWord gen3 (m22L3RepWord r)

theorem rep3_one : rep3 0 = 1 := rfl

theorem projection_rep3 (r : Fin 16) : ambientProjection (rep3 r) = m22L3Rep r := by
  rw [rep3, map_evalWord]
  simp only [projection_gen3]
  exact (m22L3Rep_eq_word r).symm

/-- A finite family of literal paired-group identities, not just native identities. -/
def Step3 : Prop := ∀ i r, ∃ k : Fin 4,
  gen3 i * rep3 r =
    rep3 (m22L3Act i r) * evalWord gen4 (m22L3Factor i r) * centralWord ^ k.val

/-- The last positive lift has cube equal to the specified central word. -/
def Terminal : Prop := gen4 0 ^ 3 = centralWord

end
end Sporadic.Mathieu.M22CyclicFour.OrderCertificate
