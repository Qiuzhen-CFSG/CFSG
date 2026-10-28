module
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.Seeds
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Base
public import Mathlib.Data.Nat.Bits

/-!
# Kernel-checkable recovery words for thirteen-pairs

A recovery word is a product of integer powers of `ab` and its left conjugate by an
actual standard-generator word. Every such product lies in the literal
`pairSubgroup`. Equality is checked at the certified permutation base 0, 1, 2
using the existing packed ATLAS generators; the base theorem then proves
ambient equality. Recovering both standard generators proves generation of
the whole carrier. The same membership checker can recover generators of
candidate derived subgroups in exceptional cases.

Source: the primary ATLAS Tits generators. The permutation-base certificate
comes from the independently checked ambient Schreier chain in
`ConverseLocalCoverage.DoubleCosetCover.Base`.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration
open Subgroup Atlas1600OrderCertificate

@[expose] public def standardGenerator (b : Bool) : Atlas1600Group :=
  if b then ⟨atlas1600B, atlas1600B_mem⟩ else ⟨atlas1600A, atlas1600A_mem⟩

@[expose] public def wordValue {G : Type*} [Monoid G] (a b : G) (code : Nat) : G :=
  (code.bits.dropLast.map (fun c => if c then b else a)).prod

@[expose] public def standardWord (code : Nat) : Atlas1600Group :=
  wordValue (standardGenerator false) (standardGenerator true) code

@[expose] public def pairWord {G : Type*} [Group G] (u v : G)
    (w : List (Bool × Int)) : G :=
  (w.map (fun s => (if s.1 then v else u) ^ s.2)).prod

public theorem pairWord_mem (x : Atlas1600Group) (w : List (Bool × Int)) :
    pairWord generator (MulAut.conj x generator) w ∈ pairSubgroup x := by
  apply Subgroup.list_prod_mem
  intro y hy
  obtain ⟨⟨b, k⟩, _, rfl⟩ := List.mem_map.mp hy
  apply Subgroup.zpow_mem
  cases b
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers generator)
  · exact Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers generator))

@[expose] public def fastWord (code : Nat) : Equiv.Perm (Fin 1600) :=
  wordValue L0G0 L0G1 code

@[expose] public def fastPairWord (code : Nat) (w : List (Bool × Int)) :
    Equiv.Perm (Fin 1600) :=
  pairWord (L0G0 * L0G1)
    (fastWord code * (L0G0 * L0G1) * (fastWord code)⁻¹) w

@[expose] public def recoveryTest (code : Nat) (w : List (Bool × Int))
    (target : Nat) : Bool :=
  (fastPairWord code w 0 == fastWord target 0) &&
  (fastPairWord code w 1 == fastWord target 1) &&
  (fastPairWord code w 2 == fastWord target 2)

private theorem map_wordValue {G H : Type*} [Monoid G] [Monoid H]
    (f : G →* H) (a b : G) (code : Nat) :
    f (wordValue a b code) = wordValue (f a) (f b) code := by
  simp only [wordValue, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  cases c <;> rfl

private theorem map_pairWord {G H : Type*} [Group G] [Group H]
    (f : G →* H) (u v : G) (w : List (Bool × Int)) :
    f (pairWord u v w) = pairWord (f u) (f v) w := by
  simp only [pairWord, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨b, k⟩ _
  cases b <;> exact map_zpow f _ _

public theorem fastWord_eq (code : Nat) : fastWord code = (standardWord code).val := by
  let f : Atlas1600Group →* Equiv.Perm (Fin 1600) := atlas1600Subgroup.subtype
  change _ = f (wordValue _ _ code)
  rw [map_wordValue]
  simp only [fastWord, standardGenerator, Bool.false_eq_true, ↓reduceIte,
    L0G0_eq_atlas, L0G1_eq_atlas]
  rfl

private theorem fastPairWord_eq (code : Nat) (w : List (Bool × Int)) :
    fastPairWord code w =
      (pairWord generator (MulAut.conj (standardWord code) generator) w).val := by
  let f : Atlas1600Group →* Equiv.Perm (Fin 1600) := atlas1600Subgroup.subtype
  change _ = f (pairWord _ _ w)
  rw [map_pairWord]
  simp only [fastPairWord, L0G0_eq_atlas, L0G1_eq_atlas, fastWord_eq]
  rfl

public theorem recoveryTest_sound (code : Nat) (w : List (Bool × Int))
    (target : Nat) (h : recoveryTest code w target = true) :
    standardWord target ∈ pairSubgroup (standardWord code) := by
  have he : pairWord generator (MulAut.conj (standardWord code) generator) w =
      standardWord target := by
    simp only [recoveryTest, Bool.and_eq_true, beq_iff_eq,
      fastWord_eq, fastPairWord_eq] at h
    exact ConverseLocalCoverage.DoubleCosetCertificate.threePoint_ext h.1.1 h.1.2 h.2
  exact he ▸ pairWord_mem _ w

public theorem eq_top_of_standardGenerators_mem (H : Subgroup Atlas1600Group)
    (ha : standardGenerator false ∈ H) (hb : standardGenerator true ∈ H) : H = ⊤ := by
  have h : atlas1600Subgroup ≤ H.map atlas1600Subgroup.subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro y (rfl | rfl)
    · exact ⟨standardGenerator false, ha, rfl⟩
    · exact ⟨standardGenerator true, hb, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := h x.property
  exact (show y = x from Subtype.ext he) ▸ hy

public theorem pairSubgroup_eq_top_of_recovery (code : Nat)
    (wa wb : List (Bool × Int))
    (ha : recoveryTest code wa 2 = true) (hb : recoveryTest code wb 3 = true) :
    pairSubgroup (standardWord code) = ⊤ :=
  eq_top_of_standardGenerators_mem _ (recoveryTest_sound _ _ _ ha)
    (recoveryTest_sound _ _ _ hb)

end Tits.MinimumIndexThirteen.PairGeneration
