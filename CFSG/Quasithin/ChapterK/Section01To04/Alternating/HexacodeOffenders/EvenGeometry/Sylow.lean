module
public import Theory.Representation.HexacodeAction.TerminalIrreducible
public import Theory.Representation.BinaryOffender.Basic
public import Mathlib.GroupTheory.Sylow

/-!
# The concrete dihedral Sylow group in the even hexacode cover

Three explicit products of the existing adjacent-transposition lifts have
coordinate images (01)(23), (02)(13), and (01)(45). Their eight normal words
satisfy the dihedral multiplication law and form a Sylow two-subgroup.
The two coordinate planes in these normal words give the two four-groups;
the square test for a word and a product exhausts all elementary subgroups.

The systematic encoder parametrizes all 64 codewords. Counting the words
fixed by the two generators of each four-group gives fixed-space orders
4 and 16, hence binary dimensions 2 and 4. All finite checks are small
kernel-checked identities on the concrete monomial maps and codewords.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, K.1.3,
printed p.453 (PDF p.464). The encoder and coordinate lifts are the licensed
ATLAS constructions attributed in the imported code modules.
-/

public section
open Atlas.Codes Representation Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders.EvenGeometry.SylowModel

/-- The common central involution of the two four-groups. -/
@[expose] def z : HexEvenAutomorphisms := ⟨hexLift 0 * hexLift 2, by simp⟩
/-- The product of swaps within the first and last coordinate pairs. -/
@[expose] def t : HexEvenAutomorphisms := ⟨hexLift 0 * hexLift 4, by simp⟩
/-- The cross-pair involution on the first four coordinates. -/
@[expose] def s : HexEvenAutomorphisms := ⟨hexLift 1 * hexLift 0 * hexLift 2 * hexLift 1, by simp⟩


theorem z_coordinate : hexCoordinateSixHom z.val = Equiv.swap 0 1 * Equiv.swap 2 3 := by
  simp [z]

theorem t_coordinate : hexCoordinateSixHom t.val = Equiv.swap 0 1 * Equiv.swap 4 5 := by
  simp [t]

theorem s_coordinate : hexCoordinateSixHom s.val = Equiv.swap 0 2 * Equiv.swap 1 3 := by
  decide +kernel

theorem generators_not_commute : s * t ≠ t * s := by
  intro h
  have hh := congrArg (fun g : HexEvenAutomorphisms => hexCoordinateSixHom g.val) h
  exact (by decide +kernel : hexCoordinateSixHom (s * t).val ≠
    hexCoordinateSixHom (t * s).val) hh

abbrev Bits := Fin 2 × Fin 2 × Fin 2
abbrev PairBits := Fin 2 × Fin 2

def word (p : Bits) : HexEvenAutomorphisms := z ^ p.1.val * s ^ p.2.1.val * t ^ p.2.2.val

def mulBits (p q : Bits) : Bits :=
  (p.1 + q.1 + p.2.2 * q.2.1, p.2.1 + q.2.1, p.2.2 + q.2.2)
def invBits (p : Bits) : Bits := (p.1 + p.2.1 * p.2.2, p.2.1, p.2.2)

set_option maxRecDepth 4096 in
theorem word_mul (p q : Bits) : word (mulBits p q) = word p * word q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Monomial.ext
  · apply Equiv.ext; intro i; revert p q i; decide +kernel
  · funext i; apply LinearEquiv.ext; intro u; revert p q i u; decide +kernel

set_option maxRecDepth 4096 in
theorem word_inv (p : Bits) : word (invBits p) = (word p)⁻¹ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Monomial.ext
  · apply Equiv.ext; intro i; revert p i; decide +kernel
  · funext i; apply LinearEquiv.ext; intro u; revert p i u; decide +kernel

theorem word_injective : Function.Injective word := by
  intro p q he
  have hc := congrArg (fun g : HexEvenAutomorphisms => hexCoordinateSixHom g.val) he
  exact (by decide +kernel : ∀ p q : Bits,
    hexCoordinateSixHom (word p).val = hexCoordinateSixHom (word q).val → p = q) p q hc

private def rangeSubgroup {I : Type*} (f : I → HexEvenAutomorphisms)
    (ho : ∃ i, f i = 1) (hm : ∀ i j, ∃ k, f k = f i * f j)
    (hi : ∀ i, ∃ j, f j = (f i)⁻¹) : Subgroup HexEvenAutomorphisms where
  carrier := Set.range f
  one_mem' := ho
  mul_mem' := by rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩; exact hm i j
  inv_mem' := by rintro _ ⟨i, rfl⟩; exact hi i

def sylowGroup : Subgroup HexEvenAutomorphisms := rangeSubgroup word
  ⟨(0, 0, 0), by simp [word]⟩ (fun p q => ⟨mulBits p q, word_mul p q⟩)
  (fun p => ⟨invBits p, word_inv p⟩)

def firstWord (p : PairBits) := word (p.1, p.2, 0)
def secondWord (p : PairBits) := word (p.1, 0, p.2)

def lineGroup : Subgroup HexEvenAutomorphisms := rangeSubgroup firstWord
  ⟨(0, 0), by simp [firstWord, word]⟩
  (fun p q => ⟨(p.1 + q.1, p.2 + q.2), by
    simpa [firstWord, mulBits] using word_mul (p.1, p.2, 0) (q.1, q.2, 0)⟩)
  (fun p => ⟨p, by simpa [firstWord, invBits] using word_inv (p.1, p.2, 0)⟩)

def planeGroup : Subgroup HexEvenAutomorphisms := rangeSubgroup secondWord
  ⟨(0, 0), by simp [secondWord, word]⟩
  (fun p q => ⟨(p.1 + q.1, p.2 + q.2), by
    simpa [secondWord, mulBits] using word_mul (p.1, 0, p.2) (q.1, 0, q.2)⟩)
  (fun p => ⟨p, by simpa [secondWord, invBits] using word_inv (p.1, 0, p.2)⟩)

theorem sylowGroup_card : Nat.card sylowGroup = 8 := by
  change Nat.card (Set.range word) = 8
  rw [Nat.card_range_of_injective word_injective]
  simp [Bits]

theorem lineGroup_card : Nat.card lineGroup = 4 := by
  change Nat.card (Set.range firstWord) = 4
  have hi : Function.Injective firstWord := by
    intro p q h
    have hh := word_injective h
    exact Prod.ext (congrArg (fun p : Bits => p.1) hh) (congrArg (fun p : Bits => p.2.1) hh)
  rw [Nat.card_range_of_injective hi]
  simp [PairBits]

theorem planeGroup_card : Nat.card planeGroup = 4 := by
  change Nat.card (Set.range secondWord) = 4
  have hi : Function.Injective secondWord := by
    intro p q h
    have hh := word_injective h
    exact Prod.ext (congrArg (fun p : Bits => p.1) hh) (congrArg (fun p : Bits => p.2.2) hh)
  rw [Nat.card_range_of_injective hi]
  simp [PairBits]

@[expose] noncomputable def standardSylow : Sylow 2 HexEvenAutomorphisms :=
  (IsPGroup.of_card (show Nat.card sylowGroup = 2 ^ 3 by rw [sylowGroup_card]; decide)).toSylow (by
    have h := sylowGroup.card_mul_index
    rw [sylowGroup_card, hexEven_card] at h
    have hi : sylowGroup.index = 135 := by omega
    rw [hi]; decide)



@[simp] theorem standardSylow_coe : (standardSylow : Subgroup HexEvenAutomorphisms) = sylowGroup := rfl

private theorem elementary_of_inv (A : Subgroup HexEvenAutomorphisms)
    (h : ∀ x ∈ A, x⁻¹ = x) : IsElementaryAbelian 2 A := by
  have hi (x : A) : x⁻¹ = x := Subtype.ext (h x x.property)
  exact {
    toIsMulCommutative := ⟨⟨fun x y => by
      calc x * y = (x * y)⁻¹ := (hi _).symm
           _ = y⁻¹ * x⁻¹ := mul_inv_rev _ _
           _ = y * x := by rw [hi, hi]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun x => by
        calc x ^ 2 = x * x := pow_two x
             _ = x⁻¹ * x := congrArg (fun a => a * x) (hi x).symm
             _ = 1 := inv_mul_cancel x) }

theorem lineGroup_elementary : IsElementaryAbelian 2 lineGroup := by
  apply elementary_of_inv
  rintro _ ⟨p, rfl⟩
  simpa [firstWord, invBits] using (word_inv (p.1, p.2, 0)).symm

theorem planeGroup_elementary : IsElementaryAbelian 2 planeGroup := by
  apply elementary_of_inv
  rintro _ ⟨p, rfl⟩
  simpa [secondWord, invBits] using (word_inv (p.1, 0, p.2)).symm

theorem lineGroup_le_sylow : lineGroup ≤ sylowGroup := by
  rintro _ ⟨p, rfl⟩
  exact ⟨(p.1, p.2, 0), rfl⟩

theorem planeGroup_le_sylow : planeGroup ≤ sylowGroup := by
  rintro _ ⟨p, rfl⟩
  exact ⟨(p.1, 0, p.2), rfl⟩

theorem word_mem_line (p : Bits) : word p ∈ lineGroup ↔ p.2.2 = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    exact (congrArg (fun p : Bits => p.2.2) (word_injective hq)).symm
  · intro h
    refine ⟨(p.1, p.2.1), ?_⟩
    change word (p.1, p.2.1, 0) = word (p.1, p.2.1, p.2.2)
    rw [h]

theorem word_mem_plane (p : Bits) : word p ∈ planeGroup ↔ p.2.1 = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    exact (congrArg (fun p : Bits => p.2.1) (word_injective hq)).symm
  · intro h
    refine ⟨(p.1, p.2.2), ?_⟩
    change word (p.1, 0, p.2.2) = word (p.1, p.2.1, p.2.2)
    rw [h]

theorem line_ne_plane : lineGroup ≠ planeGroup := by
  intro h
  have hs : word (0, 1, 0) ∈ lineGroup := (word_mem_line _).mpr rfl
  rw [h, word_mem_plane] at hs
  exact (by decide : (1 : Fin 2) ≠ 0) hs

private theorem compatible (p q : Bits)
    (hp : word p ^ 2 = 1) (hq : word q ^ 2 = 1)
    (hpq : (word p * word q) ^ 2 = 1) : p.2.1 = 0 ∨ q.2.2 = 0 := by
  let f := hexCoordinateSixHom.comp hexSign.ker.subtype
  have h (g : HexEvenAutomorphisms) (hg : g ^ 2 = 1) : f g ^ 2 = 1 := by
    rw [← map_pow, hg, map_one]
  have hh := h (word p * word q) hpq
  rw [map_mul] at hh
  exact (by decide +kernel : ∀ p q : Bits,
    f (word p) ^ 2 = 1 → f (word q) ^ 2 = 1 →
    (f (word p) * f (word q)) ^ 2 = 1 → p.2.1 = 0 ∨ q.2.2 = 0)
      p q (h _ hp) (h _ hq) hh

/-- Every elementary subgroup of the actual Sylow group lies in one of its two four-groups. -/
theorem elementary_exhaustion (A : Subgroup HexEvenAutomorphisms)
    (hA : IsElementaryAbelian 2 A) (hAT : A ≤ sylowGroup) :
    A ≤ lineGroup ∨ A ≤ planeGroup := by
  classical
  let _ := hA
  by_cases h : A ≤ planeGroup
  · exact Or.inr h
  · left
    obtain ⟨x, hx, hxp⟩ := Set.not_subset.mp h
    obtain ⟨p, rfl⟩ := hAT hx
    have hp : p.2.1 ≠ 0 := fun hh => hxp ((word_mem_plane p).mpr hh)
    intro y hy
    obtain ⟨q, rfl⟩ := hAT hy
    apply (word_mem_line q).mpr
    exact (compatible p q
      (elemPow_eq_one_of_isElementaryAbelian _ hx)
      (elemPow_eq_one_of_isElementaryAbelian _ hy)
      (elemPow_eq_one_of_isElementaryAbelian _ (A.mul_mem hx hy))).resolve_left hp

/-- These are precisely the two four-groups in the chosen Sylow two-subgroup. -/
theorem fourGroup_exhaustion (A : Subgroup HexEvenAutomorphisms)
    (hA : IsElementaryAbelian 2 A) (hAT : A ≤ sylowGroup) (hc : Nat.card A = 4) :
    A = lineGroup ∨ A = planeGroup := by
  rcases elementary_exhaustion A hA hAT with h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [hc, lineGroup_card]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (by rw [hc, planeGroup_card]))

theorem mem_fixedSpace_line (v : hexacode) :
    v ∈ fixedSpace Hexacode.evenAction lineGroup ↔
      Hexacode.evenAction z v = v ∧ Hexacode.evenAction s v = v := by
  constructor
  · intro hv
    constructor
    · simpa [firstWord, word] using hv ⟨firstWord (1, 0), ⟨(1, 0), rfl⟩⟩
    · simpa [firstWord, word] using hv ⟨firstWord (0, 1), ⟨(0, 1), rfl⟩⟩
  · rintro ⟨hz, hs⟩ ⟨g, ⟨a, b⟩, rfl⟩
    fin_cases a <;> fin_cases b <;>
      simp [firstWord, word, map_mul, Module.End.mul_apply, hz, hs]

theorem mem_fixedSpace_plane (v : hexacode) :
    v ∈ fixedSpace Hexacode.evenAction planeGroup ↔
      Hexacode.evenAction z v = v ∧ Hexacode.evenAction t v = v := by
  constructor
  · intro hv
    constructor
    · simpa [secondWord, word] using hv ⟨secondWord (1, 0), ⟨(1, 0), rfl⟩⟩
    · simpa [secondWord, word] using hv ⟨secondWord (0, 1), ⟨(0, 1), rfl⟩⟩
  · rintro ⟨hz, ht⟩ ⟨g, ⟨a, b⟩, rfl⟩
    fin_cases a <;> fin_cases b <;>
      simp [secondWord, word, map_mul, Module.End.mul_apply, hz, ht]

private def parameterFixed (u : HexEvenAutomorphisms) (p : Fin 3 → K) : Prop :=
  Monomial.act z.val.val (systematicEncoder p) = systematicEncoder p ∧
    Monomial.act u.val.val (systematicEncoder p) = systematicEncoder p

private instance (u : HexEvenAutomorphisms) (p : Fin 3 → K) : Decidable (parameterFixed u p) :=
  inferInstanceAs (Decidable (_ ∧ _))

private noncomputable def fixedEquiv (u : HexEvenAutomorphisms)
    (A : Subgroup HexEvenAutomorphisms)
    (h : ∀ v, v ∈ fixedSpace Hexacode.evenAction A ↔
      Hexacode.evenAction z v = v ∧ Hexacode.evenAction u v = v) :
    fixedSpace Hexacode.evenAction A ≃ {p : Fin 3 → K // parameterFixed u p} where
  toFun v := ⟨hexProjection firstThree v.val, by
    obtain ⟨hz, hu⟩ := (h v.val).mp v.property
    change Monomial.act z.val.val (systematicEncoder (hexProjection firstThree v.val)) = _ ∧
      Monomial.act u.val.val (systematicEncoder (hexProjection firstThree v.val)) = _
    rw [systematic_reconstruct]
    exact ⟨congrArg Subtype.val hz, congrArg Subtype.val hu⟩⟩
  invFun p := ⟨⟨systematicEncoder p, systematic_mem p⟩, (h _).mpr
    ⟨Subtype.ext p.property.1, Subtype.ext p.property.2⟩⟩
  left_inv v := Subtype.ext (Subtype.ext (systematic_reconstruct v.val))
  right_inv p := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl

private theorem lineFixed_card :
    Nat.card (fixedSpace Hexacode.evenAction lineGroup) = 4 := by
  rw [Nat.card_congr (fixedEquiv s lineGroup mem_fixedSpace_line), Nat.card_eq_fintype_card]
  decide +kernel

private theorem planeFixed_card :
    Nat.card (fixedSpace Hexacode.evenAction planeGroup) = 16 := by
  rw [Nat.card_congr (fixedEquiv t planeGroup mem_fixedSpace_plane), Nat.card_eq_fintype_card]
  decide +kernel

theorem lineFixed_finrank :
    Module.finrank (ZMod 2) (fixedSpace Hexacode.evenAction lineGroup) = 2 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := fixedSpace Hexacode.evenAction lineGroup)
  rw [Nat.card_zmod, lineFixed_card] at h
  exact Nat.pow_right_injective (by decide : 1 < 2) h.symm

theorem planeFixed_finrank :
    Module.finrank (ZMod 2) (fixedSpace Hexacode.evenAction planeGroup) = 4 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := fixedSpace Hexacode.evenAction planeGroup)
  rw [Nat.card_zmod, planeFixed_card] at h
  exact Nat.pow_right_injective (by decide : 1 < 2) h.symm

end CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders.EvenGeometry.SylowModel
