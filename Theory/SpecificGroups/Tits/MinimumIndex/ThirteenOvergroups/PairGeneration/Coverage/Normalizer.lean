module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.Representatives

/-!
# Certified elements of the marked thirteen-normalizer

A five-letter word in the checked point-stabilizer generators conjugates
`ab` to its fourth power. The three-point base certifies that identity, and
finite cardinality upgrades inclusion of the cyclic subgroup to equality.
Consequently all 78 displayed products belong to the literal normalizer.
No assertion about the order or exhaustiveness of this family is needed.

Source: the primary ATLAS generators and the ambient Schreier certificate;
see `source/README.md` for the untrusted discovery of this short word.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration.CoverageCertificate
open Atlas1600OrderCertificate Theory.GroupTheory Subgroup

@[expose] public def chainGenerator (i : Fin 6) : Atlas1600Group :=
  ⟨L1Gen i, H0_eq_atlas ▸ H1_le
    (evalWord_mem_wordSubgroup L1Gen L1Inv L1Inv_spec [i])⟩

public theorem chainWord_val (w : List (Fin 6)) :
    (evalWord chainGenerator w).val = evalWord L1Gen w := by
  induction w with
  | nil => rfl
  | cons i w ih => change L1Gen i * (evalWord chainGenerator w).val = _; rw [ih]

@[expose] public def complement : Atlas1600Group := evalWord chainGenerator [1, 5, 4, 4, 4]
@[expose] public def fastComplement : Equiv.Perm (Fin 1600) := evalWord L1Gen [1, 5, 4, 4, 4]

public theorem fastComplement_eq : fastComplement = complement.val := (chainWord_val _).symm

set_option maxRecDepth 20000 in
public theorem complement_conjugates : complement * generator * complement⁻¹ = generator ^ 4 := by
  have h : ∀ p : Fin 3,
      (fastComplement * (L0G0 * L0G1) * fastComplement⁻¹) (p.castLE (by decide)) =
      ((L0G0 * L0G1) ^ 4) (p.castLE (by decide)) := by
    apply allFin
    decide +kernel
  have hv : generator.val = L0G0 * L0G1 := by
    simp only [L0G0_eq_atlas, L0G1_eq_atlas]; rfl
  apply ConverseLocalCoverage.DoubleCosetCertificate.threePoint_ext
  · change (complement.val * generator.val * complement.val⁻¹) 0 = (generator.val ^ 4) 0
    rw [hv, ← fastComplement_eq]
    exact h 0
  · change (complement.val * generator.val * complement.val⁻¹) 1 = (generator.val ^ 4) 1
    rw [hv, ← fastComplement_eq]
    exact h 1
  · change (complement.val * generator.val * complement.val⁻¹) 2 = (generator.val ^ 4) 2
    rw [hv, ← fastComplement_eq]
    exact h 2

public theorem complement_mem : complement ∈ thirteenNormalizer := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.eq_of_le_of_card_ge
  · change (zpowers generator).map (MulAut.conj complement).toMonoidHom ≤ zpowers generator
    rw [MonoidHom.map_zpowers]
    apply zpowers_le.mpr
    change complement * generator * complement⁻¹ ∈ zpowers generator
    rw [complement_conjugates]
    exact pow_mem (mem_zpowers generator) 4
  · rw [Subgroup.card_map_of_injective (MulAut.conj complement).injective]

@[expose] public def normalWord (n : Fin 78) : Atlas1600Group :=
  generator ^ (n.val % 13) * complement ^ (n.val / 13)

public theorem normalWord_mem (n : Fin 78) : normalWord n ∈ thirteenNormalizer :=
  thirteenNormalizer.mul_mem
    (thirteenNormalizer.pow_mem (thirteenSubgroup.le_normalizer (mem_zpowers generator)) _)
    (thirteenNormalizer.pow_mem complement_mem _)

@[expose] public def normalizerElement (n : Fin 78) : thirteenNormalizer :=
  ⟨normalWord n, normalWord_mem n⟩

@[expose] public def fastNormalWord (n : Fin 78) : Equiv.Perm (Fin 1600) :=
  (L0G0 * L0G1) ^ (n.val % 13) * fastComplement ^ (n.val / 13)

public theorem fastNormalWord_eq (n : Fin 78) : fastNormalWord n = (normalWord n).val := by
  change _ = generator.val ^ (n.val % 13) * complement.val ^ (n.val / 13)
  have hv : generator.val = L0G0 * L0G1 := by
    simp only [L0G0_eq_atlas, L0G1_eq_atlas]; rfl
  rw [hv, ← fastComplement_eq]
  rfl

end Tits.MinimumIndexThirteen.PairGeneration.CoverageCertificate
