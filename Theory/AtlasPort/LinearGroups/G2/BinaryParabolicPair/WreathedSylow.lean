module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.MarkedRestriction
public import ABG.ChapterII.Section1.WreathedDefs


/-!
# A wreathed presentation for the Sylow subgroup of G₂(2)′

In the six positive-root coordinates, membership in the actual commutator
subgroup is the equation `a₂ + a₃ + a₅ = 0`. The elements with coordinates
`s = (0,0,0,1,0,1)`, `t = (1,1,1,0,0,1)` and `z = (0,0,0,0,1,0)` satisfy
`s⁴ = t⁴ = z² = 1`; conjugation by `z` interchanges the commuting `s` and `t`.
Every allowed tuple is represented by `sⁱ tʲ zᵏ`, with `i,j < 4` and `k < 2`.
The polynomial coordinate laws verify these finite calculations in the kernel.
Lifting them through the original embedding proves the presentation for the
chosen Sylow subgroup `derivedSylow`, whose order is already known to be 32.

The presentation is Alperin–Brauer–Gorenstein, *Finite groups with
quasi-dihedral and wreathed Sylow 2-subgroups*, Chapter I, article p.2.
The concrete carrier and root-coordinate laws are from the licensed ATLAS
port through the imports; see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`.
-/

namespace Atlas.G2.BinaryParabolicPair
open Atlas.G2.Explicit BinaryCore

private def sParameters : Fin 6 → ZMod 2 := ![0,0,0,1,0,1]
private def tParameters : Fin 6 → ZMod 2 := ![1,1,1,0,0,1]
private def zParameters : Fin 6 → ZMod 2 := ![0,0,0,0,1,0]

private def powerParameters (a : Fin 6 → ZMod 2) : ℕ → Fin 6 → ZMod 2
  | 0 => 0
  | n+1 => unipotentProductParameters (powerParameters a n) a

private theorem product_powerParameters (a : Fin 6 → ZMod 2) (n : ℕ) :
    unipotentProduct (powerParameters a n) = unipotentProduct a ^ n := by
  induction n with
  | zero => exact unipotentProduct_zero
  | succ n hn => rw [powerParameters, ← unipotentProduct_mul, hn, pow_succ]

private theorem parameter_relations :
    powerParameters sParameters 4 = 0 ∧
    powerParameters tParameters 4 = 0 ∧
    powerParameters zParameters 2 = 0 ∧
    unipotentProductParameters (unipotentProductParameters zParameters sParameters)
      zParameters = tParameters ∧
    unipotentProductParameters (unipotentProductParameters zParameters tParameters)
      zParameters = sParameters ∧
    unipotentProductParameters sParameters tParameters =
      unipotentProductParameters tParameters sParameters := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem parameter_coverage : ∀ a : Fin 6 → ZMod 2,
    a 2 + a 3 + a 5 = 0 → ∃ i j : Fin 4, ∃ k : Fin 2,
      a = unipotentProductParameters
        (unipotentProductParameters (powerParameters sParameters i.val)
          (powerParameters tParameters j.val)) (powerParameters zParameters k.val) := by
  decide +kernel

private theorem product_mem_derived_iff (a : Fin 6 → ZMod 2) :
    unipotentProduct a ∈ DerivedModel ↔ a 2 + a 3 + a 5 = 0 := by
  change unipotentProduct a ∈ commutator (Model (ZMod 2)) ↔ _
  rw [commutator_eq_longRootClosure, ← QuotientGroup.eq_one_iff]
  change BinaryException.projection (unipotentProduct a) = 1 ↔ _
  simp only [unipotentProduct, map_mul, BinaryException.project_A,
    BinaryException.project_B, BinaryException.project_E, one_mul, mul_one,
    BinaryException.project_C_eq_D, BinaryException.project_D_eq_F]
  rw [← map_mul, ← map_mul, rootF_add, rootF_add]
  have hb : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide +kernel
  rcases hb (a 2 + a 3 + a 5) with h | h
  · simp [h, rootF_zero]
  · rw [h]
    exact iff_of_false quotientBit_ne_one (by decide)

private noncomputable def sylowElement (a : Fin 6 → ZMod 2)
    (ha : a 2 + a 3 + a 5 = 0) : derivedSylow :=
  ⟨⟨unipotentProduct a, (product_mem_derived_iff a).mpr ha⟩, by
    exact derivedSylow_eq.ge (unipotentProduct_mem a)⟩

private noncomputable def s : derivedSylow :=
  sylowElement sParameters (by decide +kernel)
private noncomputable def t : derivedSylow :=
  sylowElement tParameters (by decide +kernel)
private noncomputable def z : derivedSylow :=
  sylowElement zParameters (by decide +kernel)

private theorem s_four : s ^ 4 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change unipotentProduct sParameters ^ 4 = 1
  rw [← product_powerParameters, parameter_relations.1, unipotentProduct_zero]

private theorem t_four : t ^ 4 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change unipotentProduct tParameters ^ 4 = 1
  rw [← product_powerParameters, parameter_relations.2.1, unipotentProduct_zero]

private theorem z_two : z ^ 2 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change unipotentProduct zParameters ^ 2 = 1
  rw [← product_powerParameters, parameter_relations.2.2.1, unipotentProduct_zero]

private theorem z_inv : z⁻¹ = z :=
  inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using z_two)

private theorem conjugate_s : z⁻¹ * s * z = t := by
  rw [z_inv]
  apply Subtype.ext
  apply Subtype.ext
  change unipotentProduct zParameters * unipotentProduct sParameters *
    unipotentProduct zParameters = unipotentProduct tParameters
  rw [unipotentProduct_mul, unipotentProduct_mul, parameter_relations.2.2.2.1]

private theorem conjugate_t : z⁻¹ * t * z = s := by
  rw [z_inv]
  apply Subtype.ext
  apply Subtype.ext
  change unipotentProduct zParameters * unipotentProduct tParameters *
    unipotentProduct zParameters = unipotentProduct sParameters
  rw [unipotentProduct_mul, unipotentProduct_mul, parameter_relations.2.2.2.2.1]

private theorem s_t_commute : s * t = t * s := by
  apply Subtype.ext
  apply Subtype.ext
  change unipotentProduct sParameters * unipotentProduct tParameters =
    unipotentProduct tParameters * unipotentProduct sParameters
  rw [unipotentProduct_mul, unipotentProduct_mul, parameter_relations.2.2.2.2.2]

private theorem sylow_normal_form (x : derivedSylow) :
    ∃ i j : Fin 4, ∃ k : Fin 2, x = s ^ i.val * t ^ j.val * z ^ k.val := by
  have hxU : x.val.val ∈ unipotent := derivedSylow_eq.le x.prop
  rw [unipotent_eq_range] at hxU
  obtain ⟨a, ha⟩ := hxU
  have haD : unipotentProduct a ∈ DerivedModel := by rw [ha]; exact x.val.prop
  obtain ⟨i, j, k, hijk⟩ := parameter_coverage a ((product_mem_derived_iff a).mp haD)
  refine ⟨i, j, k, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change x.val.val = unipotentProduct sParameters ^ i.val *
    unipotentProduct tParameters ^ j.val * unipotentProduct zParameters ^ k.val
  rw [← ha, hijk]
  simp only [← unipotentProduct_mul, product_powerParameters]

private theorem sylow_generation : Subgroup.closure ({s, t, z} : Set derivedSylow) = ⊤ := by
  let H := Subgroup.closure ({s, t, z} : Set derivedSylow)
  have hs : s ∈ H := Subgroup.subset_closure (by simp)
  have ht : t ∈ H := Subgroup.subset_closure (by simp)
  have hz : z ∈ H := Subgroup.subset_closure (by simp)
  apply top_unique
  intro x _
  obtain ⟨i, j, k, rfl⟩ := sylow_normal_form x
  exact H.mul_mem (H.mul_mem (H.pow_mem hs _) (H.pow_mem ht _)) (H.pow_mem hz _)

/-- The actual positive-root Sylow subgroup of G₂(2)′ is wreathed of height two. -/
public theorem derivedSylow_isWreathedOfHeight : ABG.IsWreathedOfHeight derivedSylow 2 := by
  refine ⟨by decide, ?_, s, t, z, s_four, t_four, z_two, conjugate_s, conjugate_t,
    s_t_commute, sylow_generation⟩
  exact card_derivedSylow

end Atlas.G2.BinaryParabolicPair
