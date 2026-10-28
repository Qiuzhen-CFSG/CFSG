module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic
public import Theory.GroupTheory.Commutator.CentralExtensionPairing
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Additive transvection lifts in odd-prime symplectic groups

Every root parameter group over the prime field is cyclic. Its full preimage
in a central extension is therefore abelian. For p > 3 choose c with c² ≠ 1
and a symplectic element sending v to cv. Commutating its lift with a lift
of the transvection of parameter t/(c²−1) gives an additive section of the
transvection group. In a perfect central cover these lifted groups generate
the entire covering group.

The compatibility is with the literal `Matrix.PSp4Three.parameterHom`. The
last theorem is the consumer of the lifting calculation. Cross-direction
relations, which would make these sections a section of the whole matrix
group, are not proved here. At p = 3 only the commuting-preimage theorem is
asserted; there is no scalar with c² ≠ 1.

Source: the root-lifting method for the upper bound in the type C₂ multiplier
calculation, cited in Aschbacher–Smith I.1.4, p.408, and GLS3 §6.1.
The commutator construction uses the same elementary argument as the existing
characteristic-two `SymplecticFour.CentralRootLifts` module. Scalar selection
adapts Gerald Höhn's ATLAS `Symplectic/PerfectLarge.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`; see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff` for its license and attribution. The prime-field
cyclic-preimage argument is independent of the characteristic-two pairing.
-/

public section
noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime
open Matrix.PSp4Three
open scoped commutatorElement
variable {p : ℕ} [Fact p.Prime]

/-- In a prime field a transvection root group is cyclic; its full preimage
under any central extension is abelian. -/
theorem transvection_preimage_commute {E : Type*} [Group E]
    (f : E →* Sp (ZMod p)) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (v : Vector 2 (ZMod p))
    {x y : E} (hx : f x ∈ (parameterHom v).range)
    (hy : f y ∈ (parameterHom v).range) : Commute x y := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  obtain ⟨t, ht⟩ := hf (transvection v 1)
  have hpow (c : ZMod p) : f (t ^ c.val) = transvection v c := by
    rw [map_pow, ht, transvection_pow]
    congr 1
    simp [nsmul_eq_mul]
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [CentralExtension.commutator_eq_of_image_eq f hk
    (ha.symm.trans (hpow a.toAdd).symm) (hb.symm.trans (hpow b.toAdd).symm)]
  exact ((Commute.refl t).pow_pow _ _).commutator_eq

private theorem exists_scalar {F : Type*} [Field F] [Finite F] (hq : 3 < Nat.card F) :
    ∃ c : F, c ≠ 0 ∧ c ^ 2 ≠ 1 := by
  classical
  let := Fintype.ofFinite F
  have hcard : ({0, 1, -1} : Finset F).card < (Finset.univ : Finset F).card := by
    have h := Finset.card_le_three (a := (0 : F)) (b := 1) (c := -1)
    simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card] using lt_of_le_of_lt h hq
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  exact ⟨c, hc.1, fun h => (sq_eq_one_iff.mp h).elim hc.2.1 hc.2.2⟩

/-- Every additive transvection parametrization lifts through every central
extension of the actual symplectic group when the prime is greater than three. -/
theorem exists_transvection_lift (hp : 3 < p)
    {E : Type*} [Group E] (f : E →* Sp (ZMod p)) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (v : Vector 2 (ZMod p)) :
    ∃ u : Multiplicative (ZMod p) →* E, f.comp u = parameterHom v := by
  classical
  by_cases hv : v = 0
  · subst v
    exact ⟨1, by ext x; simp [parameterHom]⟩
  obtain ⟨c, hc, hc₂⟩ := exists_scalar (F := ZMod p) (by simpa using hp)
  obtain ⟨g, _, hg⟩ := exists_generated_send hv (smul_ne_zero hc hv)
  obtain ⟨a, ha⟩ := hf g
  choose b hb using fun x : ZMod p => hf (transvection v x)
  let d : ZMod p := c ^ 2 - 1
  have hd : d ≠ 0 := sub_ne_zero.mpr hc₂
  let s : ZMod p → E := fun x => ⁅a, b (d⁻¹ * x)⁆
  have hs (x : ZMod p) : f (s x) = transvection v x := by
    dsimp [s]
    rw [map_commutatorElement, commutatorElement_def, ha, hb, transvection_conjugate,
      hg, transvection_scale, transvection_inverse, ← transvection_add]
    congr 1
    calc
      c ^ 2 * (d⁻¹ * x) + -(d⁻¹ * x) = d * (d⁻¹ * x) := by dsimp [d]; ring
      _ = x := mul_inv_cancel_left₀ hd x
  have hs0 : s 0 = 1 := by
    dsimp [s]
    rw [mul_zero]
    have h0 : f (b 0) = f 1 := by rw [hb, transvection_zero, map_one]
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl h0]
    simp
  have hsadd (x y : ZMod p) : s (x + y) = s x * s y := by
    have hsum : f (b (d⁻¹ * (x + y))) = f (b (d⁻¹ * x) * b (d⁻¹ * y)) := by
      rw [map_mul, hb, hb, hb, ← transvection_add, mul_add]
    have hcomm : Commute (b (d⁻¹ * x)) (s y) :=
      transvection_preimage_commute f hf hk v
        ⟨.ofAdd _, (hb _).symm⟩ ⟨.ofAdd _, (hs _).symm⟩
    change ⁅a, b (d⁻¹ * (x + y))⁆ = _
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl hsum,
      commutatorElement_mul_right_eq_mul_conj]
    change s x * b (d⁻¹ * x) * s y * (b (d⁻¹ * x))⁻¹ = _
    rw [mul_assoc (s x), hcomm.eq, ← mul_assoc, mul_assoc (s x * s y),
      mul_inv_cancel, mul_one]
  exact ⟨{ toFun x := s x.toAdd
           map_one' := hs0
           map_mul' x y := hsadd x.toAdd y.toAdd }, MonoidHom.ext fun x => hs x.toAdd⟩

/-- The lifted additive transvection groups generate the full perfect central
cover. Relations between different directions are still a separate obligation. -/
theorem exists_generating_transvection_lifts (hp : 3 < p)
    {E : Type*} [Group E] (f : PerfectCentralCovering.Cover E (Sp (ZMod p))) :
    ∃ u : Vector 2 (ZMod p) → Multiplicative (ZMod p) →* E,
      (∀ v, f.toMonoidHom.comp (u v) = parameterHom v) ∧
      Subgroup.closure (Set.range (fun a : Vector 2 (ZMod p) × Multiplicative (ZMod p) =>
        u a.1 a.2)) = ⊤ := by
  choose u hu using fun v => exists_transvection_lift hp f.toMonoidHom
    f.surjective f.ker_le_center v
  refine ⟨u, hu, ?_⟩
  let R := Subgroup.closure (Set.range
    (fun a : Vector 2 (ZMod p) × Multiplicative (ZMod p) => u a.1 a.2))
  have hR : R.map f.toMonoidHom = ⊤ := by
    apply top_unique
    rw [← transvectionGroup_eq_top (n := 2) (F := ZMod p)]
    apply (Subgroup.closure_le _).mpr
    rintro t ⟨v, a, rfl⟩
    exact ⟨u v (.ofAdd a), Subgroup.subset_closure ⟨(v, .ofAdd a), rfl⟩,
      DFunLike.congr_fun (hu v) (.ofAdd a)⟩
  have hs : Function.Surjective (f.toMonoidHom.comp R.subtype) := by
    intro x
    have hx : x ∈ R.map f.toMonoidHom := by rw [hR]; trivial
    obtain ⟨y, hy, hyx⟩ := hx
    exact ⟨⟨y, hy⟩, hyx⟩
  let := f.isPerfect
  have ht := PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    f.toMonoidHom R.subtype hs f.ker_le_center
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := ht x
  exact y.property

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime
