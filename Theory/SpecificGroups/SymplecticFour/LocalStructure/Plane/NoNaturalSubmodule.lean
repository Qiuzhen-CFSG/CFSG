module
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.Commutator
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.CentralModule
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Action

/-!
# No natural submodule in the symplectic plane radical

For a finite field of order greater than two, every normal subgroup of the
actual plane-local radical is central or is the whole radical. The natural
central quotient is transitive on nonzero vectors. A noncentral normal
subgroup therefore supplements the central kernel; commutator generation
then makes that subgroup the entire radical. The nonzero central kernel
excludes a natural submodule.

The final theorem accepts a surjective natural quotient and its original
conjugation action. It proves that its image in the plane radical vanishes,
without assuming linearity over the larger field or injectivity of that image.
This is the terminal local calculation in Aschbacher--Smith 9.3, printed
pp.734--735, after the Sp₄ block recognition of9.3.10.
-/

public section

open Matrix Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour.Plane
noncomputable section
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

private theorem naturalCoordinates_conjugate (g : planeLocal (F := F))
    (q : radical (F := F)) :
    naturalCoordinates (conjugate g q) =
      Multiplicative.ofAdd ((quotientMap g).val *ᵥ (naturalCoordinates q).toAdd) :=
  centralQuotientEquiv_conjugate g q

private theorem radical_central_supplement (W : Subgroup (planeLocal (F := F)))
    [W.Normal] (hW : W ≤ radical) (hnc : ¬W ≤ center (planeLocal (F := F)))
    (r : radical (F := F)) :
    ∃ c ∈ W, ∃ z ∈ center (planeLocal (F := F)), r.val = c * z := by
  obtain ⟨w, hw, hncw⟩ := Set.not_subset.mp hnc
  let wR : radical (F := F) := ⟨w, hW hw⟩
  have hw0 : (naturalCoordinates wR).toAdd ≠ 0 := by
    intro hz
    apply hncw
    change wR ∈ (center (planeLocal (F := F))).subgroupOf radical
    rw [← naturalCoordinates_ker, MonoidHom.mem_ker]
    exact Multiplicative.toAdd.injective hz
  by_cases hr0 : (naturalCoordinates r).toAdd = 0
  · refine ⟨1, W.one_mem, r.val, ?_, (one_mul _).symm⟩
    change r ∈ (center (planeLocal (F := F))).subgroupOf radical
    rw [← naturalCoordinates_ker, MonoidHom.mem_ker]
    exact Multiplicative.toAdd.injective hr0
  obtain ⟨A, hA⟩ := natural_transitive hw0 hr0
  let c := conjugate (levi A) wR
  have hcW : c.val ∈ W := (inferInstance : W.Normal).conj_mem w hw (levi A)
  have hcoord : naturalCoordinates c = naturalCoordinates r := by
    apply Multiplicative.toAdd.injective
    rw [naturalCoordinates_conjugate]
    exact hA
  have hz : (c⁻¹ * r).val ∈ center (planeLocal (F := F)) := by
    change c⁻¹ * r ∈ (center (planeLocal (F := F))).subgroupOf radical
    rw [← naturalCoordinates_ker, MonoidHom.mem_ker, map_mul, map_inv, hcoord,
      inv_mul_cancel]
  exact ⟨c.val, hcW, (c⁻¹ * r).val, hz, by simp⟩

/-- Every proper invariant subgroup of the plane radical is central. -/
theorem normal_radical_le_center_or_eq {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
    (W : Subgroup (planeLocal (F := F))) [W.Normal] (hW : W ≤ radical) :
    W ≤ center (planeLocal (F := F)) ∨ W = radical := by
  by_cases hc : W ≤ center (planeLocal (F := F))
  · exact Or.inl hc
  right
  apply le_antisymm hW
  rw [← radical_commutator_eq hcard hn]
  apply commutator_le.mpr
  intro r hr g _
  obtain ⟨c, hcW, z, hz, hrz⟩ := radical_central_supplement W hW hc ⟨r, hr⟩
  have hzg : ⁅z, g⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    ((mem_center_iff.mp hz) g).symm
  change r = c * z at hrz
  rw [hrz, commutatorElement_mul_left_eq_conj_mul, hzg]
  simpa only [mul_one, mul_inv_cancel, one_mul] using
    (commutator_le_left W ⊤ (commutator_mem_commutator hcW (mem_top g)))

omit [Finite F] in
/-- The off-diagonal alternating shear gives a nonzero central radical element. -/
theorem radical_inf_center_ne_bot :
    radical (F := F) ⊓ center (planeLocal (F := F)) ≠ ⊥ := by
  let B : symmetricMatrices F := ⟨!![0, 1; 1, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl⟩
  let q : radical (F := F) := radicalEquiv.symm (Multiplicative.ofAdd B)
  have hqc : q.val ∈ center (planeLocal (F := F)) := by
    change q ∈ (center (planeLocal (F := F))).subgroupOf radical
    rw [mem_center_subgroupOf_iff_alternating]
    exact ⟨1, by simp [q, B]⟩
  intro he
  have hq : q = 1 := Subtype.ext (show q.val = 1 from
    (mem_bot.mp (he ▸ (show q.val ∈ radical ⊓ center _ from ⟨q.property, hqc⟩))))
  have hb := congrArg (fun x : radical (F := F) => (radicalEquiv x).toAdd.val 0 1) hq
  simp [q, B] at hb

/-- A normal subgroup of the radical disjoint from the local center vanishes. -/
theorem normal_radical_eq_bot_of_disjoint_center {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
    (W : Subgroup (planeLocal (F := F))) [W.Normal] (hW : W ≤ radical)
    (hd : Disjoint W (center (planeLocal (F := F)))) : W = ⊥ := by
  rcases normal_radical_le_center_or_eq hcard hn W hW with hc | rfl
  · exact le_bot_iff.mp (le_inf le_rfl hc |>.trans hd.le_bot)
  · exact (radical_inf_center_ne_bot (F := F) hd.eq_bot).elim

omit [CharP F 2] [Finite F] in
private theorem natural_fixed_zero (v : Fin 2 → F)
    (h : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F, A.val *ᵥ v = v) : v = 0 := by
  let U : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp⟩
  let D : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; 1, 1], by simp⟩
  have h1 := congrFun (h U) 0
  have h0 := congrFun (h D) 1
  have hv1 : v 1 = 0 := by simpa [U, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h1
  have hv0 : v 0 = 0 := by simpa [D, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
  ext i
  fin_cases i <;> assumption

/-- Every equivariant homomorphism from the natural module into the radical is zero. -/
theorem natural_hom_into_radical_eq_one {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
    (f : Multiplicative (Fin 2 → F) →* planeLocal (F := F))
    (hR : f.range ≤ radical)
    (he : ∀ (g : planeLocal (F := F)) (v : Multiplicative (Fin 2 → F)),
      f (Multiplicative.ofAdd ((quotientMap g).val *ᵥ v.toAdd)) = g * f v * g⁻¹) :
    f = 1 := by
  by_contra hf0
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro v hv
    change v = 1
    by_contra hv1
    have hv0 : v.toAdd ≠ 0 := fun h => hv1 (Multiplicative.toAdd.injective h)
    apply hf0
    apply MonoidHom.ext
    intro x
    by_cases hx : x = 1
    · simp [hx]
    obtain ⟨A, hA⟩ := natural_transitive hv0
      (show x.toAdd ≠ 0 from fun h => hx (Multiplicative.toAdd.injective h))
    have hh := he (levi A) v
    rw [quotientMap_levi, hA, MonoidHom.mem_ker.mp hv] at hh
    simpa using hh
  have : f.range.Normal := ⟨by
    rintro x ⟨v, rfl⟩ g
    exact ⟨_, he g v⟩⟩
  have hd : Disjoint f.range (center (planeLocal (F := F))) := by
    rw [disjoint_iff_inf_le]
    rintro x ⟨⟨v, rfl⟩, hc⟩
    have hv : v.toAdd = 0 := natural_fixed_zero _ (by
      intro A
      have hh := he (levi A) v
      rw [(mem_center_iff.mp hc) (levi A), mul_assoc, mul_inv_cancel, mul_one] at hh
      exact congrArg Multiplicative.toAdd (hf hh))
    have hv1 : v = 1 := Multiplicative.toAdd.injective hv
    simp [hv1]
  have hr := normal_radical_eq_bot_of_disjoint_center hcard hn f.range hR hd
  apply hf0
  apply MonoidHom.ext
  intro v
  exact mem_bot.mp (hr ▸ (show f v ∈ f.range from ⟨v, rfl⟩))

/-- A natural quotient cannot give a nonzero image in the actual plane radical. -/
theorem le_ker_of_natural_quotient {H : Type*} [Group H] {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
    (V : Subgroup H) [V.Normal]
    (q : H →* planeLocal (F := F)) (hq : Function.Surjective q)
    (p : V →* Multiplicative (Fin 2 → F)) (hp : Function.Surjective p)
    (hker : p.ker ≤ (q.comp V.subtype).ker)
    (hR : V.map q ≤ radical)
    (he : ∀ (g : H) (v : V), p (MulAut.conjNormal g v) =
      Multiplicative.ofAdd ((quotientMap (q g)).val *ᵥ (p v).toAdd)) :
    V ≤ q.ker := by
  let f := p.liftOfSurjective hp ⟨q.comp V.subtype, hker⟩
  have hf (v : V) : f (p v) = q v := by simp [f]
  have hFR : f.range ≤ radical := by
    rintro x ⟨y, rfl⟩
    obtain ⟨v, rfl⟩ := hp y
    rw [hf]
    exact hR ⟨v, v.property, rfl⟩
  have hFE (g : planeLocal (F := F)) (v : Multiplicative (Fin 2 → F)) :
      f (Multiplicative.ofAdd ((quotientMap g).val *ᵥ v.toAdd)) = g * f v * g⁻¹ := by
    obtain ⟨a, rfl⟩ := hq g
    obtain ⟨b, rfl⟩ := hp v
    rw [← he, hf, hf]
    change q (a * b.val * a⁻¹) = _
    simp only [map_mul, map_inv]
  have hF := natural_hom_into_radical_eq_one hcard hn f hFR hFE
  intro v hv
  change q v = 1
  rw [← hf ⟨v, hv⟩, hF]
  rfl
end
end Theory.SpecificGroups.SymplecticFour.Plane
