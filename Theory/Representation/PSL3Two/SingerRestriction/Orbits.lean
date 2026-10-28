module

public import Theory.Representation.PSL3Two.SingerRestriction

/-!
# Stabilizers and cubic orbits in the Singer fixed plane

In the actual trace-zero endomorphism model of the binary Steinberg module,
commutation with the Singer matrix determines a matrix from three entries.
Trace zero leaves the published two-parameter fixed plane. Every nonzero
matrix in this plane has a power equal to the Singer matrix. Its stabilizer
therefore centralizes the Singer matrix and lies in the Singer subgroup.
Only the eight possible centralizer matrices require a finite certificate.

Sylow conjugacy transports the exact stabilizer to every subgroup of order
seven. An order-three subgroup normalizing it then acts freely on the three
nonzero fixed vectors, hence transitively.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma J.2.3(1),(3), printed pp.433–434 (PDF pp.444–445).
-/

public section
open Matrix Representation Representation.BinaryOffender
open scoped Matrix
open Matrix.PSL3Two.OuterInvolutionSinger
namespace BinaryLinearThree.SingerRestriction

private def centralMatrix (a b c : ZMod 2) : Mat :=
  !![c,a,b; a,a+b+c,a+b; b,a+b,a+c]

private lemma centralMatrix_of_commutes (A : Mat) (h : A * singer.val = singer.val * A) :
    A = centralMatrix (A 0 1) (A 0 2) (A 0 0) := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h02 := congrFun (congrFun h 0) 2
  have h11 := congrFun (congrFun h 1) 1
  have h12 := congrFun (congrFun h 1) 2
  have h20 := congrFun (congrFun h 2) 0
  norm_num [singer, Matrix.mul_apply, Fin.sum_univ_three] at h00 h01 h02 h11 h12 h20
  change A 0 2 * 1 = 1 * A 2 0 at h00
  change A 0 1 + A 0 2 * 1 = 1 * A 2 1 at h01
  change A 0 0 * 1 + A 0 1 * 1 + A 0 2 * 0 = 1 * A 2 2 at h02
  change A 1 2 * 1 = 1 * A 2 1 at h11
  change A 1 0 * 1 + A 1 1 * 1 + A 1 2 * 0 = A 1 2 + 1 * A 2 2 at h12
  change A 2 2 * 1 = 1 * A 0 0 + 1 * A 1 0 + 0 * A 2 0 at h20
  simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero] at h00 h01 h02 h11 h12 h20
  ext i j
  fin_cases i <;> fin_cases j <;> simp [centralMatrix]
  · linear_combination -h02 - h20
  · linear_combination h12 + h11 - h01 + h20
  · linear_combination h11 - h01
  · exact h00.symm
  · exact h01.symm
  · simpa [add_comm] using h02.symm

private lemma central_cert : ∀ a b c : ZMod 2, (centralMatrix a b c).det = 1 →
    ∃ i : Fin 7, centralMatrix a b c = singer.val ^ (i : ℕ) := by decide +kernel

private lemma power_cert : ∀ a b : ZMod 2, (a ≠ 0 ∨ b ≠ 0) →
    ∃ i : Fin 7, fixedMatrix a b ^ (i : ℕ) = singer.val := by decide +kernel

private lemma trace_cert : ∀ a b c : ZMod 2, (centralMatrix a b c).trace = 0 → c = b := by decide

private lemma matrix_commutes_of_fixed (g : Group) (v : Steinberg) (hv : S g v = v) :
    g.val * LinearMap.toMatrix' v.val = LinearMap.toMatrix' v.val * g.val := by
  have he : g.val * (LinearMap.toMatrix' v.val * (g⁻¹).val) =
      LinearMap.toMatrix' v.val := by
    apply Matrix.toLin'.injective
    have hval := congrArg Subtype.val hv
    change Matrix.toLin' g.val ∘ₗ (v.val ∘ₗ Matrix.toLin' (g⁻¹).val) = v.val at hval
    simpa only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', LinearMap.comp_assoc] using hval
  have hi : (g⁻¹).val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
  have hh := congrArg (fun A : Mat => A * g.val) he
  simpa only [mul_assoc, hi, mul_one] using hh

private lemma fixed_eq (v : Steinberg) (hv : S singer v = v) :
    ∃ a b : ZMod 2, v = fixedVector a b := by
  let A := LinearMap.toMatrix' v.val
  have ha := centralMatrix_of_commutes A (matrix_commutes_of_fixed singer v hv).symm
  have ht : A.trace = 0 := by
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
    exact v.property
  rw [ha] at ht
  have hc := trace_cert _ _ _ ht
  refine ⟨A 0 1, A 0 2, ?_⟩
  apply Subtype.ext
  have hm : A = fixedMatrix (A 0 1) (A 0 2) := by
    rw [ha, hc]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [centralMatrix, fixedMatrix, CharTwo.add_self_eq_zero, add_comm, add_left_comm]
  exact (Matrix.toLin'_toMatrix' v.val).symm.trans (congrArg Matrix.toLin' hm)

private lemma fixedVector_zero : fixedVector 0 0 = 0 := by
  apply Subtype.ext
  have hh : fixedMatrix 0 0 = 0 := by decide
  change (fixedMatrix 0 0).toLin' = 0
  rw [hh, map_zero]

private lemma stabilizer_singer (v : Steinberg) (hv : v ∈ fixedSpace S (Subgroup.zpowers singer))
    (hv0 : v ≠ 0) (g : Group) : S g v = v ↔ g ∈ Subgroup.zpowers singer := by
  constructor
  · intro hg
    obtain ⟨a, b, rfl⟩ := fixed_eq v ((mem_fixedSpace_zpowers_iff S singer v).mp hv)
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra! h
      exact hv0 (h.1 ▸ h.2 ▸ fixedVector_zero)
    obtain ⟨i, hi⟩ := power_cert a b hab
    have hc : Commute g.val (fixedMatrix a b) := by
      change g.val * fixedMatrix a b = fixedMatrix a b * g.val
      simpa only [fixedVector, LinearMap.toMatrix'_toLin'] using matrix_commutes_of_fixed g _ hg
    have hcs := hc.pow_right (i : ℕ)
    rw [hi] at hcs
    have he := centralMatrix_of_commutes g.val hcs.eq
    have hd : (centralMatrix (g.val 0 1) (g.val 0 2) (g.val 0 0)).det = 1 :=
      he ▸ g.property
    obtain ⟨j, hj⟩ := central_cert _ _ _ hd
    have hg' : g = singer ^ (j : ℕ) := Subtype.ext (he.trans hj)
    rw [hg']
    exact (Subgroup.zpowers singer).pow_mem (Subgroup.mem_zpowers singer) _
  · exact fun hg => hv ⟨g, hg⟩

/-- The stabilizer of every nonzero order-seven fixed vector is exactly that
order-seven subgroup, for the actual Steinberg representation. -/
theorem stabilizer_order_seven (H : Subgroup Group) (hH : Nat.card H = 7)
    (v : Steinberg) (hv : v ∈ fixedSpace S H) (hv0 : v ≠ 0) (g : Group) :
    S g v = v ↔ g ∈ H := by
  constructor
  · intro hg
    obtain ⟨t, ht⟩ := exists_conjugate_singer H hH
    have hv' : S t⁻¹ v ∈ fixedSpace S (Subgroup.zpowers singer) := by
      intro k
      have hk : t * (k : Group) * t⁻¹ ∈ H := ht ▸ Subgroup.mem_map.mpr ⟨k,k.property,rfl⟩
      have hf : S (t * (k : Group) * t⁻¹) v = v := hv ⟨_,hk⟩
      have he := congrArg (S t⁻¹) hf
      change S k.val (S t⁻¹ v) = S t⁻¹ v
      simpa only [map_mul, Module.End.mul_apply, Representation.inv_self_apply] using he
    have hv0' : S t⁻¹ v ≠ 0 := by
      intro h
      exact hv0 ((S.apply_bijective t⁻¹).injective (h.trans (map_zero _).symm))
    have hfix : S (t⁻¹ * g * t) (S t⁻¹ v) = S t⁻¹ v := by
      simp only [map_mul, Module.End.mul_apply, Representation.self_inv_apply, hg]
    have hmem := (stabilizer_singer _ hv' hv0' _).mp hfix
    rw [← ht]
    refine Subgroup.mem_map.mpr ⟨t⁻¹ * g * t, hmem, ?_⟩
    change t * (t⁻¹ * g * t) * t⁻¹ = g
    group
  · exact fun hg => hv ⟨g, hg⟩

/-- Every normalizing order-three subgroup is transitive on the nonzero
vectors of the order-seven Steinberg fixed plane. -/
theorem transitive_order_three (H D : Subgroup Group) (hH : Nat.card H = 7)
    (hD : Nat.card D = 3) (hDH : D ≤ Subgroup.normalizer H)
    (u v : Steinberg) (hu : u ∈ fixedSpace S H) (hv : v ∈ fixedSpace S H)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) : ∃ g ∈ D, S g u = v := by
  classical
  let F := fixedSpace S H
  let P := {w : F // w ≠ 0}
  have hF : Nat.card F = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      finrank_fixedSpace_order_seven H hH]
    norm_num
  let _ : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; decide)
  have hstable (g : D) : S g.val u ∈ F := by
    intro k
    have hk : g.val⁻¹ * (k : Group) * g.val ∈ H := by
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (H : Set Group)).inv_mem (hDH g.property)) k.val).mp k.property
    have hf : S (g.val⁻¹ * (k : Group) * g.val) u = u := hu ⟨_,hk⟩
    have he := congrArg (S g.val) hf
    change S k.val (S g.val u) = S g.val u
    simpa only [map_mul, Module.End.mul_apply, Representation.self_inv_apply] using he
  let f : D → P := fun g => ⟨⟨S g.val u, hstable g⟩, by
    intro h
    have he := congrArg Subtype.val h
    exact hu0 ((S.apply_bijective g.val).injective (he.trans (map_zero _).symm))⟩
  have hinj : Function.Injective f := by
    intro x y h
    have he : S x.val u = S y.val u := congrArg (fun z : P => z.val.val) h
    have hfix : S (y.val⁻¹ * x.val) u = u := by
      simpa only [map_mul, Module.End.mul_apply, Representation.inv_self_apply] using
        congrArg (S y.val⁻¹) he
    have hm := (stabilizer_order_seven H hH u hu hu0 _).mp hfix
    have hd : Disjoint D H := Subgroup.disjoint_of_coprime_natCard (by rw [hD,hH]; decide)
    apply Subtype.ext
    exact (inv_mul_eq_one.mp (hd.le_bot ⟨D.mul_mem (D.inv_mem y.property) x.property,hm⟩)).symm
  have hcard : Nat.card P = 3 := by
    let _ : Fintype F := Fintype.ofFinite F
    simpa [P, Nat.card_eq_fintype_card, Fintype.card_subtype_compl] using
      congrArg (fun n : ℕ => n - 1) hF
  have hs := (Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hD.trans hcard.symm⟩
  obtain ⟨g, hg⟩ := hs.2 ⟨⟨v,hv⟩, fun h => hv0 (congrArg Subtype.val h)⟩
  exact ⟨g,g.property, congrArg (fun z : P => z.val.val) hg⟩
end BinaryLinearThree.SingerRestriction
