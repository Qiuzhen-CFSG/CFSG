module

public import Theory.Mathieu.M11.Properties.InvolutionClasses
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import Theory.Mathieu.M11.Properties.SylowTwo
public import Theory.GroupTheory.TwoRankFourthPower
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Three involutions generate M11 and its odd central covers

An explicit word c in the native ATLAS generators is an involution and cB is
another involution. Thus A, c, cB generate M11. The unique involution class
makes these three conjugates of any prescribed involution. Surjectivity onto
the simple central quotient lifts this generation to a perfect cover with
no central involution.

The native semidihedral Sylow subgroup also gives automorphism two-rank at
most two, using the proved innerness of every M11 automorphism. Together
these facts give the degree-six upper bound for an FF binary normalizer.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.1.13, printed pp.73–74. Generator provenance is retained in
`Theory.Mathieu.M11.Generators`; the short word here is checked against those
literal permutations, without an external finite-group certificate.
-/

public section
open Theory.GroupTheory
open Subgroup
namespace Sporadic.Mathieu
private noncomputable abbrev a : M11 := m11GeneratorAInM11
private noncomputable abbrev b : M11 := m11GeneratorBInM11
private noncomputable def c : M11 :=
  a * b ^ 3 * a * b ^ 3 * a * b * a * b ^ 2 * a * b ^ 2 * a * b ^ 3 * a * b * a * b * a

private def cPerm : Equiv.Perm (Fin 11) :=
  Equiv.swap 0 10 * Equiv.swap 2 9 * Equiv.swap 4 8 * Equiv.swap 5 6

set_option maxRecDepth 4096 in
private theorem c_coe : (c : Equiv.Perm (Fin 11)) = cPerm := by
  ext i
  fin_cases i <;> rfl

private theorem c_sq : c ^ 2 = 1 := by
  apply Subtype.ext
  change (c : Equiv.Perm (Fin 11)) ^ 2 = 1
  rw [c_coe]
  ext i
  fin_cases i <;> rfl

private theorem cb_sq : (c * b) ^ 2 = 1 := by
  apply Subtype.ext
  change ((c : Equiv.Perm (Fin 11)) * m11GeneratorB) ^ 2 = 1
  rw [c_coe]
  ext i
  fin_cases i <;> rfl

private theorem c_ne : c ≠ 1 := by
  intro h
  have hh := congrArg (fun x : M11 => (x : Equiv.Perm (Fin 11)) 0) h
  rw [c_coe] at hh
  exact (by decide : cPerm 0 ≠ (0 : Fin 11)) hh

set_option maxRecDepth 4096 in
private theorem cb_ne : c * b ≠ 1 := by
  intro h
  have hh := congrArg (fun x : M11 => (x : Equiv.Perm (Fin 11)) 0) h
  change (c : Equiv.Perm (Fin 11)) (m11GeneratorB 0) = 0 at hh
  rw [c_coe] at hh
  exact (by decide : cPerm (m11GeneratorB 0) ≠ (0 : Fin 11)) hh

private theorem three_generate : zpowers a ⊔ zpowers c ⊔ zpowers (c * b) = ⊤ := by
  apply top_unique
  rw [← m11_generators_closure_eq_top, closure_le]
  intro x hx
  rcases hx with (rfl | rfl)
  · exact (show zpowers a ≤ zpowers a ⊔ zpowers c ⊔ zpowers (c * b) from le_sup_of_le_left le_sup_left) (mem_zpowers _)
  · change b ∈ zpowers a ⊔ zpowers c ⊔ zpowers (c * b)
    have hc : c ∈ zpowers a ⊔ zpowers c ⊔ zpowers (c * b) :=
      (show zpowers c ≤ zpowers a ⊔ zpowers c ⊔ zpowers (c * b) from le_sup_of_le_left le_sup_right) (mem_zpowers _)
    have hcb : c * b ∈ zpowers a ⊔ zpowers c ⊔ zpowers (c * b) :=
      (show zpowers (c * b) ≤ zpowers a ⊔ zpowers c ⊔ zpowers (c * b) from le_sup_right) (mem_zpowers _)
    simpa only [inv_mul_cancel_left, b] using
      (zpowers a ⊔ zpowers c ⊔ zpowers (c * b)).mul_mem
        ((zpowers a ⊔ zpowers c ⊔ zpowers (c * b)).inv_mem hc) hcb

/-- Three conjugates of any involution generate the actual Witt-design M11. -/
theorem m11_three_involution_conjugates (t : M11) (ht : orderOf t = 2) :
    ∃ g h : M11, zpowers t ⊔ zpowers (g * t * g⁻¹) ⊔ zpowers (h * t * h⁻¹) = ⊤ := by
  obtain ⟨u, hu⟩ := isConj_iff.mp (m11_involution_isConj_generatorA t ht)
  obtain ⟨v, hv⟩ := isConj_iff.mp (m11_involution_isConj_generatorA c
    (orderOf_eq_prime c_sq c_ne))
  obtain ⟨w, hw⟩ := isConj_iff.mp (m11_involution_isConj_generatorA (c * b)
    (orderOf_eq_prime cb_sq cb_ne))
  change u * t * u⁻¹ = a at hu
  change v * c * v⁻¹ = a at hv
  change w * (c * b) * w⁻¹ = a at hw
  refine ⟨u⁻¹ * v⁻¹ * u, u⁻¹ * w⁻¹ * u, ?_⟩
  have he := congrArg (fun H : Subgroup M11 => H.map (MulAut.conj u⁻¹).toMonoidHom)
    three_generate
  rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers, map_top_of_surjective _ (MulAut.conj u⁻¹).surjective] at he
  have ha : u⁻¹ * a * u = t := by rw [← hu]; group
  have hc : u⁻¹ * c * u = (u⁻¹ * v⁻¹ * u) * t * (u⁻¹ * v⁻¹ * u)⁻¹ := by
    have hc0 : c = v⁻¹ * a * v := by rw [← hv]; group
    rw [hc0, ← hu]; group
  have hd : u⁻¹ * (c * b) * u = (u⁻¹ * w⁻¹ * u) * t * (u⁻¹ * w⁻¹ * u)⁻¹ := by
    have hd0 : c * b = w⁻¹ * a * w := by rw [← hw]; group
    rw [hd0, ← hu]; group
  simpa only [MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv, ha, hc, hd] using he

/-- Three involutions generate any perfect central cover of M11 with no
central involution. In particular this applies to a faithful binary irreducible image. -/
theorem m11_cover_three_involution_conjugates {E : Type*} [Group E]
    [Group.IsPerfect E] (e : E ⧸ center E ≃* M11)
    (hZ : ∀ z : E, z ∈ center E → z ^ 2 = 1 → z = 1)
    (t : E) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ g h : E, zpowers t ⊔ zpowers (g * t * g⁻¹) ⊔ zpowers (h * t * h⁻¹) = ⊤ := by
  let f : E →* M11 := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center E := by
    ext x
    change e (QuotientGroup.mk' (center E) x) = 1 ↔ x ∈ center E
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hft : f t ≠ 1 := by
    intro h
    apply ht
    exact hZ t (hk ▸ h) ht2
  obtain ⟨g, h, hgen⟩ := m11_three_involution_conjugates (f t)
    (orderOf_eq_prime (by rw [← map_pow, ht2, map_one]) hft)
  obtain ⟨g', rfl⟩ := hf g
  obtain ⟨h', rfl⟩ := hf h
  refine ⟨g', h', ?_⟩
  let D := zpowers t ⊔ zpowers (g' * t * g'⁻¹) ⊔ zpowers (h' * t * h'⁻¹)
  have hD : D.map f = ⊤ := by
    simpa only [D, Subgroup.map_sup, MonoidHom.map_zpowers, map_mul, map_inv] using hgen
  have hsurj : Function.Surjective (f.comp D.subtype) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
    exact hD
  have hs := PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    f D.subtype hsurj hk.le
  simpa only [Subgroup.range_subtype] using MonoidHom.range_eq_top.mpr hs

/-- Every elementary abelian two-subgroup of the actual automorphism group
of M11 has rank at most two. -/
theorem m11_automorphism_twoRank_le_two : primeRank 2 (MulAut M11) ≤ 2 := by
  let e : M11 ≃* MulAut M11 := MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot m11_center_eq_bot,
      fun f => m11_automorphism_inner f⟩
  rw [← primeRank_equiv 2 e]
  obtain ⟨P, a, _, ha, _, _, _⟩ := m11_exists_semidihedral_sylow
  rw [P.primeRank_eq]
  have hcard : Nat.card P = 2 ^ (2 + 2) := by
    rw [P.card_eq_multiplicity, m11_order]
    decide +kernel
  have hx : a ^ 4 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [ha] at hd
    norm_num at hd
  exact twoRank_le_of_card_pow_and_fourth_ne 2 hcard a hx

end Sporadic.Mathieu
