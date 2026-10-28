module

public import Theory.Representation.HexacodeAction.Field

/-!
# The binary commutant of the even hexacode group

Every binary linear endomorphism commuting with the actual even hexacode
monomial action is multiplication by an element of the four-element field.
Consequently every commuting binary linear automorphism is one of the three
powers of the specific coordinate-kernel generator `hexZ`.

Commutation with `hexZ` first gives field linearity. In the oriented field
coordinates, `hexY` is diagonal with entries `1, omega, omega²`, so its fixed
space is the first coordinate axis. The element `hexX` cycles the three axes.
A commuting map is therefore scalar on all three basis vectors, with the same
scalar. Only calculations on the three coordinates and four-element field
use finite decision procedures, all checked by the kernel.

This is the concrete commutant calculation for the module in
Aschbacher–Smith, *The Classification of Quasithin Groups*, K.1.3,
printed p.453 (PDF p.464), used in the terminal argument on printed p.1155
(PDF p.1172). The source-group external action and its commutation hypothesis
are supplied separately by the Chapter 15 assembly.

The code and explicit elements are the existing ATLAS ports under
`Theory.AtlasPort.OtherSporadic.Codes`, authored by Gerald Höhn and ATLAS
contributors, released under the ATLAS Research and Attribution License 1.0
(`LICENSES/ATLAS.txt`). No port definitions or interfaces are changed here.
-/

public section

open Atlas.Codes
open scoped BigOperators

namespace Representation.Hexacode

private lemma action_X_coordinates (w : hexacode) :
    fieldCoordinates (action hexX w) =
      ![fieldCoordinates w 2, fieldCoordinates w 0, fieldCoordinates w 1] := by
  funext i
  change orientedLetter (firstThree i)
      (Monomial.act (hexLiftRaw 0 * hexLiftRaw 1) w.val (firstThree i)) = _
  have hp : ∀ i : Fin 3,
      (hexLiftRaw 0 * hexLiftRaw 1).perm.symm (firstThree i) =
        firstThree (![2, 0, 1] i) := by decide
  change orientedLetter (firstThree i)
      ((hexLiftRaw 0 * hexLiftRaw 1).localMap (firstThree i)
        (w.val ((hexLiftRaw 0 * hexLiftRaw 1).perm.symm (firstThree i)))) = _
  rw [hp]
  have hl : ∀ (i : Fin 3) (u : K),
      orientedLetter (firstThree i)
        ((hexLiftRaw 0 * hexLiftRaw 1).localMap (firstThree i) u) =
        orientedLetter (firstThree (![2, 0, 1] i)) u := by decide
  rw [hl]
  fin_cases i <;> rfl

private lemma action_Y_coordinates (w : hexacode) (i : Fin 3) :
    fieldCoordinates (action hexY w) i =
      (![1, omega, omega ^ 2] i) * fieldCoordinates w i := by
  change orientedLetter (firstThree i)
      (Monomial.act (hexLiftRaw 3 * hexLiftRaw 4) w.val (firstThree i)) = _
  have hp : ∀ i : Fin 3,
      (hexLiftRaw 3 * hexLiftRaw 4).perm.symm (firstThree i) = firstThree i := by decide
  change orientedLetter (firstThree i)
      ((hexLiftRaw 3 * hexLiftRaw 4).localMap (firstThree i)
        (w.val ((hexLiftRaw 3 * hexLiftRaw 4).perm.symm (firstThree i)))) = _
  rw [hp]
  have hl : ∀ (i : Fin 3) (u : K),
      orientedLetter (firstThree i)
        ((hexLiftRaw 3 * hexLiftRaw 4).localMap (firstThree i) u) =
        (![1, omega, omega ^ 2] i) * orientedLetter (firstThree i) u := by decide
  exact hl i _


private def rotate (v : Fin 3 → F) : Fin 3 → F := ![v 2, v 0, v 1]
private def diagonal (v : Fin 3 → F) : Fin 3 → F := fun i => ![1, omega, omega ^ 2] i * v i

private lemma rotate_smul (r : F) (v : Fin 3 → F) : rotate (r • v) = r • rotate v := by
  funext i
  fin_cases i <;> rfl

private lemma coordinate_commutant (f : (Fin 3 → F) →ₗ[F] (Fin 3 → F))
    (hx : ∀ v, f (rotate v) = rotate (f v))
    (hy : ∀ v, f (diagonal v) = diagonal (f v)) :
    ∃ r : F, ∀ v, f v = r • v := by
  let b : Fin 3 → (Fin 3 → F) := fun i => Pi.single i 1
  let r : F := f (b 0) 0
  have hd : diagonal (b 0) = b 0 := by decide
  have hh := hy (b 0)
  rw [hd] at hh
  have h0 : f (b 0) = r • b 0 := by
    have h1 := congrFun hh 1
    have h2 := congrFun hh 2
    have hz1 : ∀ u : F, u = omega * u → u = 0 := by decide
    have hz2 : ∀ u : F, u = omega ^ 2 * u → u = 0 := by decide
    have hu1 := hz1 _ h1
    have hu2 := hz2 _ h2
    funext i
    fin_cases i
    · simp [r, b]
    · simpa [b] using hu1
    · simpa [b] using hu2
  have hx0 : rotate (b 0) = b 1 := by decide
  have hx1 : rotate (b 1) = b 2 := by decide
  have h1 : f (b 1) = r • b 1 := by
    rw [← hx0, hx, h0, rotate_smul]
  have h2 : f (b 2) = r • b 2 := by
    rw [← hx1, hx, h1, rotate_smul]
  have hb (i : Fin 3) : f (b i) = r • b i := by
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  refine ⟨r, fun v => ?_⟩
  have hv : v = ∑ i, v i • b i := by
    funext j
    simp [b, Pi.smul_apply, Pi.single_apply, Finset.sum_apply]
  calc
    f v = ∑ i, v i • f (b i) := by conv_lhs => rw [hv]; rw [map_sum]; simp only [map_smul]
    _ = r • ∑ i, v i • b i := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hb]
      exact smul_comm _ _ _
    _ = r • v := by rw [← hv]


/-- The entire binary endomorphism commutant consists of field scalars. -/
theorem commuting_even_endomorphism_eq_smul
    (f : Atlas.Codes.hexacode →ₗ[ZMod 2] Atlas.Codes.hexacode)
    (hf : ∀ (g : Atlas.Codes.HexEvenAutomorphisms) w,
      f (action g.val w) = action g.val (f w)) :
    ∃ r : F, ∀ w, f w = r • w := by
  have hz (w : hexacode) : f (action hexZ w) = action hexZ (f w) := hf hexEvenZ w
  have hs (r : F) (w : hexacode) : f (r • w) = r • f w := by
    rw [field_smul_formula, map_add, map_smul, map_smul,
      hz, ← field_smul_formula]
  let ff : hexacode →ₗ[F] hexacode :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := hs }
  let c := fieldCoordinates.toLinearMap.comp (ff.comp fieldCoordinates.symm.toLinearMap)
  have hx (w : hexacode) :
      fieldCoordinates (action hexX w) = rotate (fieldCoordinates w) :=
    action_X_coordinates w
  have hy (w : hexacode) :
      fieldCoordinates (action hexY w) = diagonal (fieldCoordinates w) :=
    funext (action_Y_coordinates w)
  have hcx (v) : c (rotate v) = rotate (c v) := by
    obtain ⟨w, rfl⟩ := fieldCoordinates.surjective v
    change fieldCoordinates (f (fieldCoordinates.symm (rotate (fieldCoordinates w)))) =
      rotate (fieldCoordinates (f (fieldCoordinates.symm (fieldCoordinates w))))
    rw [← hx, fieldCoordinates.symm_apply_apply, fieldCoordinates.symm_apply_apply,
      hf ⟨hexX, hexX_even⟩, hx]
  have hcy (v) : c (diagonal v) = diagonal (c v) := by
    obtain ⟨w, rfl⟩ := fieldCoordinates.surjective v
    change fieldCoordinates (f (fieldCoordinates.symm (diagonal (fieldCoordinates w)))) =
      diagonal (fieldCoordinates (f (fieldCoordinates.symm (fieldCoordinates w))))
    rw [← hy, fieldCoordinates.symm_apply_apply, fieldCoordinates.symm_apply_apply,
      hf ⟨hexY, hexY_even⟩, hy]
  obtain ⟨r, hr⟩ := coordinate_commutant c hcx hcy
  refine ⟨r, fun w => ?_⟩
  apply fieldCoordinates.injective
  rw [fieldCoordinates.map_smul]
  have hw := hr (fieldCoordinates w)
  change fieldCoordinates (f (fieldCoordinates.symm (fieldCoordinates w))) =
    r • fieldCoordinates w at hw
  rwa [fieldCoordinates.symm_apply_apply] at hw


private lemma scalar_power_eq_smul (n : ℕ) (w : hexacode) :
    action (hexZ ^ n) w = omega ^ n • w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, map_mul]
    change action (hexZ ^ n) (action hexZ w) = _
    rw [ih, scalar_eq_omega_smul, smul_smul, pow_succ]

/-- A binary automorphism commuting with the even action is a power of the
actual coordinate-kernel generator. -/
theorem commuting_even_automorphism_eq_scalar
    (e : hexacode ≃ₗ[ZMod 2] hexacode)
    (he : ∀ (g : HexEvenAutomorphisms) w,
      e (action g.val w) = action g.val (e w)) :
    ∃ k : Fin 3, ∀ w, e w = action (hexZ ^ k.val) w := by
  obtain ⟨r, hr⟩ := commuting_even_endomorphism_eq_smul e.toLinearMap he
  have hn : r ≠ 0 := by
    intro h
    let w : hexacode := fieldCoordinates.symm (fun _ => 1)
    have hew : e w = e 0 := by
      change e.toLinearMap w = e.toLinearMap 0
      rw [hr, h, zero_smul, map_zero]
    have hh := congrArg (fun v : hexacode => fieldCoordinates v 0) (e.injective hew)
    simp [w] at hh
  have hpow : ∀ r : F, r ≠ 0 → ∃ k : Fin 3, r = omega ^ k.val := by decide
  obtain ⟨k, hk⟩ := hpow r hn
  refine ⟨k, fun w => ?_⟩
  rw [scalar_power_eq_smul, ← hk]
  exact hr w


/-- The three powers of `hexZ` are exactly the invertible binary commutant. -/
theorem commuting_even_automorphism_iff
    (e : hexacode ≃ₗ[ZMod 2] hexacode) :
    (∀ (g : HexEvenAutomorphisms) w,
      e (action g.val w) = action g.val (e w)) ↔
    ∃ k : Fin 3, ∀ w, e w = action (hexZ ^ k.val) w := by
  constructor
  · exact commuting_even_automorphism_eq_scalar e
  · rintro ⟨k, hk⟩ g w
    rw [hk, scalar_power_eq_smul, hk, scalar_power_eq_smul]
    exact (action_even_smul g.val g.property _ w).symm

end Representation.Hexacode
