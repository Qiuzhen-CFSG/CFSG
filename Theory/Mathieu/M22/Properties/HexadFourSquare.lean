module

public import Theory.Mathieu.M22.Properties.HexadFourSquare.Basic
public import Theory.Mathieu.M22.Properties.HexadSplitCoordinates
public import Theory.Mathieu.M22.Properties.HexadFourSquare.Certificate

/-!
# Native commuting squares for the actual M22 hexad sections

A certified square-root pair in the stabilizer of the standard hexad fixing
point zero transports to every hexad and every complementary point. Hexad
transitivity supplies the first conjugator; the regular action of the
pointwise hexad kernel supplies the required adjustment of the point.

The quotient is injective on a complementary-point stabilizer. Thus the
transported involutions are exactly the images under the existing section
`m22HexadPointSection`, with its literal six-point marking. Changing the actor
marking also gives the identity for the published `m22HexadSection` carrying
the natural-module coordinates. No complement-classification premise is used.

This supplies the native commuting-square input to the separate quartic-cover
splitting reduction for Aschbacher--Smith I.2.2(6), printed p.412 / PDF p.423.
The statement concerns point-defined sections; it does not classify all
complements of the hexad kernel.
-/

public section
open scoped Pointwise
namespace Sporadic.Mathieu.M22HexadFourSquare

private theorem pointSection_recovers {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    {p : Fin 22} (hp : p ∉ B) (g : MulAction.stabilizer M22 B)
    (hg : g.val • p = p) :
    m22HexadPointSection hB hp (m22HexadSixMap hB g) = g := by
  let E := MulEquiv.ofBijective _ (m22HexadSixMap_pointStabilizer_bijective hB hp)
  exact congrArg Subtype.val (E.symm_apply_apply ⟨g, hg⟩)

private theorem pointSection_hasSquare_of_pair {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) {p : Fin 22} (hp : p ∉ B)
    (s t : MulAction.stabilizer M22 B)
    (hs2 : s ^ 2 = 1) (ht2 : t ^ 2 = 1)
    (hs1 : s ≠ 1) (ht1 : t ≠ 1) (hst : s * t ≠ 1)
    (hsp : s.val • p = p) (htp : t.val • p = p)
    (r : M22) (hr : r ^ 2 = s.val) (hrt : Commute r t.val) :
    HasSquare (m22HexadPointSection hB hp) := by
  let q := m22HexadSixMap hB
  let j := m22HexadPointSection hB hp
  have hs : j (q s) = s := pointSection_recovers hB hp s hsp
  have ht : j (q t) = t := pointSection_recovers hB hp t htp
  refine ⟨q s, q t, ?_, ?_, ?_, ?_, ?_, r, ?_, ?_⟩
  · rw [← map_pow, hs2, map_one]
  · rw [← map_pow, ht2, map_one]
  · intro h
    apply hs1
    rw [← hs, h, map_one]
  · intro h
    apply ht1
    rw [← ht, h, map_one]
  · intro h
    apply hst
    rw [← hs, ← ht, ← map_mul, h, map_one]
  · exact hr.trans (congrArg Subtype.val hs).symm
  · exact (congrArg Subtype.val ht).symm ▸ hrt

private theorem exists_flag_conjugator {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) {p : Fin 22} (hp : p ∉ B) :
    ∃ g : M22, g • m22Hexad123 = B ∧ g • (0 : Fin 22) = p := by
  obtain ⟨g, hg⟩ := exists_smul_m22Hexad123_eq hB
  have h0 : g • (0 : Fin 22) ∉ B := by
    rw [← hg]
    simpa using (show (0 : Fin 22) ∉ m22Hexad123 by decide +kernel)
  obtain ⟨u, hu⟩ := (m22HexadKernel_regular hB h0).surjective ⟨p, hp⟩
  refine ⟨u.val.val * g, ?_, ?_⟩
  · rw [mul_smul, hg]
    exact u.val.property
  · rw [mul_smul]
    exact congrArg Subtype.val hu

private theorem pointSection_hasSquare_of_base_pair {B : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) {p : Fin 22} (hp : p ∉ B)
    (s t : MulAction.stabilizer M22 m22Hexad123)
    (hs2 : s ^ 2 = 1) (ht2 : t ^ 2 = 1)
    (hs1 : s ≠ 1) (ht1 : t ≠ 1) (hst : s * t ≠ 1)
    (hs0 : s.val • (0 : Fin 22) = 0) (ht0 : t.val • (0 : Fin 22) = 0)
    (r : M22) (hr : r ^ 2 = s.val) (hrt : Commute r t.val) :
    HasSquare (m22HexadPointSection hB hp) := by
  obtain ⟨g, hg, hgp⟩ := exists_flag_conjugator hB hp
  let E := MulAction.stabilizerEquivStabilizer hg.symm
  have hE (a : MulAction.stabilizer M22 m22Hexad123) :
      (E a).val = MulAut.conj g a.val := MulAction.stabilizerEquivStabilizer_apply hg.symm a
  have hfix (a : MulAction.stabilizer M22 m22Hexad123)
      (ha : a.val • (0 : Fin 22) = 0) : (E a).val • p = p := by
    rw [hE, ← hgp]
    change (g * a.val * g⁻¹) • (g • (0 : Fin 22)) = g • (0 : Fin 22)
    simp only [mul_smul, inv_smul_smul, ha]
  apply pointSection_hasSquare_of_pair hB hp (E s) (E t)
    (by rw [← map_pow, hs2, map_one]) (by rw [← map_pow, ht2, map_one])
    (by simpa using hs1) (by simpa using ht1) ?_ (hfix s hs0) (hfix t ht0)
    (MulAut.conj g r) ?_ ?_
  · intro h
    apply hst
    apply E.injective
    simpa only [map_mul, map_one] using h
  · rw [← map_pow, hr, hE]
  · rw [hE]
    exact hrt.map (MulAut.conj g)

/-- Every section obtained by fixing a complementary point has the native
commuting square, with its original six-point marking. -/
theorem pointSection_hasSquare {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    {p : Fin 22} (hp : p ∉ B) : HasSquare (m22HexadPointSection hB hp) :=
  pointSection_hasSquare_of_base_pair hB hp
    Certificate.firstInHexad Certificate.secondInHexad
    Certificate.first_square Certificate.second_square
    Certificate.first_ne_one Certificate.second_ne_one Certificate.product_ne_one
    Certificate.first_fixes Certificate.second_fixes
    Certificate.root Certificate.root_square Certificate.root_commutes

/-- The existing naturally marked native section has the same commuting square. -/
theorem section_hasSquare {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    HasSquare (m22HexadSection hB) :=
  (pointSection_hasSquare hB
    (Classical.choose_spec (exists_m22Hexad_complementary_point hB))).comp_mulEquiv
      (m22HexadMarking hB)

/-- Every native hexad has a section of the literal six-point action together
with the square-root identity required by the central-cover splitting reduction. -/
theorem exists_native_section {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    ∃ j : alternatingGroup (Fin 6) →* MulAction.stabilizer M22 B,
      (∀ a, m22HexadAction hB (j a) = a.val) ∧ HasSquare j := by
  obtain ⟨p, hp⟩ := exists_m22Hexad_complementary_point hB
  refine ⟨m22HexadPointSection hB hp, ?_, pointSection_hasSquare hB hp⟩
  intro a
  exact congrArg Subtype.val (m22HexadSixMap_pointSection hB hp a)

end Sporadic.Mathieu.M22HexadFourSquare
