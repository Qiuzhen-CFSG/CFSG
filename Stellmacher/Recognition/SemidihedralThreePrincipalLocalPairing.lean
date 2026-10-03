module
public import ABG.ChapterIII.Section7.ThreePrincipalPairing
public import Theory.Character.InvolutionPairQuotient
public import Theory.SpecificGroups.GL2.ThreeInvolutionPairs
public import Stellmacher.Recognition.SemidihedralCentralizerQuotient
public import Stellmacher.Recognition.SemidihedralThreePrincipalLocalSections
public import Theory.SpecificGroups.GL2.ThreeOddCoreInvolutionFibers

/-!
# Local principal-character pairing with the odd core retained

The local pairing in ABG III.7 (8) follows from two concrete facts: every
noncentral quotient involution has [O₂′(N) : C_O₂′(N)(T)] involution lifts,
and the root-supported character combination on a product is four exactly
when its quotient product squares to the scalar involution, and zero otherwise.

There are twenty-four such quotient pairs. Each has b² lifts, so the sum is
96b². Since |N| = 48|O₂′(N)| = 48|A|b, normalization gives 2b/|A|. The
odd core is retained throughout. The final theorem obtains the quotient map
from semidihedral N₂ recognition and applies the proved fiber and section
formulas to every supplied principal datum.

Source: Alperin–Brauer–Gorenstein, III.7 equation (8), article pp.103–104.
-/

namespace Stellmacher.Recognition
open Theory.Character Matrix Matrix.GeneralLinearGroup
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable

private theorem involution_image_order
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hker : Nat.Coprime 2 (Nat.card f.ker))
    (u : G) (hu : orderOf u = 2) : orderOf (f u) = 2 := by
  apply orderOf_eq_prime (p := 2)
  · rw [← map_pow, ← hu, pow_orderOf_eq_one, map_one]
  · intro he
    let a : f.ker := ⟨u, he⟩
    have ho : orderOf a = 2 := (Subgroup.orderOf_coe a).symm.trans hu
    have hd : 2 ∣ Nat.card f.ker := ho ▸ orderOf_dvd_natCard a
    have hh := Nat.eq_one_of_dvd_coprimes hker (dvd_refl 2) hd
    norm_num at hh

/-- Uniform noncentral involution fibers and the root-section evaluation
imply the local principal-character pairing, without killing the odd core. -/
public theorem threePrincipal_local_pairing_of_quotient_data
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) (T : Subgroup G) (c : ABG.ThreePrincipalData G x)
    (f : Subgroup.centralizer ({x} : Set G) →* GL (Fin 2) (ZMod 3))
    (hfker : f.ker = pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)))
    (hfiber : ∀ y : GL (Fin 2) (ZMod 3), orderOf y = 2 → y ≠ threeCentral →
      Nat.card {u : {u : Subgroup.centralizer ({x} : Set G) // orderOf u = 2} // f u = y} =
        ((Subgroup.centralizer (T : Set G)).subgroupOf
          ((pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))).map
            (Subgroup.centralizer ({x} : Set G)).subtype)).index)
    (hvalue : ∀ u v : Subgroup.centralizer ({x} : Set G),
      orderOf u = 2 → orderOf v = 2 →
      c.localOrderFunction (u * v) = if (f u * f v)^2 = threeCentral then 4 else 0) :
    let N := Subgroup.centralizer ({x} : Set G)
    let K := (pPrimeCore 2 N).map N.subtype
    let A := (Subgroup.centralizer (T : Set G)).subgroupOf K
    scalarProduct N c.localOrderFunction (fun u => (involutionPairCount u : ℂ)) =
      2 * (A.index : ℂ) / Nat.card A := by
  let N := Subgroup.centralizer ({x} : Set G)
  let O := pPrimeCore 2 N
  let K := O.map N.subtype
  let A := (Subgroup.centralizer (T : Set G)).subgroupOf K
  have hfodd : Nat.Coprime 2 (Nat.card f.ker) := by
    rw [hfker]
    exact pPrimeCore_coprime_card
  have hpair := scalarProduct_involutionPairCount_eq_of_fibers f
    (involution_image_order f hfodd) (fun p => (p.1 * p.2)^2 = threeCentral)
    A.index 24 4 c.localOrderFunction (by
      intro a b ha hb
      split_ifs with h
      · simpa only [if_pos h] using hvalue a b ha hb
      · simpa only [if_neg h] using hvalue a b ha hb) (by
      intro a b ha hb hab
      obtain ⟨ha', hb'⟩ := three_involution_pair_square_central_noncentral a b ha hb hab
      exact ⟨hfiber a ha ha', hfiber b hb hb'⟩)
    three_involution_pair_square_central_card
  have hK : Nat.card K = Nat.card O := Subgroup.card_map_of_injective N.subtype_injective
  have hcard : Nat.card N = 48 * Nat.card A * A.index := by
    rw [involutionCentralizer_card_of_simple_nTwo S hS hN x hx,
      ← hK, ← A.card_mul_index, mul_assoc]
  have ha : (Nat.card A : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := A)).ne'
  have hb : (A.index : ℂ) ≠ 0 := by exact_mod_cast A.index_ne_zero_of_finite
  have hpair' : scalarProduct N c.localOrderFunction (fun u => (involutionPairCount u : ℂ)) =
      (Nat.card N : ℂ)⁻¹ * (24 * (A.index : ℂ)^2 * 4) := by
    convert hpair using 1
    · congr 1
      exact Subsingleton.elim _ _
    · simp only [Nat.cast_ofNat]
      rfl
  change scalarProduct N c.localOrderFunction _ = 2 * (A.index : ℂ) / Nat.card A
  rw [hpair', hcard]
  push_cast
  field_simp
  ring

/-- ABG III.7 (8): the local principal-character pairing is twice the index
of the four-group centralizer in the odd core, divided by its order. -/
public theorem threePrincipal_local_pairing
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2)
    (T : Subgroup G) [IsElementaryAbelian 2 T] (hT : Nat.card T = 4) (hxT : x ∈ T)
    (c : ABG.ThreePrincipalData G x) :
    let N := Subgroup.centralizer ({x} : Set G)
    let K := (pPrimeCore 2 N).map N.subtype
    let A := (Subgroup.centralizer (T : Set G)).subgroupOf K
    scalarProduct N c.localOrderFunction (fun u => (involutionPairCount u : ℂ)) =
      2 * (A.index : ℂ) / Nat.card A := by
  let N := Subgroup.centralizer ({x} : Set G)
  let O := pPrimeCore 2 N
  obtain ⟨e⟩ := involutionCentralizer_oddCoreQuotient_equiv_gl2_three_of_simple_nTwo
    S hS hN x hx
  let eF : ABG.GL2 3 1 ≃* GL (Fin 2) (ZMod 3) :=
    Units.mapEquiv (GaloisField.equivZmodP 3).toRingEquiv.mapMatrix.toMulEquiv
  let f : N →* GL (Fin 2) (ZMod 3) :=
    (e.trans eF).toMonoidHom.comp (QuotientGroup.mk' O)
  have hf : Function.Surjective f :=
    (e.trans eF).surjective.comp (QuotientGroup.mk'_surjective O)
  have hfker : f.ker = O := by
    rw [MonoidHom.ker_comp_of_injective _ _ (e.trans eF).injective,
      QuotientGroup.ker_mk']
  exact threePrincipal_local_pairing_of_quotient_data S hS hN x hx T c f hfker
    (Subgroup.card_noncentral_involution_fiber_of_oddCoreQuotient x hx T hT hxT f hf hfker)
    (threePrincipal_localOrderFunction_mul_of_semidihedral S hS x hx c f hf hfker)

end
end Stellmacher.Recognition
