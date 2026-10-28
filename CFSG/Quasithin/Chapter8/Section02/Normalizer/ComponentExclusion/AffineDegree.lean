module

public import Theory.Representation.AbelianAffineDegree
public import Theory.SpecificGroups.SL2.AffineFreeAction
public import Theory.SpecificGroups.SL2.AffineTetrahedral
public import Theory.SpecificGroups.SL2.Affine.Action
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Mathlib.Algebra.CharP.CharAndCard
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.FrobeniusDegree

/-!
# The degree obstruction for genuine odd-plane extensions

For the natural SL₂(p) quotient, explicit binary tetrahedral matrices give
a subgroup of order 24 in the actual marked plane action. The quotient SL₂(5) acts faithfully on the normal elementary p-plane when
its centralizer is precisely that plane. Restricting this action to the
actual embedded SL₂(3) gives free actors of order 24, including when p ≠ 5.
The automizer character bound then applies without splitting the extension
or assuming irreducibility of the binary module. Restriction along an
injective embedding into the actual automorphism action of a binary section
preserves faithfulness and gives the same degree bound on that section.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the final
sentence of Lemma 8.2.7, printed p.718 (PDF p.735); the extension alternatives
are specified in A.3.6 and A.3.12–13, pp.43–49. Both alternatives retain their literal quotient and conjugation markings.
The resulting obstruction applies to the rank-ten section bound from 8.2.7;
the construction of that section and its extension remains with the parent.
-/

public section
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion
open Subgroup Matrix
open scoped IsMulCommutative

private theorem plane_nontrivial {E : Type*} [Group E] [Finite E]
    (N : Subgroup E) {p : ℕ} (hp : 3 < p) (hN : Nat.card N = p ^ 2) : Nontrivial N := by
  apply Finite.one_lt_card_iff_nontrivial.mp
  rw [hN]
  nlinarith

/-- A self-centralizing elementary odd-plane extension of SL₂(5) has faithful binary degree at least 24. -/
theorem sl25Extension_finrank_ge_twentyFour {E V : Type*} [Group E] [Finite E]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (N : Subgroup E) [N.Normal] {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p N]
    (hp : 3 < p) (hN : Nat.card N = p ^ 2)
    (e : (E ⧸ N) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))
    (hcentral : centralizer (N : Set E) = N)
    (ρ : Representation (ZMod 2) E V) (hρ : Function.Injective ρ) :
    24 ≤ Module.finrank (ZMod 2) V := by
  let := plane_nontrivial N hp hN
  obtain ⟨α, hα, hconj⟩ := N.exists_faithful_quotient_conjugation hcentral
  let β := α.comp e.symm.toMonoidHom
  obtain ⟨C, hC, hfree⟩ := Matrix.SpecialLinearGroup.AffineFreeAction.exists_free_twentyFour_sl25
    hp hN β (hα.comp e.symm.injective)
  have hodd : Odd (Nat.card N) := by
    rw [hN]
    exact ((Fact.out : p.Prime).odd_of_ne_two (by omega)).pow
  have hn : (Nat.card N : ZMod 2) ≠ 0 := ZMod.natCast_ne_zero_iff_odd.mpr hodd
  have hd := Representation.card_le_finrank_of_fixedPointFree_quotientAction ρ N hρ hn
    (e.toMonoidHom.comp (QuotientGroup.mk' N))
    (e.surjective.comp (QuotientGroup.mk'_surjective N)) β
    (fun g => by simpa [β] using hconj g) C hfree
  rwa [hC] at hd

/-- Apply the extension bound through an injective map into the actual binary section action. -/
theorem sl25Extension_embedded_action_finrank_ge_twentyFour
    {E W : Type*} [Group E] [Finite E] [Group W] [Finite W]
    [IsElementaryAbelian 2 W]
    (N : Subgroup E) [N.Normal] {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p N]
    (hp : 3 < p) (hN : Nat.card N = p ^ 2)
    (e : (E ⧸ N) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))
    (hcentral : centralizer (N : Set E) = N)
    (A : Subgroup (MulAut W)) (i : E →* A) (hi : Function.Injective i) :
    24 ≤ Module.finrank (ZMod 2) (Additive W) := by
  let ρ := Representation.ofElementaryAbelianAction (A := A) (G := W) (p := 2)
  have hρ : Function.Injective ρ := by
    intro a b hab
    apply Subtype.ext
    ext w
    exact Additive.ofMul.injective
      (congrArg (fun f : Module.End (ZMod 2) (Additive W) => f (Additive.ofMul w)) hab)
  exact sl25Extension_finrank_ge_twentyFour N hp hN e hcentral (ρ.comp i) (hρ.comp hi)

/-- The exact natural quotient and conjugation marking force faithful binary degree at least 24. -/
theorem naturalExtension_finrank_ge_twentyFour {E V : Type*} [Group E] [Finite E]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (N : Subgroup E) [N.Normal] {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p N]
    (hp : 3 < p) (hN : Nat.card N = p ^ 2)
    (hmodel : CFSG.Quasithin.Chapter1.Section02.LocalModels.NaturalSL2Action E N p)
    (ρ : Representation (ZMod 2) E V) (hρ : Function.Injective ρ) :
    24 ≤ Module.finrank (ZMod 2) V := by
  classical
  let := plane_nontrivial N hp hN
  obtain ⟨F, _, _, hF, v, e, ha⟩ := hmodel
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime (by simpa only [← Nat.card_eq_fintype_card] using hF)
  obtain ⟨C, hC⟩ := Matrix.SpecialLinearGroup.AffineTetrahedral.exists_subgroup_card_twentyFour
    (F := F) hp
  let α : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut N :=
    (MulAut.congr v.symm).toMonoidHom.comp (Matrix.SL2.naturalAction F)
  have hα (g : E) : α (e (QuotientGroup.mk' N g)) = MulAut.conjNormal g := by
    apply MulEquiv.ext
    intro n
    apply v.injective
    change v (v.symm (Matrix.SL2.naturalAction F (e (QuotientGroup.mk' N g)) (v n))) = _
    rw [v.apply_symm_apply]
    exact (ha g n).symm
  have hcop : p.Coprime (Nat.card C) := by
    rw [hC, show 24 = 2 ^ 3 * 3 by decide]
    apply Nat.Coprime.mul_right
    · exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))).pow_right 3
    · exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt (by decide) hp)
  have hfree : ∀ c : C, c ≠ 1 → MonoidHom.FixedPointFree (α c) := by
    intro c hc n hn
    by_contra hne
    have hv : Multiplicative.toAdd (v n) ≠ 0 := by
      intro hv
      apply hne
      apply v.injective
      simpa using congrArg Multiplicative.ofAdd hv
    have hfix : (c : Matrix.SpecialLinearGroup (Fin 2) F).val *ᵥ
        Multiplicative.toAdd (v n) = Multiplicative.toAdd (v n) := by
      have hh := congrArg (fun x => Multiplicative.toAdd (v x)) hn
      change Multiplicative.toAdd (v (v.symm
        (Matrix.SL2.naturalAction F c (v n)))) = _ at hh
      simpa only [v.apply_symm_apply, Matrix.SL2.naturalAction_apply] using hh
    have hpow : (c : Matrix.SpecialLinearGroup (Fin 2) F) ^ Nat.card C = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (x := c))
    have hc1 := Matrix.SpecialLinearGroup.AffineFreeAction.eq_one_of_fixed_vector_of_coprime
      (c : Matrix.SpecialLinearGroup (Fin 2) F) hcop hpow _ hv hfix
    exact hc (Subtype.ext hc1)
  have hodd : Odd (Nat.card N) := by
    rw [hN]
    exact ((Fact.out : p.Prime).odd_of_ne_two (by omega)).pow
  have hn : (Nat.card N : ZMod 2) ≠ 0 := ZMod.natCast_ne_zero_iff_odd.mpr hodd
  have hd := Representation.card_le_finrank_of_fixedPointFree_quotientAction ρ N hρ hn
    (e.toMonoidHom.comp (QuotientGroup.mk' N))
    (e.surjective.comp (QuotientGroup.mk'_surjective N)) α hα C hfree
  rwa [hC] at hd

/-- Both source extension alternatives force faithful binary degree at least 24. -/
theorem oddPlaneExtension_finrank_ge_twentyFour {E V : Type*} [Group E] [Finite E]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (N : Subgroup E) [N.Normal] {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p N]
    (hp : 3 < p) (hN : Nat.card N = p ^ 2)
    (hmodel : Chapter1.Section02.LocalModels.NaturalSL2Action E N p ∨
      (Nonempty ((E ⧸ N) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
        centralizer (N : Set E) = N))
    (ρ : Representation (ZMod 2) E V) (hρ : Function.Injective ρ) :
    24 ≤ Module.finrank (ZMod 2) V := by
  rcases hmodel with h | ⟨⟨e⟩, h⟩
  · exact naturalExtension_finrank_ge_twentyFour N hp hN h ρ hρ
  · exact sl25Extension_finrank_ge_twentyFour N hp hN e h ρ hρ

/-- Restriction along the specified embedding into the actual section action
preserves faithfulness. Its kernel action is the restriction along
`i.comp N.subtype`, hence uses the literal image `N.map i`. -/
theorem oddPlaneExtension_embedded_action_finrank_ge_twentyFour
    {E W : Type*} [Group E] [Finite E] [Group W] [Finite W]
    [IsElementaryAbelian 2 W]
    (N : Subgroup E) [N.Normal] {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p N]
    (hp : 3 < p) (hN : Nat.card N = p ^ 2)
    (hmodel : Chapter1.Section02.LocalModels.NaturalSL2Action E N p ∨
      (Nonempty ((E ⧸ N) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
        centralizer (N : Set E) = N))
    (A : Subgroup (MulAut W)) (i : E →* A) (hi : Function.Injective i) :
    24 ≤ Module.finrank (ZMod 2) (Additive W) := by
  let ρ := Representation.ofElementaryAbelianAction (A := A) (G := W) (p := 2)
  have hρ : Function.Injective ρ := by
    intro a b hab
    apply Subtype.ext
    ext w
    exact Additive.ofMul.injective
      (congrArg (fun f : Module.End (ZMod 2) (Additive W) => f (Additive.ofMul w)) hab)
  exact oddPlaneExtension_finrank_ge_twentyFour N hp hN hmodel (ρ.comp i) (hρ.comp hi)

/-- The genuine odd-plane extensions cannot embed in a section action of
binary degree at most ten, the upper bound obtained in Lemma 8.2.7. -/
theorem oddPlaneExtension_section_obstruction
    {E W : Type*} [Group E] [Finite E] [Group W] [Finite W]
    [IsElementaryAbelian 2 W]
    (N : Subgroup E) [N.Normal] {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p N]
    (hp : 3 < p) (hN : Nat.card N = p ^ 2)
    (hmodel : Chapter1.Section02.LocalModels.NaturalSL2Action E N p ∨
      (Nonempty ((E ⧸ N) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
        centralizer (N : Set E) = N))
    (A : Subgroup (MulAut W)) (i : E →* A) (hi : Function.Injective i)
    (hsmall : Module.finrank (ZMod 2) (Additive W) ≤ 10) : False := by
  have hlarge := oddPlaneExtension_embedded_action_finrank_ge_twentyFour N hp hN hmodel A i hi
  omega

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion
