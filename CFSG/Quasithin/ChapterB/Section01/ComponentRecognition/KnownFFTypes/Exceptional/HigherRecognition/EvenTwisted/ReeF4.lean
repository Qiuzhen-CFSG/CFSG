module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.Absolute
public import Theory.SpecificGroups.ReeF4.AlmostSimpleTwoElements
public import Theory.Representation.ElementaryCentralQuotient
public import Theory.Representation.ReeF4.FixedSpaceBounds

/-!
# Ree F4: reduction to intrinsic rank and involution bounds

Every elementary two-subgroup of the ambient group lies in the quasisimple
component, by the proved innerness theorem for the actual Ree quotient.
A faithful irreducible action makes the central quotient injective on that
elementary subgroup. Thus its order is controlled by the model's intrinsic
bound. Any nonidentity element of it is an involution, and its fixed space
contains the subgroup fixed space. The inequalities 5n < 10n then give the
strict F-module gap, with the original coefficient-field degree retained.

The sharp elementary order bound and the central-cover involution bound remain
explicit inputs. This module does not yet prove the unconditional source
exclusion. No absolute irreducibility of the component restriction is assumed.

Source: Guralnick--Malle, *Classification of 2F-modules, II*, Theorem 8.1
and Lemma 8.8, internal pp.52, 57--58. The 2A-purity argument needed for 2F
is unnecessary for the weaker F-module inequality proved conditionally here.
-/

public section

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.ReeF4
open Subgroup Representation Representation.BinaryOffender
open Theory.GroupTheory
universe u v

variable {H : Type u} [Group H] [Finite H] (N : Subgroup H)
  [N.Normal] [IsQuasisimple N]

/-- The actual model order bound controls an ambient elementary subgroup.
Both placement in N and injectivity modulo its center are proved. -/
theorem elementary_rank_le_of_model_bound {m : ℕ} (hm : 1 ≤ m)
    (hF : generalizedFitting H = N) (e : N ⧸ center N ≃* _root_.ReeF4.Model m)
    (horder : ∀ B : Subgroup (_root_.ReeF4.Model m), IsElementaryAbelian 2 B →
      Nat.card B ≤ 2 ^ (5 * (2 * m + 1)))
    {E W : Type v} [Field E] [CharP E 2]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (σ : Representation E H W) [IsIrreducible (σ.comp N.subtype)]
    (hf : Function.Injective σ) (A : Subgroup H) [IsElementaryAbelian 2 A] :
    rank A ≤ 5 * (2 * m + 1) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAN := _root_.ReeF4.elementary_le_of_generalizedFitting N hm hF e A
  let B := A.subgroupOf N
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAN
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (center N))
  have hcard : Nat.card (B.map π) = Nat.card B := by
    change Nat.card (B.map (e.toMonoidHom.comp (QuotientGroup.mk' (center N)))) = _
    rw [← Subgroup.map_map, Subgroup.card_map_of_injective e.injective]
    exact card_map_centralQuotient (p := 2) (σ.comp N.subtype)
      (hf.comp Subtype.val_injective) B
  have hbound := horder (B.map π) (IsElementaryAbelian.map π)
  rw [hcard] at hbound
  have hBA : Nat.card B = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  rw [hBA] at hbound
  simpa only [rank, Nat.log_pow Nat.one_lt_two] using Nat.log_mono_right (b := 2) hbound

/-- Assembly of the F inequality from the two genuine model estimates.
The hypotheses still need model-specific proofs. -/
theorem absoluteGap_of_involution_bound {m : ℕ} (hm : 1 ≤ m)
    (hF : generalizedFitting H = N) (e : N ⧸ center N ≃* _root_.ReeF4.Model m)
    (horder : ∀ B : Subgroup (_root_.ReeF4.Model m), IsElementaryAbelian 2 B →
      Nat.card B ≤ 2 ^ (5 * (2 * m + 1)))
    (hinvolution : _root_.ReeF4.CoverInvolutionBound.{u,v} m) :
    AbsoluteGap.{u,v} H N := by
  intro E W _ _ _ _ _ _ _ σ _ hi hf A hA
  let : IsIrreducible (σ.comp N.subtype) := hi
  let : IsElementaryAbelian 2 A := hA.2
  have hrank := elementary_rank_le_of_model_bound N hm hF e horder σ hf A
  have hAN := _root_.ReeF4.elementary_le_of_generalizedFitting N hm hF e A
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1
  let t : N := ⟨a, hAN a.property⟩
  have ht : t ≠ 1 := by
    intro ht
    apply ha
    apply Subtype.ext
    exact congrArg (fun z : N => (z : H)) ht
  have ht2 : t ^ 2 = 1 := Subtype.ext
    (elemPow_eq_one_of_isElementaryAbelian (a : H) a.property)
  have hinv := hinvolution N ⟨e⟩ E W (σ.comp N.subtype) hi
    (hf.comp Subtype.val_injective) t ht ht2
  have hz : zpowers t ≤ A.subgroupOf N := zpowers_le.mpr a.property
  have hfixed : invariants (σ.comp A.subtype) ≤
      invariants ((σ.comp N.subtype).comp (zpowers t).subtype) := by
    intro w hw z
    exact hw ⟨((z : N) : H), hz z.property⟩
  have hcodim :
      Module.finrank E (W ⧸ invariants ((σ.comp N.subtype).comp (zpowers t).subtype)) ≤
      Module.finrank E (W ⧸ invariants (σ.comp A.subtype)) := by
    rw [Submodule.finrank_quotient, Submodule.finrank_quotient]
    exact Nat.sub_le_sub_left (Submodule.finrank_mono hfixed) _
  have hlarge := hinv.trans (Nat.mul_le_mul_left (Module.finrank (ZMod 2) E) hcodim)
  omega

/-- Select the original positive Ree parameter from the literal quotient witness.
The two estimates remain the only extra premises in this family assembly. -/
theorem absoluteGap_of_bounds
    (hF : generalizedFitting H = N)
    (hmodel : _root_.ReeF4.IsReeF4Model (N ⧸ center N))
    (horder : ∀ m : ℕ, 1 ≤ m →
      ∀ B : Subgroup (_root_.ReeF4.Model m), IsElementaryAbelian 2 B →
        Nat.card B ≤ 2 ^ (5 * (2 * m + 1)))
    (hinvolution : ∀ m : ℕ, 1 ≤ m → _root_.ReeF4.CoverInvolutionBound.{u,v} m) :
    AbsoluteGap.{u,v} H N := by
  obtain ⟨m, hm, ⟨e⟩⟩ := hmodel
  exact absoluteGap_of_involution_bound N hm hF e (horder m hm) (hinvolution m hm)

/-- The binary consumer uses the proved Schur-field transport on the original
ambient representation, including irreducibility of its component restriction. -/
theorem not_ff_of_involution_bounds
    (hF : generalizedFitting H = N)
    (hmodel : _root_.ReeF4.IsReeF4Model (N ⧸ center N))
    (horder : ∀ m : ℕ, 1 ≤ m →
      ∀ B : Subgroup (_root_.ReeF4.Model m), IsElementaryAbelian 2 B →
        Nat.card B ≤ 2 ^ (5 * (2 * m + 1)))
    (hinvolution : ∀ m : ℕ, 1 ≤ m → _root_.ReeF4.CoverInvolutionBound.{u,v} m)
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) H V)
    [IsIrreducible ρ] [IsIrreducible (ρ.comp N.subtype)]
    (hf : Function.Injective ρ) : ¬ IsFFModule ρ := by
  exact not_ff_of_absoluteGap N ρ hf
    (absoluteGap_of_bounds N hF hmodel horder hinvolution)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.ReeF4
