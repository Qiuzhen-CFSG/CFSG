module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.EvenModels.Basic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.SimpleSection
public import Theory.AtlasPort.LinearGroups.G2.PSL3TwoParabolics
public import Theory.AtlasPort.LinearGroups.G2.PSL3TwoComponents
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAction
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# The G₂ cases of the field-component sieve

The actual involution centralizers contain no PSL₃(2), by the two parabolic
quotients and the octonion normalizer-cover theorem. An outer field involution
has a smaller G₂ fixed group once cocycle conjugacy and coefficient descent
are supplied; that group has no ordinary PSL₃(2) component. At the binary
endpoint the full fixed group is G₂(2), whose component is G₂(2)′.

The two catalogue exclusions below remain conditional on the indicated
universal automorphism and descent theorems. These premises have separate
owners; no automorphism coverage or field descent is asserted here.

Source: Aschbacher--Smith, proof of 15.3.38, printed p.1137; Theorem C and
Remark A.2.4, p.33; field fixed groups in 16.1.4(4), p.1171 and p.1191.
-/

public section
open Subgroup Atlas.G2 Atlas.G2.LieAutomorphismExtensions
open Atlas.G2.EvenFieldFixedResidual
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
universe u
variable {S : Type u} [Group S] (s : SimpleInput S)
include s

/-- Transport retains the literal fixed group and relative componenthood. -/
theorem SimpleInput.not_g2_fixed_model {H F : Type*} [Group H] [Field F] [Finite F]
    (e : S ≃* H) :
    ¬ Nonempty ((MulAut.congr e s.involution).fixedSubgroup ≃* Model F) := by
  rintro ⟨d⟩
  exact PSL3TwoObstructions.no_fixed_component_of_equiv s.involution
    ((MulAut.fixedSubgroupCongr e s.involution).trans d) s.component s.isComponent ⟨s.equiv⟩

/-- An involution with the marked fixed component cannot be inner in even G₂. -/
theorem SimpleInput.g2_involution_not_inner {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) (e : S ≃* Model F) :
    ∀ g : Model F, MulAut.congr e s.involution ≠ MulAut.conj g := by
  intro g hg
  let a := MulAut.congr e s.involution
  have ha : orderOf a = 2 := by
    exact (orderOf_injective (MulAut.congr e).toMonoidHom
      (MulAut.congr e).injective s.involution).trans s.involution_order
  obtain ⟨x, hx, _, hfix⟩ := MulAut.inner_involution_representative
    (model_center_eq_bot hq) a ha ⟨g, hg⟩
  let d := (MulAut.fixedSubgroupCongr e s.involution).trans (MulEquiv.subgroupCongr hfix)
  let j := d.toMonoidHom.comp (s.component.subtype.comp s.equiv.symm.toMonoidHom)
  exact PSL3TwoObstructions.not_injective_involution_centralizer x hx j
    (d.injective.comp (Subtype.val_injective.comp s.equiv.symm.injective))

/-- A supplied cocycle solution and coefficient descent give the field-case
contradiction. Their construction is still a prerequisite of the source exclusion. -/
theorem SimpleInput.not_g2_of_coboundary_of_descent
    {F : Type*} [Field F] [Finite F]
    (e : S ≃* Model F) (g : Model F) (σ : F ≃+* F)
    (he : MulAut.congr e s.involution = MulAut.conj g * fieldAction σ)
    (hboundary : ∃ c : Model F, g = c * fieldAction σ c⁻¹)
    (descent : (fieldAction σ).fixedSubgroup ≃* Model (fixedField σ)) : False := by
  let d := (fixedEquivOfCoboundary (MulAut.congr e s.involution) g
    (Classical.choose hboundary) σ he (Classical.choose_spec hboundary)).trans descent
  exact s.not_g2_fixed_model e ⟨d⟩

/-- Conditional catalogue assembly using full automorphism coverage and the
actual non-inner fixed-group theorem, with both universal premises explicit. -/
theorem SimpleInput.not_even_g2_of_coverage_of_fixed_groups
    (coverage : ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      2 < Nat.card F → Function.Surjective (semilinearAction (F := F)))
    (fixed : ∀ (F : Type) [Field F] [Finite F] {n : ℕ},
      2 ≤ n → Nat.card F = 2 ^ n → ∀ (a : MulAut (Model F)), a ^ 2 = 1 →
      ∀ (g : Model F) (σ : F ≃+* F), a = MulAut.conj g * fieldAction σ →
      (∀ h : Model F, a ≠ MulAut.conj h) →
      Nonempty (a.fixedSubgroup ≃* Model (fixedField σ)))
    {n : ℕ} (hn : 2 ≤ n) : ¬ ClassificationModels.IsG2At S (2 ^ n) := by
  rintro ⟨F, _, _, hc, ⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (show Fintype.card F = 2 ^ n by simpa only [Nat.card_eq_fintype_card] using hc)
  have hq : 2 < Nat.card F := by
    rw [hc]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (show 1 < n by omega)
  let a := MulAut.congr e s.involution
  have ha : a ^ 2 = 1 := by
    have ho : orderOf a = 2 := by
      exact (orderOf_injective (MulAut.congr e).toMonoidHom
        (MulAut.congr e).injective s.involution).trans s.involution_order
    exact ho ▸ pow_orderOf_eq_one a
  obtain ⟨z, hz⟩ := coverage F hq a
  have he : a = MulAut.conj z.left * fieldAction z.right := hz.symm
  exact s.not_g2_fixed_model e
    (fixed F hn hc a ha z.left z.right he (s.g2_involution_not_inner hq e))

/-- Conditional binary catalogue exclusion using the genuine full-group
conjugation identification of Aut(G₂(2)′). -/
theorem SimpleInput.not_binary_g2_of_automorphism_coverage
    (coverage : Function.Bijective binaryConjugation) :
    ¬ Nonempty (S ≃* commutator (Model (ZMod 2))) := by
  rintro ⟨e⟩
  let a := MulAut.congr e s.involution
  obtain ⟨g, hg⟩ := coverage.surjective a
  have hg2 : orderOf g = 2 := by
    calc
      orderOf g = orderOf (binaryConjugation g) :=
        (orderOf_injective binaryConjugation coverage.injective g).symm
      _ = orderOf a := congrArg orderOf hg
      _ = orderOf s.involution :=
        orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective s.involution
      _ = 2 := s.involution_order
  let d := MulAut.fixedSubgroupCongr e s.involution
  let j := d.toMonoidHom.comp (s.component.subtype.comp s.equiv.symm.toMonoidHom)
  let k := ((commutator (Model (ZMod 2))).subtype.comp (a.fixedSubgroup.subtype.comp j)).codRestrict
    (centralizer ({g} : Set (Model (ZMod 2)))) (by
      intro x
      apply mem_centralizer_singleton_iff.mpr
      have hx := (MulAut.mem_fixedSubgroup a (j x).val).mp (j x).property
      rw [← hg] at hx
      have hv := congrArg (fun z : BinaryDerived => z.val) hx
      exact (mul_inv_eq_iff_eq_mul.mp hv).symm)
  exact PSL3TwoObstructions.not_injective_involution_centralizer g hg2 k (by
    intro x y h
    apply s.equiv.symm.injective
    apply Subtype.val_injective
    apply d.injective
    apply Subtype.val_injective
    apply Subtype.val_injective
    exact congrArg (fun z : centralizer ({g} : Set (Model (ZMod 2))) => z.val) h)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
