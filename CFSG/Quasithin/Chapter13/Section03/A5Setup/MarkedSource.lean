module

public import CFSG.Quasithin.Chapter13.Section03.A5Setup.LocalSource
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.ChosenModules
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Context
public import Theory.Representation.OrthogonalFourMinusRankOne.FivePoint.CoverAction

/-!
# The original A₅ Context from the chosen natural module

The natural quotient model from 12.2.2 is transported through the canonical
odd-degree core equivalence to the five-letter marking. The source minimal
A₅ choice gives normalizer containment before a normalizer action is known.
The concrete normalizer theorem then extends the actual L action to N_G(V),
with the same coordinates and the literal O₂(L) kernel.

Thus the original invariant flag constructs the Context consumed by 13.5
and 13.6. A one-or-two-copy outcome from 6.2.20 also suffices: the genuine
Irr⁺ condition rules out a diagonal double copy. The source entry supplies
T-invariance by homogeneity; module selection and its preceding classification
remain earlier obligations. No A₅ Context is assumed.
Source: Aschbacher–Smith 12.2.2(3d), 13.3.2(3), and Notation 13.2.1,
printed pp.795, 885, and 877.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup
open Section06.CentralizerReduction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

omit [Finite G] in
/-- Construct the actual five-point module and its full normalizer action
from the source conjugation model, retaining its given quotient map. -/
theorem exists_marking_of_conjugation_model [IsElementaryAbelian 2 V]
    (hLN : L ≤ normalizer (V : Set G))
    (hNL : normalizer (V : Set G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (f : V ≃* Multiplicative (natural (Fin 5)))
    (hf : ∀ (l : L) (v : V),
      ((f.symm (Multiplicative.ofAdd
        (Chapter6.Source.a5Module (e (QuotientGroup.mk' (pCore 2 L) l))
          (f v).toAdd))) : G) = MulAut.conj (l : G) (v : G)) :
    ∃ (s : A5Module.Marking L V)
      (p : normalizer (V : Set G) →* Equiv.Perm (Fin 5)),
      s.action.ker = pCore 2 L ∧
      (∀ (n : normalizer (V : Set G)) (x : FiveCentralizerGeometry.Space),
        MulAut.conj (n : G) (s.map (Multiplicative.ofAdd x)) =
          s.map (Multiplicative.ofAdd (coreRepresentation (Fin 5) (p n) x))) ∧
      (∀ (l : L) (hl : (l : G) ∈ normalizer (V : Set G)),
        p ⟨l, hl⟩ = (s.action l).val) := by
  let N := normalizer (V : Set G)
  let C := L.subgroupOf N
  let : C.Normal := (normal_subgroupOf_iff_le_normalizer hLN).mpr hNL
  let a := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have ha : Function.Surjective a := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let aC := a.comp (subgroupOfEquivOfLe hLN).toMonoidHom
  let E : Additive V ≃ₗ[ZMod 2] natural (Fin 5) :=
    f.toAdditiveLeft.toLinearEquiv (ZMod.map_smul _)
  let ρ := Representation.elementaryRepresentation (p := 2) V.normalizerMonoidHom
  have hE (l : C) (v : Additive V) :
      E (ρ l.val v) = naturalRepresentation (Fin 5) (aC l).val (E v) := by
    change f (V.normalizerMonoidHom l.val v.toMul) =
      Multiplicative.ofAdd (Chapter6.Source.a5Module (aC l) (f v.toMul).toAdd)
    apply f.symm.injective
    rw [f.symm_apply_apply]
    apply Subtype.ext
    exact (hf ((subgroupOfEquivOfLe hLN) l) v.toMul).symm
  obtain ⟨p, hp, hpL⟩ :=
    Representation.OrthogonalFourMinus.FivePoint.exists_ambient_permutation_of_cover
      ρ C aC (ha.comp (subgroupOfEquivOfLe hLN).surjective) E hE
  let c := (coreEquivNatural (Fin 5) (by decide)).toAddEquiv.toMultiplicative
  let m : Multiplicative FiveCentralizerGeometry.Space →* G :=
    V.subtype.comp (f.symm.toMonoidHom.comp c.toMonoidHom)
  have hm (n : N) (x : FiveCentralizerGeometry.Space) :
      MulAut.conj (n : G) (m (Multiplicative.ofAdd x)) =
        m (Multiplicative.ofAdd (coreRepresentation (Fin 5) (p n) x)) := by
    have he := hp n (Additive.ofMul (f.symm (c (Multiplicative.ofAdd x))))
    have hce := coreEquivNatural_equivariant (Fin 5) (by decide) (p n) x
    change f (V.normalizerMonoidHom n (f.symm (c (Multiplicative.ofAdd x)))) =
      Multiplicative.ofAdd (naturalRepresentation (Fin 5) (p n)
        (f (f.symm (c (Multiplicative.ofAdd x)))).toAdd) at he
    rw [f.apply_symm_apply] at he
    have he' := congrArg (fun y => ((f.symm y : V) : G)) he
    rw [f.symm_apply_apply] at he'
    exact he'.trans (congrArg (fun y => ((f.symm (Multiplicative.ofAdd y) : V) : G))
      hce.symm)
  have hpL' (l : L) (hl : (l : G) ∈ N) : p ⟨l, hl⟩ = (a l).val :=
    hpL ((subgroupOfEquivOfLe hLN).symm l)
  let s : A5Module.Marking L V := {
    map := m
    injective := V.subtype_injective.comp (f.symm.injective.comp c.injective)
    range_eq := by
      apply le_antisymm
      · rintro x ⟨y, rfl⟩
        exact (f.symm (c y)).property
      · intro x hx
        refine ⟨c.symm (f ⟨x, hx⟩), ?_⟩
        change ((f.symm (c (c.symm (f ⟨x, hx⟩))) : V) : G) = x
        rw [c.apply_symm_apply, f.symm_apply_apply]
    action := a
    onto := ha
    equivariant := by
      intro l x
      simpa only [hpL'] using hm ⟨l, hLN l.property⟩ x }
  refine ⟨s, p, ?_, hm, hpL'⟩
  ext l
  change e (QuotientGroup.mk' (pCore 2 L) l) = 1 ↔ l ∈ pCore 2 L
  rw [map_eq_one_iff e e.injective]
  exact QuotientGroup.eq_one_iff (N := pCore 2 L) l

/-- The original chosen natural A₅ module constructs the Context used in
the two closure branches, without a normalizer-action assumption. -/
theorem context_of_natural_module
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (d : Chapter12.Section02.ChosenModule T L V)
    (hmodel : Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (h12 : V₁ ≤ V₂) (h2V : V₂ ≤ V) (h1 : Nat.card V₁ = 2) (h2 : Nat.card V₂ = 4)
    (hT1 : (T : Subgroup G) ≤ normalizer (V₁ : Set G))
    (hT2 : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (h3V : V₃ ≤ V) (h3 : Nat.card V₃ = 8)
    (hT3 : (T : Subgroup G) ≤ normalizer (V₃ : Set G)) :
    Nonempty (Section05.A5Source.Context T L V V₁ V₂ V₃) := by
  let := d.elementary
  obtain ⟨e, f, hf⟩ := hmodel
  obtain ⟨s, p, hk, hp, hl⟩ := exists_marking_of_conjugation_model d.normalizes
    (module_normalizer h d e hTV) e f hf
  exact ⟨⟨h, d, ⟨s, hk, p, hp, hl, hTV, d.le_sylow, h12, h2V, h1, h2, hT1, hT2⟩,
    h3V, h3, hT3⟩⟩

/-- Actual 6.2.20/12.2.2 consumer: Irr⁺ removes the double-copy alternative
before constructing the original A₅ Context. -/
theorem context_of_one_or_two_modules
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (d : Chapter12.Section02.ChosenModule T L V)
    (hmodel : Chapter6.Source.IsOneOrTwoA5Modules L V)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (h12 : V₁ ≤ V₂) (h2V : V₂ ≤ V) (h1 : Nat.card V₁ = 2) (h2 : Nat.card V₂ = 4)
    (hT1 : (T : Subgroup G) ≤ normalizer (V₁ : Set G))
    (hT2 : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (h3V : V₃ ≤ V) (h3 : Nat.card V₃ = 8)
    (hT3 : (T : Subgroup G) ≤ normalizer (V₃ : Set G)) :
    Nonempty (Section05.A5Source.Context T L V V₁ V₂ V₃) :=
  context_of_natural_module h d (d.one_a5_of_one_or_two hmodel) hTV
    h12 h2V h1 h2 hT1 hT2 h3V h3 hT3

end CFSG.Quasithin.Chapter13.Section03.A5Setup
