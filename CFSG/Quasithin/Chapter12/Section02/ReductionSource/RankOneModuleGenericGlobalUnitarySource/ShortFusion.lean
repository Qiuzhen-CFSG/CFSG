module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortFusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFactors

/-!
# Simultaneous fusion on the chosen module's short-root quotient

The literal whole-reduced input constructs the same short and long roots,
full q-element line and q² quotient module as the prepared source. Fusion
of every subset of that module is controlled by an element of the actual
ambient line normalizer which also normalizes the original L. The short
root dies in the quotient and the marked long root survives. No ambient
fusion or realization premise is added. Both orientations, the degree-two
rows and q=4 are retained.

Source: Aschbacher–Smith F.4.42 and its 5.3/12.2 application, printed
pp.295–296,659,795 of `refs/quasithin.pdf`. Common-centralizer containment
and the resulting unique fixed cosets remain separate source obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open UnitaryCompletion
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The original quotient module and all its simultaneous ambient fusion,
with the whole line as kernel and no additional fusion hypothesis. -/
theorem rankOne_unitary_short_root_ambient_quotient_fusion
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ hU : U ≤ center (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      let f := UnitarySource.shortLineQuotientMap L t U hU
      Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      f (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) = 1 ∧
      f z ≠ 1 ∧ (∀ v ∈ V.map f, v ≠ 1 →
        ∃ a ∈ primeToResidual 2 (centralizer ({t} : Set L)),
          f a * f z * (f a)⁻¹ = v) ∧
      ∀ (s : Set (UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U)),
        s ⊆ V.map f →
        ∀ g : UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U,
          (∀ x ∈ s, g*x*g⁻¹ ∈ V.map f) →
          ∃ a : UnitarySource.shortLineNormalizer L t U,
            a.val.val ∈ normalizer (L : Set G) ∧ ∀ x ∈ s,
              QuotientGroup.mk' (UnitarySource.shortLineKernel L t U) a * x *
                (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U) a)⁻¹ = g*x*g⁻¹ := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_short_root_ambient_quotient_fusion hi hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
