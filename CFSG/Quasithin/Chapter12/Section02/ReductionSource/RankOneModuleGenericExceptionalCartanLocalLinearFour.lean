module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalLinearFour
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The original chosen-module cubic excludes the linear four-group alternative

The literal Chapter12 application retains the original Sylow, module, both
Cartan Hall subgroups and residual. The original right Hall cannot normalize
a four-group through the residual involution in either linear ternary row.
Construction of that four-group from cyclic-actor escape remains open.
Source: Aschbacher--Smith 5.1.13 and 12.2.2, printed pp.636,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The original chosen-module sieve excludes the B-invariant four-group
alternative while retaining the marked involution and the whole Cartan mover. -/
theorem rankOne_local_cartan_escape_seed_linear_four_reduction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        C.Normal ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ (ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p)) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨ IsSL (C ⧸ pCore 2 C) 3 p) →
          K = residual H ∧ p = 5 ∧
            ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
            IsSL (((residual H).subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y))) 2 5 ∧
            Nat.card B = 3 ∧
            let q := QuotientGroup.mk' (pCore 2 Y)
            let Rbar := ((residual H).subgroupOf Y).map q
            let Cbar := C.map q
            let Tbar := ((T : Subgroup G).subgroupOf Y).map q
            ∃ z : Y ⧸ pCore 2 Y,
              z ∈ Rbar ∧ orderOf z = 2 ∧
              (∀ x : Y ⧸ pCore 2 Y, x ∈ Rbar → orderOf x = 2 → x = z) ∧
              z ∈ Tbar ∧
              Tbar ⊔ (B.subgroupOf Y).map q ≤ centralizer ({z} : Set (Y ⧸ pCore 2 Y)) ∧
              Rbar = ⁅Cbar ⊓ centralizer ({z} : Set (Y ⧸ pCore 2 Y)),
                Cbar ⊓ centralizer ({z} : Set (Y ⧸ pCore 2 Y))⁆ ∧
              (normalizer (residual H : Set G)).subgroupOf Y =
                (centralizer ({z} : Set (Y ⧸ pCore 2 Y))).comap q ∧
              (∀ E : Subgroup (Y ⧸ pCore 2 Y), E ≤ Cbar ⊓ Tbar →
                IsElementaryAbelian 2 E → Nat.card E = 4 →
                ¬ (B.subgroupOf Y).map q ≤ normalizer (E : Set (Y ⧸ pCore 2 Y))) ∧
              ∃ a : (A ⊓ Y : Subgroup G), q ⟨a.val,a.property.2⟩ * z * (q ⟨a.val,a.property.2⟩)⁻¹ ≠ z) :=
  localCartan_escape_seed_linear_four_reduction
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hY hescape

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
