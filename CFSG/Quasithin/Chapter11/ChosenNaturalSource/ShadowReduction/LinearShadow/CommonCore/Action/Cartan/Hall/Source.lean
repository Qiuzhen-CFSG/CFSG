module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Hall.Geometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Hall.DiagonalMatrix
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Coordinates

/-!
# Hall geometry in the original chosen-natural source

The relative Hall subgroup supplies prime support, normalization of the
original inner Sylow, and a nonidentity conjugate diagonal in the literal
K/O2(K) marking. The exact 11.0.4 residual clauses give D0 <= L, and the
existing Cartan-choice theorem then chooses a permitted Cartan containing D0.
The diagonal is also applied to the existing natural fixed-space consumer.

The SL3/Sp4 alternative and 11.0.4 clauses remain with the parameter-component
and local-geometry producers. The natural marking and VH <= T remain with
the natural-action producer. The final fixed-space application retains the
separate L-module dichotomy owned by the parent Cartan assembly task.
No Hall torus identification, diagonal witness or normalization is assumed.
Source: Aschbacher--Smith, 11.3.7(2,3,5), printed p.773.
-/

open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Hall
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

open LocalGeometry in
/-- The Hall geometry supplies both inputs of the original Cartan-choice
consumer. The displayed residual clauses are exactly source 11.0.4. -/
theorem source_hall_cartan
    (cL : Coordinates D S.field) (f : InvariantFlag cL)
    (s : Hypothesis1131At D S (cL.binarySubspace (f.space 0)) H)
    (c : NaturalQuotientMarking T H S.field) (A : Subgroup G)
    (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    oddCartanPart A ≤ L ∧
      oddCartanPart A ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ∧
      ∃ X : Subgroup G, IsCartan T L X ∧ oddCartanPart A ≤ X := by
  have hL := source_oddCartanPart_le D S A hA hHall
    (source_hall_prime_support s c A hA hHall) halt hres hcubic
  have hn := (le_inf ((oddCartanPart_le A).trans (hA.trans inf_le_left)) hL).trans
    (source_normalizes_inner_sylow s c halt)
  exact ⟨hL,hn,source_cartan_choice cL A H hA hHall hL hn⟩


theorem source_conjugate_diagonal (s : Hypothesis1131At D S U₁ H)
    (c : NaturalQuotientMarking T H S.field) (A : Subgroup G)
    (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G)))) :
    ∃ d : outsideResidual H, (d : G) ∈ oddCartanPart A ∧
      ∃ b : SL(2,S.field.Carrier), ∃ a : S.field.Carrier, a ≠ 1 ∧
        (b * c.quotientEquiv (QuotientGroup.mk' _ d) * b⁻¹).val = !![a,0;0,a⁻¹] := by
  have hOK := oddCartanPart_le_residual_of_hall _ A hA hHall
  have hne0 := oddCartanPart_ne_bot A (source_hall_ne_bot s c A hA hHall)
  have ho : Odd (Nat.card A) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv]
    exact OddHall.odd_hall_odd hHall
  have ho0 : Odd (Nat.card ((oddCartanPart A).subgroupOf (outsideResidual H))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hOK).toEquiv]
    exact ho.of_dvd_nat (card_dvd_of_le (oddCartanPart_le A))
  have hn : (oddCartanPart A).subgroupOf (outsideResidual H) ≤
      normalizer (residualSylow s : Set (outsideResidual H)) :=
    (comap_mono ((oddCartanPart_le A).trans (hA.trans inf_le_right))).trans
      (residual_intersection_normalizes s c)
  have hne : (oddCartanPart A).subgroupOf (outsideResidual H) ≠ ⊥ := by
    intro he
    apply hne0
    have hh := congrArg (map (outsideResidual H).subtype) he
    simpa only [map_subgroupOf_eq_of_le hOK,Subgroup.map_bot] using hh
  obtain ⟨d,hd,b,a,ha,he⟩ := exists_conjugate_diagonal
    (quotientMap c) (quotientMap_surjective c) (residualSylow s)
    (by rw [quotientMap_ker]; exact pCore_isPGroup.le_sylow_of_normal _)
    ((oddCartanPart A).subgroupOf (outsideResidual H)) hn ho0 hne
  exact ⟨d,hd,b,a,ha,he⟩

/-- The actual D0 has the K-fixed space on the original omega center. -/
theorem source_oddCartan_fixed (s : Hypothesis1131At D S U₁ H)
    (c : NaturalQuotientMarking T H S.field) (A : Subgroup G)
    (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G)))) :
    omegaCenter T ⊓ centralizer (oddCartanPart A : Set G) =
      omegaCenter T ⊓ centralizer (outsideResidual H : Set G) := by
  obtain ⟨d,hd,b,a,ha,he⟩ := source_conjugate_diagonal s c A hA hHall
  exact c.omega_fixed_eq_of_conjugate_diagonal _
    (oddCartanPart_le_residual_of_hall _ A hA hHall) d hd b a ha he

/-- Actual application to the existing fixed-space consumer. The remaining
SL3/Sp4 module dichotomy belongs to the Cartan assembly owner. -/
theorem source_fixed_spaces (s : Hypothesis1131At D S U₁ H)
    (hWT : omegaClosure T H ≤ (T : Subgroup G))
    (c : NaturalQuotientMarking T H S.field) (A : Subgroup G)
    (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hcases : omegaCenter T ⊓ centralizer (oddCartanPart A : Set G) =
        omegaCenter T ⊓ centralizer (L : Set G) ∨
      ⁅omegaCenter T, oddCartanPart A⁆ = ⊥) :
    omegaCenter T ⊓ centralizer (L : Set G) = ⊥ ∧
      V ⊓ centralizer (L : Set G) = ⊥ ∧
      omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥ := by
  obtain ⟨d,hd,b,a,ha,he⟩ := source_conjugate_diagonal s c A hA hHall
  exact source_fixed_spaces_of_cartan_dichotomy s hWT c A hA hHall d hd b a ha he hcases


open LocalGeometry in
/-- The requested source Hall geometry, on the flag's actual binary line and
with the original counterexample retained. Every extra premise is an earlier
source clause or the separately produced natural marking. -/
theorem source_hall_geometry
    (cL : Coordinates D S.field) (f : InvariantFlag cL)
    (s : Hypothesis1131At D S (cL.binarySubspace (f.space 0)) H)
    (_hcounter : ¬ Proposition1132At D S (cL.binarySubspace (f.space 0)) H)
    (_hWT : omegaClosure T H ≤ (T : Subgroup G))
    (c : NaturalQuotientMarking T H S.field) (A : Subgroup G)
    (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    (∀ p : ℕ, p.Prime → p ∣ Nat.card A → p ∣ 2 ^ S.field.degree - 1) ∧
      oddCartanPart A ≤ L ∧
      oddCartanPart A ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ∧
      (∃ X : Subgroup G, IsCartan T L X ∧ oddCartanPart A ≤ X) ∧
      ∃ d : outsideResidual H, (d : G) ∈ oddCartanPart A ∧
        ∃ b : SL(2,S.field.Carrier), ∃ a : S.field.Carrier, a ≠ 1 ∧
          (b * c.quotientEquiv (QuotientGroup.mk' _ d) * b⁻¹).val = !![a,0;0,a⁻¹] := by
  obtain ⟨hL,hn,hX⟩ := source_hall_cartan cL f s c A hA hHall halt hres hcubic
  exact ⟨source_hall_prime_support s c A hA hHall,hL,hn,hX,
    source_conjugate_diagonal s c A hA hHall⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Hall
