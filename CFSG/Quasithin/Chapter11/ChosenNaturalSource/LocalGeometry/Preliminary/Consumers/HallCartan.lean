module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Consumers.Cubic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.SourceComplete
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Hall--Cartan and common action with restricted cubic containment

The only cubic generators used by the Hall consumer lie in the original
H-star intersection. Their torus prime support forces even field degree,
so the marked intersection theorem supplies their containment in L.
The existing prime-to-p residuals control the remaining generators.
This gives the literal Cartan choice and all five common-action clauses
without an unrestricted cubic-containment premise.

The preceding flag, residual, parameter and component inputs retain their
producers qt-d-1222-natural-local-geometry and
qt-d-1222-shadow-parameter-component. qt-d-1222-shadow-common-core retains
final 11.3.7 assembly; no proof of unrestricted 11.0.4 is asserted.
Source: Aschbacher--Smith, 11.3.7, printed p.773.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- Containment of the actual odd Cartan part using only its restricted cubic generators. -/
theorem source_oddCartanPart_le_of_hStar
    {T : Sylow 2 G} {L V H : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (cL : Coordinates D S.field)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card A → p ∣ 2 ^ S.field.degree - 1)
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G))) :
    oddCartanPart A ≤ L := by
  let M := normalizer (L : Set G)
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have ho : Odd (Nat.card A) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv]
    exact OddHall.odd_hall_odd hHall
  have hdiv (p : ℕ) (hp : p ∣ 2 ^ S.field.degree - 1) :
      p ∣ (2 ^ S.field.degree) ^ 2 - 1 :=
    hp.trans (Nat.sub_dvd_pow_sub_pow (2 ^ S.field.degree) 1 2)
  apply oddCartanPart_le_of_primeToResidual A M L (hA.trans inf_le_right) ho
  · intro p hp hlarge hd
    exact (hres p hp (halt.elim
      (fun hs => Or.inl ⟨hs, hsupport p hp hd, hlarge⟩)
      (fun hs => Or.inr ⟨hs, hdiv p (hsupport p hp hd)⟩))).le
  · intro x hx hx3
    have hd : 3 ∣ 2 ^ S.field.degree - 1 :=
      hsupport 3 Nat.prime_three (hx3 ▸ A.orderOf_dvd_natCard hx)
    have heven : Even S.field.degree :=
      (Nat.BinaryTorusParity.three_dvd_sub_one_iff _).mp hd
    exact Preliminary.natural_orderThree_mem_of_hStar D S cL heven hH
      (hA hx).1 (hA hx).2 hx3

namespace Hall

/-- The literal Hall--Cartan choice on Hypothesis1131At, without global cubic containment. -/
theorem source_hall_cartan_of_hStar
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
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G))) :
    oddCartanPart A ≤ L ∧
      oddCartanPart A ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ∧
      ∃ X : Subgroup G, IsCartan T L X ∧ oddCartanPart A ≤ X := by
  have hL := source_oddCartanPart_le_of_hStar D S cL s.outside A hA hHall
    (source_hall_prime_support s c A hA hHall) halt hres
  have hn := (le_inf ((oddCartanPart_le A).trans (hA.trans inf_le_left)) hL).trans
    (source_normalizes_inner_sylow s c halt)
  exact ⟨hL,hn,source_cartan_choice cL A H hA hHall hL hn⟩

end Hall

/-- All five common-action clauses on the original data. The exact preceding
source premises remain; the global cubic callback has been removed. -/
theorem source_action_complete_of_hStar
    (cL : Coordinates D S.field) (f : InvariantFlag cL) (hu : f.IsInnerUnique)
    (hline : U₁ = cL.binarySubspace (f.space 0))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hcounter : ¬ Proposition1132At D S U₁ H)
    (hcomponent : Source.NormalComponentIn H (outsideResidual H))
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (hs : @ChapterE.globalS G _ V D.elementary = (S.field.degree : ℕ∞))
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (hparameters : (S.field.degree : ℕ∞) < ChapterE.globalR V ∨
      (Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
        ChapterE.globalR V = S.field.degree ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G)))
    (hweak : D.centralQuotientPreimage U₁ ≤
      centralizer (Source.weakClosureZero (T : Subgroup G) V : Set G))
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (ha : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaClosure T H : Set G))
    (D_H : Subgroup G) (hDH : D_H ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (D_H.subgroupOf (H ⊓ normalizer (L : Set G)))) :
    Source.NormalComponentIn H (outsideResidual H) ∧
    outsideResidual H ⊓ centralizer (omegaClosure T H : Set G) =
      (outsideResidual H).pCoreIn 2 ∧
    Function.Injective (residualQuotientAction T H s.outside.1.1.2) ∧
    ClassicalGroup.IsPSL (residualStar T H) 2 (2 ^ S.field.degree) ∧
    oddCartanPart D_H ≤ L ∧
    omegaCenter T ⊓ centralizer (L : Set G) = ⊥ ∧
    V ⊓ centralizer (L : Set G) = ⊥ ∧
    omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥ ∧
    V.map (MulAut.conj g).toMonoidHom = V ∧
    (∃ P : Sylow 2 (residualStar T H),
      (P : Subgroup (residualStar T H)).map (residualStar T H).subtype =
        (V.subgroupOf H).map (starProjection T H)) ∧
    D.centralQuotientPreimage U₁ = ⁅D.centralQuotientPreimage U₁,oddCartanPart D_H⁆ ∧
    D.centralQuotientPreimage U₁ ≤ omegaClosure T H ∧
    ∃ X : Subgroup G, IsCartan T L X ∧ oddCartanPart D_H ≤ X := by
  obtain ⟨hWT,⟨cK⟩,P,hP,_⟩ := selected_natural_action s g hg ha hs hmodel
  have s' : Hypothesis1131At D S (cL.binarySubspace (f.space 0)) H := hline ▸ s
  obtain ⟨hDL,_,X,hX,hDX⟩ := Hall.source_hall_cartan_of_hStar cL f s' cK D_H hDH hHall halt hres
  obtain ⟨hz,hv,_,_,_,_⟩ := source_component_module s cK D_H hDH hHall hDL
  have hcases := source_cartan_dichotomy cL f hu hG2 s cK D_H X hDH hHall hX hDX
  have hk := (Hall.source_fixed_spaces s hWT cK D_H hDH hHall hcases).2.2
  obtain ⟨hcomm,hVH⟩ := source_line_of_fixed_spaces cL f hu s cK D_H X hDH hHall hX hDX hv hk
  have hVi : f.Vi 0 = D.centralQuotientPreimage U₁ := by rw [hline]; rfl
  rw [hVi] at hcomm hVH
  have hAW : V.map (MulAut.conj g).toMonoidHom ≤ Source.weakClosureZero (T : Subgroup G) V :=
    le_sSup ⟨g,rfl,hg⟩
  have hcontain : D.centralQuotientPreimage U₁ ≤
      omegaClosure T H ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) :=
    le_inf hVH (hweak.trans (centralizer_le hAW))
  let := source_residualQuotient_simple hmodel
  obtain ⟨_,he,hP'⟩ := source_seed_star_sylow_transvections cL f hline hG2 s p hcounter
    halt hparameters g cK hv hk (hg.trans s.outside.1.1.2) P hP D_H hDH hHall hcontain hcomm
  exact ⟨hcomponent,source_action_kernel s hmodel,
    source_faithful_quotient_action s hmodel,source_star_model s hmodel,
    hDL,hz,hv,hk,he,⟨P,hP'⟩,hcomm,hVH,X,hX,hDX⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
