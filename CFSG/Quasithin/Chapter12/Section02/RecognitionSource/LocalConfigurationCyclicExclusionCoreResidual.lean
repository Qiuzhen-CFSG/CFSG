module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicExclusionCoreAction
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The normal Frattini-module subgroup in the extraspecial branch

The embedded derived subgroup of P is Φ(P), and W=[W,P]. Thus the
derived subgroup of the literal residual P W is exactly Y=Φ(P)W.
Residual normality makes Y normal in H, and then C_{O₂(H)}(Y) is normal
in H. In the binary-three branch the preceding faithful-module argument
makes W centralize O₂(H), so this centralizer is C_{O₂(H)}(Φ(P)).

The actual source consumer is LocalConfigurationCyclicExclusionCoreAssembly.
The remaining numerical and component-module contradiction stay with
qt-d-12213-cyclic-block; no extraspecial exclusion is asserted here.
Source: Aschbacher–Smith, 12.2.23, printed p.804.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U W : Subgroup G} {d p : ℕ} {g v : G}
namespace InvariantOddLocalAnalysis
variable (S : InvariantOddLocalAnalysis T L V d p H P U W g v)
include S

/-- The derived subgroup of the literal two-residual is Φ(P)W. -/
theorem extraspecial_residual_derived (he : IsExtraspecial p P) :
    ⁅P ⊔ W, P ⊔ W⁆ = (frattini P).map P.subtype ⊔ W := by
  let : Fact p.Prime := ⟨S.prime⟩
  let := he
  let Φ := (frattini P).map P.subtype
  let Y := Φ ⊔ W
  let K := P ⊔ W
  have hPP : ⁅P, P⁆ = Φ := by
    have hh := map_commutator (f := P.subtype) (⊤ : Subgroup P) ⊤
    rw [← MonoidHom.range_eq_map, P.range_subtype] at hh
    change (_root_.commutator P).map P.subtype = ⁅P, P⁆ at hh
    change ⁅P, P⁆ = (frattini P).map P.subtype
    rw [IsExtraspecial.frattini_eq_center (p := p),
      ← IsExtraspecial.commutator_eq_center (p := p)]
    exact hh.symm
  have hPW : P ≤ normalizer (W : Set G) :=
    (S.overgroup ▸ le_sup_left).trans S.normalizes
  have hPΦ : P ≤ normalizer (Φ : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (frattini P))
  have hPY : P ≤ normalizer (Y : Set G) :=
    (le_inf hPΦ hPW).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hKY : K ≤ normalizer (Y : Set G) :=
    sup_le hPY (le_sup_right.trans Y.le_normalizer)
  have hPK : ⁅P, K⁆ ≤ Y := by
    rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal K P W P Y hKY le_sup_left le_sup_right
      (hPP.le.trans le_sup_left) (S.moved.le.trans le_sup_right)
  have hWK : ⁅W, K⁆ ≤ Y := by
    rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal K P W W Y hKY le_sup_left le_sup_right
      (by rw [commutator_comm]; exact S.moved.le.trans le_sup_right)
      ((le_normalizer_iff_commutator_le_left.mp W.le_normalizer).trans le_sup_right)
  apply le_antisymm
  · exact commutator_sup_le_of_relative_normal K P W K Y hKY le_sup_left le_sup_right hPK hWK
  · apply sup_le
    · exact hPP.ge.trans (commutator_mono
        (show P ≤ P ⊔ W from le_sup_left) (show P ≤ P ⊔ W from le_sup_left))
    · exact S.moved.ge.trans (commutator_mono
        (show W ≤ P ⊔ W from le_sup_right) (show P ≤ P ⊔ W from le_sup_left))

/-- The subgroup Φ(P)W is normal relative to the original H. -/
theorem extraspecial_frattini_module_normal (he : IsExtraspecial p P) :
    H ≤ normalizer (((frattini P).map P.subtype ⊔ W : Subgroup G) : Set G) := by
  have hHK : H ≤ normalizer ((P ⊔ W : Subgroup G) : Set G) := by
    rw [← S.residual]
    exact le_normalizer_embedded_pResidual 2 H
  rw [← S.extraspecial_residual_derived he]
  intro h hh
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hHK hh)]

/-- The centralizer of Φ(P)W inside O₂(H) is normal in H. -/
theorem extraspecial_core_centralizer_normal (he : IsExtraspecial p P) :
    H ≤ normalizer ((H.pCoreIn 2 ⊓ centralizer
      (((frattini P).map P.subtype ⊔ W : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  exact (le_inf (H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
    ((S.extraspecial_frattini_module_normal he).trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf

/-- In the binary-three branch, centralizing Φ(P) inside O₂(H) centralizes Φ(P)W. -/
theorem extraspecial_binary_three_core_centralizer
    (A : NaturalLocalAnalysis T L V d) (he : IsExtraspecial p P)
    (hcard : Nat.card P = p ^ 3)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥)
    (hp : p = 3) (hW : Nat.card W = 64) :
    H.pCoreIn 2 ⊓ centralizer (((frattini P).map P.subtype ⊔ W : Subgroup G) : Set G) =
      H.pCoreIn 2 ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) := by
  have hc : H.pCoreIn 2 ≤ centralizer (W : Set G) :=
    le_centralizer_iff.mp (S.extraspecial_binary_three_module_centralizes_core A he hcard hf hp hW)
  apply le_antisymm
  · exact inf_le_inf_left _ (centralizer_le (show (frattini P).map P.subtype ≤
      (frattini P).map P.subtype ⊔ W from le_sup_left))
  · rintro x ⟨hx, hΦ⟩
    refine ⟨hx, ?_⟩
    apply mem_centralizer_iff.mpr
    intro y hy
    have hle : (frattini P).map P.subtype ⊔ W ≤ centralizer ({x} : Set G) :=
      sup_le (fun a ha => mem_centralizer_singleton_iff.mpr (hΦ a ha))
        (fun a ha => mem_centralizer_singleton_iff.mpr (hc hx a ha))
    exact mem_centralizer_singleton_iff.mp (hle hy)

/-- The literal Frattini centralizer in the two-core is H-normal in the
binary-three branch, as needed by the final T-orbit contradiction. -/
theorem extraspecial_binary_three_core_centralizer_normal
    (A : NaturalLocalAnalysis T L V d) (he : IsExtraspecial p P)
    (hcard : Nat.card P = p ^ 3)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥)
    (hp : p = 3) (hW : Nat.card W = 64) :
    H ≤ normalizer ((H.pCoreIn 2 ⊓ centralizer
      (((frattini P).map P.subtype : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  rw [← S.extraspecial_binary_three_core_centralizer A he hcard hf hp hW]
  exact S.extraspecial_core_centralizer_normal he

end InvariantOddLocalAnalysis
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
