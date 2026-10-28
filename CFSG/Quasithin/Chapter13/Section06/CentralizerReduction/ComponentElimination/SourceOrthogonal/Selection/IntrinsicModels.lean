module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.IntrinsicModels.ContainingFamily
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.IntrinsicModels.Quotients
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.IntrinsicModels.Catalogue
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.Comparison

/-!
# Intrinsic rank-four models and their residual consumer

The actual component D furnished by 1.2.4 belongs to Y_z: its star image
lies in J(G_v)* and the central Fitting equality makes it quasisimple.
Applying the rank-four action selection to K and D gives their two action
markings. The quotient construction in the sibling module turns these into
intrinsic two-core markings, retaining the literal action maps and kernels.
The existing Comparison theorem then identifies K with D and with the
ambient prime-to-three residual.

The catalogue comparison is proved in Catalogue and discharged in the
`_of_a36` theorems below. They construct the intrinsic markings and identify
the full action kernels with the intrinsic two-cores. The original conditional
interfaces are preserved. The universal rank-four action selection remains
the intermediate result of the parent source-selection task. The universal
A.3.6, A.3.8 and A.3.12 inputs and the genuine earlier 13.6.2–16 outputs retain
their original source obligations; these helpers do not assert the assembled
source theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.23, printed p.933/PDF p.950.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection
open ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal rank-four action marking gives an intrinsic two-core marking.
The complete A.3.6 catalogue comparison is supplied by its proved theorem. -/
theorem exists_intrinsic_four_marking_of_a36 {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK 𝒦 (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hK : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (e : plusImage K L T z v hL hz K ≃* SL(4, ZMod 2)) :
    ∃ eK : K ⧸ pCore 2 K ≃* SL(4, ZMod 2),
      ∀ k : K, eK (QuotientGroup.mk' _ k) =
        e (intrinsicToPlus K L T z v hK.1.1 hL hz k) :=
  exists_intrinsic_four_marking hA36 a36RankFourRecognition
    K L T z v hlocal hL hz hK hR e

/-- The original action kernel is exactly O₂(K), with no remaining
catalogue-recognition premise. This concerns W_K and the literal plus map. -/
theorem intrinsic_action_kernel_eq_twoCore_of_a36 {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK 𝒦 (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hK : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (e : plusImage K L T z v hL hz K ≃* SL(4, ZMod 2)) :
    (centralizer (WK K L T z v : Set G)).subgroupOf K = pCore 2 K :=
  intrinsic_action_kernel_eq_twoCore hA36 a36RankFourRecognition
    K L T z v hlocal hL hz hK hR e

/-- Conditional final application of the intrinsic markings. The actual
containing component, its Y_z membership, both markings, component equality,
and the literal prime-to-three residual equality are constructed together. -/
theorem exists_containing_models_and_residual {𝒦 : GroupClass.{u}}
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ (T : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents T →
      ∃! D : Subgroup X, D.IsCComponent ∧ B ≤ D)
    (hA38 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ D : Subgroup X, D.IsCComponent →
      D.Normal ∨ (normalizer (D : Set X)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel D)
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (hrecognition : A36RankFourRecognition.{u})
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK 𝒦 (Gv v)) (hcore : Gv v ∈ Chapter1.H G)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hKn : Tv T v ≤ normalizer (K : Set G))
    (hLK : Lv L v ≤ K) (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    (h16 : ∀ B ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (B : Set G) → ¬ B ≤ centralizer ({z} : Set G) →
      ⁅B, Stellmacher.elementaryAbelianMaxJ (Tv T v)⁆ = B)
    (hstarCore : pCore 2 (Gstar z v) = ⊥)
    (hfit : fittingSubgroup (JGstar z v) = center (JGstar z v))
    (hR : ∀ B ∈ Yz L T z v, pCore 2 (Gplus B L T z v hL hz) = ⊥)
    (hfour : ∀ B ∈ Yz L T z v,
      Nonempty (plusImage B L T z v hL hz B ≃* SL(4, ZMod 2))) :
    ∃ D : Subgroup G, D ∈ Chapter1.cComponentsIn (Gv v) ∧ D ∈ Yz L T z v ∧
      K ≤ D ∧ Gv v ≤ normalizer (D : Set G) ∧
      Nonempty (K ⧸ pCore 2 K ≃* SL(4, ZMod 2)) ∧
      Nonempty (D ⧸ pCore 2 D ≃* SL(4, ZMod 2)) ∧ K = D ∧
      K = (primeToResidual 3 (Gv v)).map (Gv v).subtype := by
  obtain ⟨D, hD, hKD, hDn⟩ := exists_containing_component hA312 hA38
    K L T z v hlocal hSyl hK hKn
  have hDY := containing_mem_Yz K D L T z v hD hKD hDn hcore hSyl hLK hmove
    h16 hstarCore hfit
  obtain ⟨eplusK⟩ := hfour K hK
  obtain ⟨eplusD⟩ := hfour D hDY
  obtain ⟨eK, _⟩ := exists_intrinsic_four_marking hA36 hrecognition
    K L T z v hlocal hL hz hK (hR K hK) eplusK
  obtain ⟨eD, _⟩ := exists_intrinsic_four_marking hA36 hrecognition
    D L T z v hlocal hL hz hDY (hR D hDY) eplusD
  exact ⟨D, hD, hDY, hKD, hDn, ⟨eK⟩, ⟨eD⟩,
    eq_containing_component K D T v hD hKD hDn hSyl hKn eK eD,
    residual_eq_of_containing_component_models K D T v hK.1 hD hKD hDn hSyl hKn
      eK eD (hlocal.stronglyQuasithin 3 (by decide) (by decide))⟩

/-- The intrinsic-model assembly with the A.3.6 catalogue comparison discharged.
It constructs the actual containing D, proves D ∈ Y_z, marks both intrinsic
quotients, and applies Comparison to obtain K = D and the source residual.
The rank-four selection for Y_z is an intermediate premise to be discharged
by the parent source-selection theorem, not an additional source hypothesis. -/
theorem exists_containing_models_and_residual_of_a36 {𝒦 : GroupClass.{u}}
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ (T : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents T →
      ∃! D : Subgroup X, D.IsCComponent ∧ B ≤ D)
    (hA38 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ D : Subgroup X, D.IsCComponent →
      D.Normal ∨ (normalizer (D : Set X)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel D)
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK 𝒦 (Gv v)) (hcore : Gv v ∈ Chapter1.H G)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hKn : Tv T v ≤ normalizer (K : Set G))
    (hLK : Lv L v ≤ K) (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    (h16 : ∀ B ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (B : Set G) → ¬ B ≤ centralizer ({z} : Set G) →
      ⁅B, Stellmacher.elementaryAbelianMaxJ (Tv T v)⁆ = B)
    (hstarCore : pCore 2 (Gstar z v) = ⊥)
    (hfit : fittingSubgroup (JGstar z v) = center (JGstar z v))
    (hR : ∀ B ∈ Yz L T z v, pCore 2 (Gplus B L T z v hL hz) = ⊥)
    (hfour : ∀ B ∈ Yz L T z v,
      Nonempty (plusImage B L T z v hL hz B ≃* SL(4, ZMod 2))) :
    ∃ D : Subgroup G, D ∈ Chapter1.cComponentsIn (Gv v) ∧ D ∈ Yz L T z v ∧
      K ≤ D ∧ Gv v ≤ normalizer (D : Set G) ∧
      Nonempty (K ⧸ pCore 2 K ≃* SL(4, ZMod 2)) ∧
      Nonempty (D ⧸ pCore 2 D ≃* SL(4, ZMod 2)) ∧ K = D ∧
      K = (primeToResidual 3 (Gv v)).map (Gv v).subtype :=
  exists_containing_models_and_residual hA312 hA38 hA36 a36RankFourRecognition
    K L T z v hlocal hcore hSyl hL hz hK hKn hLK hmove h16 hstarCore hfit hR hfour

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection
