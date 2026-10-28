module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14Generation
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.CubicCentralizer

/-!
# Cubic centralizers in the dimension-four source branch

The original source-local data construct an actual order-three element
in a marked SL₂(3) factor. Its ambient centralizer has the proved odd-core
decomposition, the opposite quaternion Sylow subgroup, and the fixed-line
and inversion identities, with the literal embeddings retained.

This supplies the three-local centralizer input to I.4.5. The ambient
G₂(3) recognition callback remains with `qt-i45-g2-recognition`;
`qt-d-14414-g2-local-source` produces SourceLocalData, and
`qt-d-14414-g2-source` owns final assembly. Source: Aschbacher–Smith
I.4.5, p.417, and14.4.3–5, pp.1007–1008; Fong–Wong §3B–C, p.156.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource Chapter14.Section04.CaseOneGeometry
open Chapter14.Section04.CaseOneDimensionFour Chapter14.Section04.DimensionFour
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_cubic_centralizer_structure (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (x : c.H₁), orderOf x = 3 ∧
      cubicCentralizer c x = cubicOddCore c x ⊔ c.H₂.map c.H.subtype ∧
      cubicOddCore c x ⊓ c.H₂.map c.H.subtype = ⊥ ∧
      cubicOddCore c x ⊓ c.H = zpowers ((x:c.H):G) ∧
      (∃ P : Sylow 2 (cubicCentralizer c x),
        (P : Subgroup (cubicCentralizer c x)).map (cubicCentralizer c x).subtype =
          (c.H₂.pCoreIn 2).map c.H.subtype ∧ Nonempty (P ≃* QuaternionGroup 2)) ∧
      (∀ z : G, orderOf z = 2 → c.H = centralizer ({z} : Set G) →
        (∀ k ∈ cubicOddCore c x, z*k*z⁻¹*k ∈ zpowers ((x:c.H):G)) ∧
          ⁅cubicOddCore c x,cubicOddCore c x⁆ ≤ zpowers ((x:c.H):G)) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  have hc : Nat.card c.H₁ = 24 := (Nat.card_congr c.H₁_model.some.toEquiv).trans
    GLS3.Chapter5.SchurPresentation.sl23_card_eq
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := c.H₁) 3 (by rw [hc]; decide)
  exact ⟨c,x,hx,cubic_centralizer_split c x hx,cubic_oddCore_inf_factor c x,
    cubic_oddCore_fixed c x hx,cubic_quaternion_sylow c x hx,
    cubic_oddCore_inversion c x hx⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
