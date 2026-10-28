module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14CubicCentralizer
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.CubicNormalizer

/-!
# Cubic normalizers in the dimension-four source branch

The original SourceLocalData produce two actual cubic lines and a common
Klein four torus in H. Their ambient normalizers have the odd-core times
opposite-factor times torus form, with the original H₁/H₂ embeddings.
The local normalizers have order144; the ambient orders are48 times the
respective odd-core orders. The first formula also records the literal
Frattini supplement inside the given involution centralizer.

This proves the normalizer input from Fong–Wong §3B(ii), p.156, in the
Chapter14 source setting. The prime-three multiplicity and ambient G₂(3)
recognition remain with `qt-i45-g2-recognition`. The consolidated
`qt-d-14414-g2-source` produces SourceLocalData and owns its final discharge.
Sources: Aschbacher–Smith I.4.5, p.417, and14.4.3–5, pp.1007–1008.
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

theorem source_cubic_normalizers (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c), IsKleinFour t.torus ∧
      cubicNormalizer c t.x = cubicOddCore c t.x ⊔ (c.H ⊓ cubicNormalizer c t.x) ∧
      cubicNormalizer c t.x = cubicOddCore c t.x ⊔ c.H₂.map c.H.subtype ⊔ t.torus.map c.H.subtype ∧
      cubicNormalizer (swapFactors c) t.y = cubicOddCore (swapFactors c) t.y ⊔
        c.H₁.map c.H.subtype ⊔ t.torus.map c.H.subtype ∧
      Nat.card (normalizer (zpowers (t.x:c.H) : Set c.H)) = 144 ∧
      Nat.card (normalizer (zpowers (t.y:c.H) : Set c.H)) = 144 ∧
      Nat.card (cubicNormalizer c t.x) = Nat.card (cubicOddCore c t.x) * 48 ∧
      Nat.card (cubicNormalizer (swapFactors c) t.y) = Nat.card (cubicOddCore (swapFactors c) t.y) * 48 := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  exact ⟨c,t,t.torus_kleinFour,cubic_normalizer_split c t.x t.x_order,
    t.left_ambient_normalizer,t.right_ambient_normalizer,
    t.left_local_normalizer_card,t.right_local_normalizer_card,
    t.left_ambient_normalizer_card,t.right_ambient_normalizer_card⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
