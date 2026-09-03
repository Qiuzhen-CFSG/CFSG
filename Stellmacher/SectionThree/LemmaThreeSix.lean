module

public import Stellmacher.SectionThree.LemmaThreeFive


open scoped BigOperators Pointwise

namespace Stellmacher.SectionThree

universe u

public structure LemmaThreeSixConclusion
    {G : Type u} [Group G] [Finite G]
    (S P Z T A : Subgroup G) (a : G) : Prop where
  exists_witness :
    ∃ x : P, ∃ L A₀ : Subgroup G,
      L = A ⊔ A.conjBy (x : G) ∧
      A₀ ≤ A ∧
      (A : Set G) = (Subgroup.zpowers a : Set G) * (A₀ : Set G) ∧
      ∃ p n : ℕ, Nat.Prime p ∧ Odd p ∧
        ∃ Ebar Abar : Subgroup (L ⧸ pCore 2 L),
          Nonempty (Ebar ≃* DihedralGroup (p ^ n)) ∧
          Abar = (A₀.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L)) ∧
          IsInternalDirectProductFamily
            (⊤ : Subgroup (L ⧸ pCore 2 L))
            (fun i : Bool => if i then Ebar else Abar) ∧
          ¬ twoResidualAmbient L ≤ phiTwo (twoResidualAmbient P) ∧
          (∀ z₁ z₂ : G,
            z₁ ∈ conjugateOrbitSet Z L → z₂ ∈ conjugateOrbitSet Z L →
            ∃ t : L, IsInvolution (t : G) ∧
              (t : G) * z₁ * (t : G)⁻¹ = z₂ ∧
              (t : G) * z₂ * (t : G)⁻¹ = z₁) ∧
          twoResidualAmbient L ≤ ⁅twoResidualAmbient L, T⁆

/-! **Stellmacher (3.6).** -/
public theorem lemma_three_six
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (Z T : Subgroup G)
    (hZ : Z ≤ S ∧ (Z.subgroupOf S).Normal)
    (hT : T ≤ S ∧ (T.subgroupOf S).Normal)
    (A : Subgroup G) (hA : A ≤ S)
    (a : G) (haA : a ∈ A) (haCore : a ∉ twoCoreAmbient P)
    (hPhi : frattiniAmbient A ≤ twoCoreAmbient P)
    (hsolv : Group.IsSolvable P)
    (hZcore : Z ≤ twoCoreAmbient P)
    (hTcore : ¬ T ≤ twoCoreAmbient P) :
    LemmaThreeSixConclusion S P Z T A a := by
  sorry

end Stellmacher.SectionThree
