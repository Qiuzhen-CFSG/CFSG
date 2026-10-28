module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.CubicComponent

/-! The original paired block cannot lie in a component whose cubic
centralizers admit no alternating-five block with elementary module of order
sixteen. The literal quotient configuration supplies that full block, so a
model may use a weaker order obstruction than absence of elementary sixteen.
Source: Aschbacher–Smith 2.4.25, printed pp.542–543. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]
variable {M M₀ : Subgroup G} {d : MinimalBlockSetup M}

theorem AlternatingPairSourceSetup.cubic_block_centralizer_overcomponent_false
    (c : AlternatingPairSourceSetup d M₀)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    [IsQuasisimple D] (hz : center D = ⊥) (hr : 2 ≤ primeRank 3 D)
    (ho : IsPGroup 2 (MulAut.Outer D))
    (hno : ∀ A : Subgroup D, IsAlternatingBlock A 5 →
      Nat.card ((blockU A).map A.subtype) = 16 →
      ∀ b : D, orderOf b = 3 → b ∈ centralizer (A : Set D) → False) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let GI := normalizer (Phi S L : Set G)
    ∀ (K : Subgroup GI), IsComponent GI K → L.subgroupOf GI ≤ K →
      Nonempty ((K ⧸ pCore 2 K) ≃* D) → False := by
  intro S L GI K hK hLK ⟨e⟩
  obtain ⟨hA,hcard,_,b,hb,hbA⟩ :=
    c.phi_component_cubic_configuration hG T hM hTM hu hST hSM hMT hi hz hr ho K hK hLK e
  exact hno _ hA hcard b hb hbA

end CFSG.Quasithin.Chapter2
