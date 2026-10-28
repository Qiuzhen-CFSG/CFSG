module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.Base
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingFixedPhi
public import CFSG.Quasithin.Chapter1.Section01Inheritance

/-! The actual nontrivial fixed Frattini subgroup gives the two-local G_I
and its original local pair. This establishes G_I∈Γ on the same selected
blocks and escaping conjugator used in source 2.4.25, printed p.542. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.ConjugateSource
open AlternatingFixedPhi
variable {G : Type*} [Group G] [Finite G] {M M₀ : Subgroup G}
  {d : MinimalBlockSetup M}

theorem AlternatingPairSourceSetup.phi_normalizer_source
    (c : AlternatingPairSourceSetup d M₀)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let F := Phi S L
    let GI := normalizer (F : Set G)
    F ≠ ⊥ ∧ IsTwoLocal GI ∧ GI ∈ gamma (Chapter1.He G) M ∧
      L ≤ centralizer (F : Set G) ∧ c.x ∈ GI ∧
      (SI S L,d.H ⊓ GI) ∈ localPairsIn (Chapter1.He G) M GI := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let F := Phi S L
  let GI := normalizer (F : Set G)
  let X := d.H ⊓ GI
  have hFS : F ≤ S := inf_le_left.trans ((P_le_I S L).trans (inf_le_left.trans inf_le_left))
  have hFH : F ≤ d.H := hFS.trans (map_subtype_le _)
  have hFp : IsPGroup 2 F := c.marked₁.twoGroup.to_le hFS
  have hF : F ≠ ⊥ := Phi_ne_bot c.marked₁ c.marked₂
  have hloc : IsTwoLocal GI := ⟨F,hF,hFp,rfl⟩
  have hLF : L ≤ centralizer (F : Set G) := le_centralizer_iff.mp (Phi_le_centralizer S L)
  have hLX : L ≤ X := le_inf (map_subtype_le _) (hLF.trans (Subgroup.centralizer_le_normalizer _))
  have hFX : F ≤ X := le_inf hFH F.le_normalizer
  have hXe : X ∈ Chapter1.He G := Chapter1.normalizer_mem_He_of_isPGroup
    d.mem_gammaEvenZero.2 hFp hFH
  have hXq : twoCore X ≠ ⊥ := by
    intro he
    exact hF (le_bot_iff.mp ((le_pCoreIn_of_normalizes hFp hFX inf_le_right).trans he.le))
  have hSIb := (c.stabilizer_base hG T hM hTM hu hST hSM hMT hi).2.2.2
  have hSIX : SI S L ≤ X := le_inf (inf_le_left.trans (map_subtype_le _))
    ((normalizer_Phi_eq c.marked₁ c.marked₂).ge.trans inf_le_right)
  have hpair : (SI S L,X) ∈ localPairsIn (Chapter1.He G) M GI :=
    ⟨⟨hSIb,hXe,hXq,hSIX,fun h => d.outside (hLX.trans h)⟩,inf_le_right⟩
  have hx : c.x ∈ GI := conjugator_normalizes_Phi c.marked₁ c.marked₂ c.x
    (c.original.R_normal c.x_mem) c.noncommuting
  exact ⟨hF,hloc,⟨Chapter1.mem_H_of_isTwoLocal hloc,⟨_,hpair⟩⟩,hLF,hx,hpair⟩
end CFSG.Quasithin.Chapter2
