module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.ActionEscape
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.PairQuotient
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalSieve

/-!
# Residual quotient and quotient-action reductions of local Cartan escape

The moved seed has whole residual quotient A₅ × A₅. Otherwise the
residual is quasisimple modulo its two-core and has a proper normal
containing component. In either case the original containing component's
normal Sylow orbit supports the literal conjugation action modulo its
two-core. The escaping Cartan has a nontrivial cyclic odd image, is
normalized by the right Hall image, and still escapes the residual image.

This proves the passage to the automorphism group used on p.636 without
assuming a particular containing model. The paired and unpaired model
exclusions and the escaping cubic remain with this classification owner.
Source: Aschbacher--Smith, 5.1.10--13, printed pp.634--637.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The original residual retains both factors in the moved branch. -/
theorem localCartan_escape_residual_quotient
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃*
      (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) ∨
      (IsQuasisimple ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ∧
        residual H ∈ Chapter1.L G (T : Subgroup G) ∧
        ∃ X : Subgroup G, X ≤ Y ∧ (X.subgroupOf Y).IsCComponent ∧
          (X.subgroupOf Y).Normal ∧ residual H < X) := by
  obtain ⟨_,K,hKH,hK,hq,_,hl,ho,hm | hs⟩ :=
    localCartan_escape_seed_reduction h hH hgen c hY hescape
  · exact Or.inl (LocalSieve.moved_seed_residual_quotient h.qtke hKH hH.1.1.2
      hH.1.1.1 hK ho hm.1.ne hm.2.1)
  · obtain ⟨he,hX⟩ := hs
    subst K
    let := hq
    let e := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
    exact Or.inr ⟨IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm,hl,hX⟩

/-- The actual normal containing orbit supplies an escaping odd cyclic quotient actor. -/
theorem localCartan_exists_escaping_component_action
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ C : Subgroup Y, C.IsCComponent ∧
      residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
      ∃ hn : ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal,
        let J := (componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y
        letI : J.Normal := hn
        let f := normalQuotientAction J (pCore 2 J)
        let Dbar := (A.subgroupOf Y).map f
        let Bbar := (B.subgroupOf Y).map f
        IsCyclic Dbar ∧ Odd (Nat.card Dbar) ∧
          Bbar ≤ normalizer (Dbar : Set (MulAut (J ⧸ pCore 2 J))) ∧
          ¬ Dbar ≤ normalizer (((residual H).subgroupOf Y).map f : Set _) ∧
          Dbar ≠ ⊥ ∧ ¬ Dbar ≤ Bbar := by
  obtain ⟨K,_,_,_,_,_,_,C,hC,_⟩ := LocalSieve.exists_escape_seed_embedding
    h.qtke h.sylow_normalizes hH hgen hY hescape
  refine ⟨C,hC.1,hC.2.2.1,hC.2.2.2,?_⟩
  let J := (componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y
  let : J.Normal := hC.2.2.2
  exact LocalSieve.cartan_action_escape h hH hgen c hY hescape J
    (comap_mono hC.2.2.1.le)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
