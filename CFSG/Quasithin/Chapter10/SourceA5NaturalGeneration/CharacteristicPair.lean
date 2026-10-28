module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.FixedCenter
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPair
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedBlockSteps
/-!
# One intrinsic characteristic pair for the original two overgroups

Choose the universal C.1.18 pair on Baum(T) once, and restrict its first
member to the original Sylow center. Its first member remains nontrivial.
The two actual local-class embeddings give alternatives for this same pair.
Vanishing fixed centers eliminate centrality; original two-local uniqueness
eliminates simultaneous normality of its second member.

The selected residual is the actual two-perfect component. Transporting its
short structure and retaining original subnormality yields a block in the
original local ambient group. Thus the final consumer needs genuine
C.1.17 local-class proofs, not separately chosen matching alternatives.
Source: Aschbacher–Smith C.1.18–19, C.1.26 and 10.2.3(4), pp.126–132,746.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open ChapterB Chapter3.Section02 ChapterC.GlaubermanNiles ChapterC.RankOne.ChiProduct
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- One of the actual selected local groups has the C.1.18 block alternative. -/
theorem source_hstar_selected_block_alternative {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZL : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hZH : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥)
    (NL NH : Subgroup G)
    (hBL : baumann (T : Subgroup G) ≤ NL) (hBH : baumann (T : Subgroup G) ≤ NH)
    (hLgen : localOrbit T L ≤ NL ⊔ (T : Subgroup G))
    (hHgen : H ≤ NH ⊔ (T : Subgroup G))
    (hlocalL : InLocalClass (inclusion hBL))
    (hlocalH : InLocalClass (inclusion hBH)) :
    BlockAlternative NL ∨ BlockAlternative NH := by
  have hTne : (T : Subgroup G) ≠ ⊥ := fun he =>
    D.seed_ne_bot (bot_unique (D.seed_le_sylow.trans he.le))
  obtain ⟨P,hP,hfirst⟩ := FixedPair.exists_uniform_pair.{u,u} T hTne
  let B := baumann (T : Subgroup G)
  let C₁ := FixedPair.firstSeed T P
  let C₂ := P.second.map B.subtype
  have hC₁Z : C₁ ≤ omegaOneCenterAmbient (T : Subgroup G) := inf_le_left
  have hTC₁ : (T : Subgroup G) ≤ centralizer (C₁ : Set G) := by
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp (hC₁Z hz)).2.2 t ht).symm
  have hC₂T : C₂ ≤ (T : Subgroup G) := (map_subtype_le P.second).trans inf_le_left
  let : P.second.Characteristic := P.second_characteristic
  have hTC₂ : (T : Subgroup G) ≤ normalizer (C₂ : Set G) :=
    ((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)).trans
      (normalizer_le_normalizer_characteristic_image _ P.second)
  have hC₂ne : C₂ ≠ ⊥ := fun he => P.second_ne_bot
    ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
  have first {N : Subgroup G} (hBN : B ≤ N)
      (hc : P.first.map (inclusion hBN) ≤ center N) :
      N ≤ centralizer (C₁ : Set G) := by
    intro n hn z hz
    obtain ⟨b,hb,rfl⟩ := hz.2
    have he := mem_center_iff.mp (hc (mem_map_of_mem (inclusion hBN) hb)) (⟨n,hn⟩ : N)
    exact (congrArg N.subtype he).symm
  have second {N : Subgroup G} (hBN : B ≤ N)
      (hn : (P.second.map (inclusion hBN)).Normal) : N ≤ normalizer (C₂ : Set G) := by
    let := hn
    have h := (P.second.map (inclusion hBN)).le_normalizer_map N.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,map_map] at h
    exact h
  have hln : NL ≤ normalizer (C₂ : Set G) ∨ BlockAlternative NL := by
    rcases hP NL (inclusion hBL) hlocalL with hc | hn | hb
    · have hz : C₁ ≤ centralizer (localOrbit T L : Set G) :=
        le_centralizer_iff.mpr (hLgen.trans (sup_le (first hBL hc) hTC₁))
      exact (hfirst (bot_unique ((le_inf hC₁Z hz).trans hZL.le))).elim
    · exact Or.inl (second hBL hn)
    · exact Or.inr hb
  rcases hln with hnL | hb
  · rcases hP NH (inclusion hBH) hlocalH with hc | hn | hb
    · have hz : C₁ ≤ centralizer (H : Set G) :=
        le_centralizer_iff.mpr (hHgen.trans (sup_le (first hBH hc) hTC₁))
      exact (hfirst (bot_unique ((le_inf hC₁Z hz).trans hZH.le))).elim
    · have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
        (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
        (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
        D.simpleQTKE T D.maximal
      have hN : normalizer (C₂ : Set G) ≤ D.maximalLocal :=
        normalizer_le_of_unique_maximalTwoLocal (D.lemma_3_2_3_uniqueness hu).2.2
          (T.isPGroup'.to_le hC₂T) hC₂ne
          (sup_le (hLgen.trans (sup_le hnL hTC₂)) hTC₂)
      exact (hH.1.2 (hHgen.trans ((sup_le (second hBH hn) hTC₂).trans hN))).elim
    · exact Or.inr hb
  · exact Or.inl hb

private theorem source_selected_block_in_ambient
    {K A : Subgroup G} (hKA : K ≤ A) (hK : (K.subgroupOf A).IsCComponent)
    (hBK : baumann (T : Subgroup G) ≤ normalizer (K : Set G))
    (hb : BlockAlternative (K ⊔ baumann (T : Subgroup G) : Subgroup G)) :
    ChapterC.IsBlock (K.subgroupOf A) := by
  let : Group.IsPerfect K := by
    let := hK.perfect
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKA).toMonoidHom)
      (subgroupOfEquivOfLe hKA).surjective
  have hpK : IsPPerfect 2 K := by
    intro Q hQ hp
    let := hQ
    let : Group.IsNilpotent (K ⧸ Q) := hp.isNilpotent
    apply top_unique
    rw [←solvableResidual_eq_top (G := K)]
    exact solvableResidual_le_of_solvable_quotient Q
  let N := K ⊔ baumann (T : Subgroup G)
  let e := ((pResidual 2 N).equivMapOfInjective N.subtype N.subtype_injective).trans
    (MulEquiv.subgroupCongr
      (SelectedRankOne.selected_component_residual_map T K hpK hBK))
  have hs : ChapterC.IsShort K := ChapterC.RankOne.Solvable.isShort_of_equiv e hb.1.short
  exact ⟨inferInstance,
    ChapterC.RankOne.Solvable.isShort_of_equiv (subgroupOfEquivOfLe hKA).symm hs,hK.subnormal⟩

/-- Apply the single characteristic pair and return a block in the original local ambient. -/
theorem source_hstar_one_block_of_localClass {H K : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZL : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hZH : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hBL : baumann (T : Subgroup G) ≤ normalizer (L : Set G))
    (hBK : baumann (T : Subgroup G) ≤ normalizer (K : Set G))
    (hHgen : H ≤ K ⊔ (T : Subgroup G))
    (hlocalL : InLocalClass (inclusion (show baumann (T : Subgroup G) ≤
      L ⊔ baumann (T : Subgroup G) from le_sup_right)))
    (hlocalK : InLocalClass (inclusion (show baumann (T : Subgroup G) ≤
      K ⊔ baumann (T : Subgroup G) from le_sup_right))) :
    ChapterC.IsBlock (L.subgroupOf (localJoin T L)) ∨ ChapterC.IsBlock (K.subgroupOf H) := by
  have hLgen : localOrbit T L ≤ (L ⊔ baumann (T : Subgroup G)) ⊔ (T : Subgroup G) := by
    have hh : localOrbit T L ≤ L ⊔ (T : Subgroup G) := by
      rw [←componentOrbit_sup]
      exact le_sup_left
    exact hh.trans (sup_le_sup_right le_sup_left _)
  rcases source_hstar_selected_block_alternative D hH hZL hZH (L ⊔ baumann (T : Subgroup G))
      (K ⊔ baumann (T : Subgroup G)) le_sup_right le_sup_right hLgen
      (hHgen.trans (sup_le_sup_right le_sup_left _)) hlocalL hlocalK with hb | hb
  · left
    have hL : (L.subgroupOf (localJoin T L)).IsCComponent := by
      change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
      rw [componentOrbit_sup]
      exact D.maximal.1.1
    exact source_selected_block_in_ambient ((le_componentOrbit L T).trans le_sup_left) hL hBL hb
  · exact Or.inr (source_selected_block_in_ambient hKH hK hBK hb)
end CFSG.Quasithin.Chapter10
