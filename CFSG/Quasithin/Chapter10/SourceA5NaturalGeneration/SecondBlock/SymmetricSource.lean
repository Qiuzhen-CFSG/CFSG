module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.HStarBaumann
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.SymmetricGeometry
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.OriginalConsequences
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.LocalClass
/-!
# Recovering the original component from the H* first-block alternative

The actual H* source supplies full-core generation in either its single or
paired residual row. The action kernel lies in that residual, so Baum(S) is
Sylow there. The selected natural block and a cubic normalizer give central
elementary commutators in Baum(S), hence in the original Baum(T). Applying
the original L local-class embedding then recovers L as a block in L₀T.

The exact natural marking, cubic subgroup and single-or-S-conjugate residual
cover are retained as source data; no full-core identity or original-L block
is assumed. Source: Aschbacher--Smith 10.2.3(4), printed pp.746--747.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open ChapterB ChapterC ChapterE Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
variable {F : Type*} [Field F] [CharP F 2]
local instance symmetricSecondBlockFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

private theorem commutator_le_omegaCenter_map_equiv
    {A B : Type*} [Group A] [Group B] (a : A ≃* B)
    (hc : commutator A ≤ GlaubermanNiles.omegaCenter A) :
    commutator B ≤ GlaubermanNiles.omegaCenter B := by
  have h := map_mono (f := a.toMonoidHom) hc
  rwa [_root_.map_commutator_eq,MonoidHom.range_eq_top.mpr a.surjective,
    ← _root_.commutator_def,GlaubermanNiles.omegaCenter_map_equiv] at h

/-- The H* first-block branch controls the original common Baumann subgroup. -/
theorem source_hstar_common_baumann_commutator_of_block
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hF : Nat.card F = 4) (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (hlarge : 1 < generationParameter H)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥)
    (K : Subgroup H) (hb : IsBlock K) {m : ℕ} (hnat : IsL2EvenBlock K m)
    (hR : pResidual 2 H = K ∨ ∃ t : H,
      t ∈ (T.subtype hH.1.1.2 : Subgroup H) ∧
        pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom)
    (A : Subgroup H) (hAK : A ≤ K) (hA : Nat.card A=3)
    (hAB : A ≤ normalizer (baumann (T.subtype hH.1.1.2 : Subgroup H) : Set H)) :
    commutator (baumann (T : Subgroup G)) ≤
      GlaubermanNiles.omegaCenter (baumann (T : Subgroup G)) := by
  let S := T.subtype hH.1.1.2
  have hR' : pResidual 2 H = K ∨ ∃ t : H,
      pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom := by
    rcases hR with h | ⟨t,_,h⟩
    · exact Or.inl h
    · exact Or.inr ⟨t,h⟩
  have hm := (source_hstar_block_full_core_moved D e hn hH hZH hF f n
    hlarge hCZ hz K hb hR').2
  have hS := (source_hstar_baumann_in_residual_of_block D e hn hH hZH hF f n
    hlarge hCZ hz K hb hR').1
  have hzH : omegaCenterIn (S : Subgroup H) ⊓ center H = ⊥ := by
    apply bot_unique
    intro z hz'
    have hzm : (z : G) ∈ omegaOneCenterAmbient (T : Subgroup G) := by
      have hh := mem_map_of_mem H.subtype hz'.1
      change (z : G) ∈ (omegaOneCenterAmbient (S : Subgroup H)).map H.subtype at hh
      rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective] at hh
      have hSm : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
        map_subgroupOf_eq_of_le hH.1.1.2
      rwa [hSm] at hh
    have hzc : (z : G) ∈ centralizer (H : Set G) := by
      intro h hh
      exact congrArg H.subtype (mem_center_iff.mp hz'.2 ⟨h,hh⟩)
    exact mem_bot.mpr (Subtype.ext (mem_bot.mp (hz ▸ ⟨hzm,hzc⟩)))
  have hc := source_baumann_commutator_of_natural_residual_cover S
    (source_hstar_fitting_eq_core D hH) K hb hnat hR hzH hm hS A hAK hA hAB
  have hBm : (baumann (S : Subgroup H)).map H.subtype=baumann (T : Subgroup G) := by
    have hh := baumann_map_injective H.subtype H.subtype_injective (S : Subgroup H)
    change (baumann (S : Subgroup H)).map H.subtype=
      baumann ((S : Subgroup H).map H.subtype) at hh
    have hSm : (S : Subgroup H).map H.subtype=(T : Subgroup G) :=
      map_subgroupOf_eq_of_le hH.1.1.2
    rwa [hSm] at hh
  let b := ((baumann (S : Subgroup H)).equivMapOfInjective H.subtype
    H.subtype_injective).trans (MulEquiv.subgroupCongr hBm)
  exact commutator_le_omegaCenter_map_equiv b hc

/-- The symmetric characteristic-pair orientation recovers the original L block. -/
theorem source_original_block_of_hstar_natural_block
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hF : Nat.card F = 4) (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (hlarge : 1 < generationParameter H)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥)
    (K : Subgroup H) (hb : IsBlock K) {m : ℕ} (hnat : IsL2EvenBlock K m)
    (hR : pResidual 2 H = K ∨ ∃ t : H,
      t ∈ (T.subtype hH.1.1.2 : Subgroup H) ∧
        pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom)
    (A : Subgroup H) (hAK : A ≤ K) (hA : Nat.card A=3)
    (hAB : A ≤ normalizer (baumann (T.subtype hH.1.1.2 : Subgroup H) : Set H)) :
    IsBlock (L.subgroupOf (localJoin T L)) := by
  have hc := source_hstar_common_baumann_commutator_of_block D e hn hH hZH hF f n
    hlarge hCZ hz K hb hnat hR A hAK hA hAB
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let J := L.subgroupOf X
  let N := J ⊔ baumann (S : Subgroup X)
  have hJ : J.IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  have hclass := source_original_component_localClass_of_hstar_natural_four
    D e hn hH hZH hF f n
  obtain ⟨b,hb',_⟩ := source_original_common_baumann_embedding_of_hstar_natural_four
    D e hn hH hZH hF f n
  have hblock : GlaubermanNiles.BlockAlternative N :=
    hb'.blockAlternative_of_commutator_le_omegaCenter
      (RankOne.ChiProduct.SelectedRankOne.baumann_fixed (T : Subgroup G)) hc
  let := hJ.perfect
  have hp : IsPPerfect 2 J := by
    intro Q hQ hQp
    let := hQ
    let : Group.IsNilpotent (J ⧸ Q) := hQp.isNilpotent
    apply top_unique
    rw [←solvableResidual_eq_top (G := J)]
    exact solvableResidual_le_of_solvable_quotient Q
  let a := ((pResidual 2 N).equivMapOfInjective N.subtype N.subtype_injective).trans
    (MulEquiv.subgroupCongr
      (RankOne.ChiProduct.SelectedRankOne.selected_component_residual_map S J hp hclass.2.1))
  exact ⟨inferInstance,RankOne.Solvable.isShort_of_equiv a hblock.1.short,hJ.subnormal⟩

end CFSG.Quasithin.Chapter10
