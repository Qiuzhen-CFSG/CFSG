module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.TerminalOvercomponent.TorusSource.Geometry
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.TerminalOvercomponent.BorelGeometry
/-!
# The terminal common component from the actual original torus

The original torus axes and the two recovered natural block cores give the
same literal commutator Sylow. The opposite axis gives the opposite full
Sylow and Borel, whose normalizer is preserved by the original stabilizer.
The terminal construction therefore supplies a unique proper common
component and bounds its three-rank by one.

The first-axis orientation is explicit. The paired geometry module proves
both orientations for source assembly. Normalization of K by the opposite
cubic is the separate earlier source input from pp.745--746; it is not
inferred merely from the common Sylow. Source: Aschbacher--Smith 10.2.3(4),
printed p.747.
-/
public section
namespace CFSG.Quasithin.Chapter10
open Subgroup Theory.GroupTheory Stellmacher Chapter3.Section02 ChapterC ChapterB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual first-axis configuration constructs the terminal component and rank bound. -/
theorem source_original_torus_first_axis_component
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G)=⊥)
    (hL : IsL2EvenBlock L 2) (hcoreL : pCore 2 L=blockU L)
    (hSO : baumann (T : Subgroup G) ≤ localOrbit T L)
    (hS : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (localOrbit T L ⊔ baumann (T : Subgroup G)))
    (hSL : baumann (T : Subgroup G) ≤ normalizer (L : Set G))
    (K C : Subgroup G) (hK : IsL2EvenBlock K 2) (hcoreK : pCore 2 K=blockU K)
    (hKS : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G) ⊓ K) K)
    (hSK : baumann (T : Subgroup G) ≤ normalizer (K : Set G))
    (hout : ¬ K ≤ D.maximalLocal)
    (hCB : C ≤ sourceOrbitBorel T L) (hc : Nat.card C=9) :
    let hCR : C ≤ localOrbit T L := hCB.trans ((map_subtype_le _).trans inf_le_left)
    let q := (originalA5ProductProjection D e hn ht htn).comp (inclusion hCR)
    let D₁ := ((MonoidHom.snd _ _).comp q).ker.map C.subtype
    let D₂ := ((MonoidHom.fst _ _).comp q).ker.map C.subtype
    D₁ ≤ K → D₂ ≤ normalizer (K : Set G) →
    ∃! I : Subgroup G,
      I ∈ Chapter1.cComponentsIn
        (normalizer ((⁅baumann (T : Subgroup G),D₂⁆ ⊔ D₂ : Subgroup G) : Set G)) ∧
      L < I ∧ K ≤ I ∧
      I ≤ centralizer ((⁅baumann (T : Subgroup G),D₂⁆ ⊔ D₂ : Subgroup G) : Set G) ∧
      primeRank 3 I ≤ 1 := by
  let hCR : C ≤ localOrbit T L := hCB.trans ((map_subtype_le _).trans inf_le_left)
  let q := (originalA5ProductProjection D e hn ht htn).comp (inclusion hCR)
  let D₁ := ((MonoidHom.snd _ _).comp q).ker.map C.subtype
  let D₂ := ((MonoidHom.fst _ _).comp q).ker.map C.subtype
  let J := L.map (MulAut.conj t).toMonoidHom
  let S := baumann (T : Subgroup G)
  dsimp only
  intro hD₁K hD₂K
  obtain ⟨hD₁L,hD₂J,hD₁,hD₂,_,_⟩ :=
    source_original_borel_torus_axes D e hn ht htn hb hz C hCB hc
  change Nat.card D₁=3 at hD₁
  change Nat.card D₂=3 at hD₂
  change D₁ ≤ K at hD₁K
  change D₂ ≤ normalizer (K : Set G) at hD₂K
  have hCS := hCB.trans (source_original_borel_normalizes_baumann hSO hS)
  have hD₁S : D₁ ≤ normalizer (S : Set G) := (map_subtype_le _).trans hCS
  have hD₂S : D₂ ≤ normalizer (S : Set G) := (map_subtype_le _).trans hCS
  obtain ⟨_,hP₁⟩ := source_original_natural_commutator_sylow D D₁ hL hcoreL hS hD₁L hD₁ hD₁S hSL
  have hP₁K := (IsL2EvenBlock.ambient_odd_commutator_sylow K S D₁ hK hcoreK hKS
    hD₁K (by rw [hD₁]; decide) (by intro he; rw [he,card_bot] at hD₁; contradiction)
    hD₁S hSK).2
  have hP₂ := (source_original_conjugate_commutator_sylow D hL hcoreL hS hSL ht
    D₂ hD₂J hD₂ hD₂S).2
  have hR := source_original_opposite_borel_normalized D e hn hL hcoreL hS hSL ht
    D₂ hD₂J hD₂ hD₂S
  let a : L ≃* J := (MulAut.conj t).subgroupMap L
  have hJ : IsShort J := RankOne.Solvable.isShort_of_equiv a hL.2.1
  have hzL := source_original_block_center_eq_bot D hn hb hz
  have hzJ : center J=⊥ := by
    apply bot_unique
    intro j hj
    have hh := (centerCongr a.symm ⟨j,hj⟩).property
    change a.symm j ∈ center L at hh
    rw [hzL,mem_bot] at hh
    exact mem_bot.mpr (a.symm.injective (hh.trans a.symm.map_one.symm))
  have hcomm : J ≤ centralizer (L : Set G) :=
    le_centralizer_iff.mp (source_original_block_commutes_prescribed_conjugate D hb ht htn)
  exact source_original_natural_pair_borel_component D e hn J K ⁅S,D₁⁆ D₁ D₂ hJ hzJ hK
    hcomm hP₁K (Chapter1.isSylowIn_iff.mp hP₁).2.1 hD₁L hD₁K hD₁ hD₂J hD₂ hD₂K hSK hP₂ hR hout
end CFSG.Quasithin.Chapter10
