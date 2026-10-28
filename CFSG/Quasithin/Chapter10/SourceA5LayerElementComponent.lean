module
public import CFSG.Quasithin.Chapter10.SourceA5ElementComponent
public import CFSG.Quasithin.Chapter10.SourceBaumannBlocks
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.NaturalAction.FixedKernel

/-!
# A moved-layer vector supplies the original element-centralizer component

The fixed kernel of the natural alternating-five block layer is trivial.
A nonidentity vector in the moved layer of an original Sylow conjugate of
L therefore does not centralize L₀. This discharges precisely the distinguishing
vector hypothesis in the prescribed centralizer-Sylow and 1.2.4 arguments.
The original component, vector and conjugating element are all retained.
Source: Aschbacher–Smith 10.2.1, printed p.743, using C.1.13(c) and 1.2.4.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

omit [Finite G] in
/-- A nonzero vector in an A5 moved layer cannot centralize an overgroup
of that original block. -/
theorem alternatingFive_layer_not_centralizes_overgroup
    {K O : Subgroup G} (hK : IsAlternatingBlock K 5) (hKO : K ≤ O)
    {v : G} (hv : v ∈ (blockU K).map K.subtype) (hv1 : v ≠ 1) :
    v ∉ centralizer (O : Set G) := by
  obtain ⟨w,hw,rfl⟩ := hv
  intro hc
  have hz : w ∈ center K := by
    apply mem_center_iff.mpr
    intro k
    exact Subtype.ext (hc k (hKO k.property))
  have he : blockU K ⊓ center K = ⊥ := by
    rw [←blockFixed_map,hK.blockFixed_eq_bot,Subgroup.map_bot]
  exact hv1 (congrArg K.subtype (mem_bot.mp (he ▸ (show w ∈ blockU K ⊓ center K from ⟨hw,hz⟩))))

/-- The actual moved layer of the selected original Sylow conjugate gives
both the prescribed Sylow centralizer and the containing C-component. -/
theorem source_a5_conjugate_layer_element_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    {t v : G} (ht : t ∈ (T : Subgroup G))
    (hv : v ∈ (blockU (L.map (MulAut.conj t).toMonoidHom)).map
      (L.map (MulAut.conj t).toMonoidHom).subtype)
    (hvT : v ∈ (T : Subgroup G)) (hv1 : v ≠ 1)
    (hvL : v ∈ centralizer (L : Set G))
    (hCT : (T : Subgroup G) ⊓ centralizer ({v} : Set G) =
      (T : Subgroup G) ⊓ normalizer (L : Set G)) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      (centralizer ({v} : Set G)) ∧
    ∃ I : Subgroup G, L ≤ I ∧ I ≤ centralizer ({v} : Set G) ∧
      (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent ∧
      centralizer ({v} : Set G) ≤ normalizer (I : Set G) := by
  have hL := (source_a5_original_block_of_baumann_not_controlled D e hn hout).2.2
  have hK : IsAlternatingBlock (L.map (MulAut.conj t).toMonoidHom) 5 :=
    RankOne.Solvable.isAlternatingBlock_of_equiv ((MulAut.conj t).subgroupMap L) hL
  have hKO : L.map (MulAut.conj t).toMonoidHom ≤ localOrbit T L :=
    le_iSup_of_le (⟨t,ht⟩ : T) le_rfl
  have hv0 := alternatingFive_layer_not_centralizes_overgroup hK hKO hv hv1
  exact ⟨source_a5_element_centralizer_sylow D e hn hvL hv0 hCT,
    source_a5_element_containing_component D e hn hvT hv1 hvL hv0 hCT⟩

end CFSG.Quasithin.Chapter10
