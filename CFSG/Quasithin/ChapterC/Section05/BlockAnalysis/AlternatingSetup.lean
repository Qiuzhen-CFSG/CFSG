module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup.Core
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveCentralizer
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPair

/-!
# Constructing the original C.5.4 alternating-five setup

The original commutator, normalization and Sylow data construct the action,
its full Baumann image and its exact two-core. C.1.13(c), with its central
O₂ factor retained, gives the direct product. The result is the literal
setup consumed by C.5.6 and the original C.5.12 terminal contradiction.

Source: Aschbacher–Smith C.5.3–4, printed pp.154–155.
-/
public section
open Subgroup Stellmacher BinaryPermutation
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
open ConjugateSource AlternatingSetup
variable {G : Type*} [Group G] [Finite G]

theorem exists_alternatingPairSetup (R K L : Subgroup G) (hR : IsPGroup 2 R)
    (hK : IsAlternatingBlock K 5) (hmove : K = ⁅K,elementaryAbelianMaxJ R⁆)
    (hn : ChapterB.baumann R ≤ normalizer (K : Set G))
    (P : Sylow 2 K) (hP : (P : Subgroup K).map K.subtype = R ⊓ K)
    (hcomm : L ≤ centralizer (K : Set G))
    (hperm : ∀ r ∈ R, K.map (MulAut.conj r).toMonoidHom = K ∨
      K.map (MulAut.conj r).toMonoidHom = L) :
    Nonempty (AlternatingPairSetup R K L) := by
  obtain ⟨hc,q,e,hKi,hSi,he⟩ := source_marked_action R K hR hK hmove hn P hP
  obtain ⟨hUS,hcore⟩ := source_core_and_module R K hR hK hn hc
  let S := ChapterB.baumann R
  let Q := (K ⊔ S).pCoreIn 2
  obtain ⟨hQ,hKQ,hUQ,hcom⟩ := source_core_split_inputs R K hR hK hn
  have hsplit : Q = sourceModule K ⊔ (Q ⊓ centralizer (K : Set G)) := by
    exact hK.two_subgroup_eq_module_sup_centralizer hQ hKQ hUQ hcom
  have hcentral : Q ⊓ centralizer (K : Set G) = S ⊓ centralizer (K : Set G) := by
    apply le_antisymm (inf_le_inf_right _ hc)
    apply le_inf _ inf_le_right
    exact (le_inf inf_le_left
      (inf_le_right.trans (centralizer_le (map_subtype_le _)))).trans hcore.ge
  refine ⟨{
    twoGroup := hR
    block := hK
    commute := hcomm
    module_le := hUS
    normalizes := hn
    core := hcore
    product := ?_
    permutes := hperm
    sylow := P
    sylow_image := hP
    action := q
    coordinates := e
    block_image := hKi
    baumann_image := hSi
    equivariant := he }⟩
  exact hsplit.trans (congrArg (sourceModule K ⊔ ·) hcentral)

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
