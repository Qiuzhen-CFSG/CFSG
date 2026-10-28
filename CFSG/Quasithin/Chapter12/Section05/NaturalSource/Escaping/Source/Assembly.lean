module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Escaping.Source.Escape
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Escaping.Source.Corank
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Escaping.Source.Section

/-!
# Applying the terminal source calculations

The terminal quotient is the literal (L₁H)/O₂(L₁H). A rank bound on the
image of C_T(V) bounds the corank of each selected conjugate Vᵍ. The
original weak closure supplies such a conjugate escaping O₂(H); G.2.2
supplies its commutator line; r>3 and s=3 supply normalization and the
strict corank inequality. This constructs TerminalConfiguration directly.

This direct record construction retains the source incidence, image rank
and faithful-action kernel. The later
SylowKernel leaf supplies a final contradiction using the proved Sylow
kernel bound instead. The Supplement and Residual leaves construct the
literal supplement, select H conditional on point escape, prove incidence
and identify its residual quotient as A₅. KernelCorank and Completion then
prove the actual conjugate's corank bound and the full action-kernel bound,
without requiring the stronger whole-image rank premise of this leaf.
Point escape remains with qt-d-1251-source.
Source: Aschbacher--Smith, proof of 12.5.1, printed p.822.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The image in the full intrinsic quotient H₁/O₂(H₁), using its original
inclusion and quotient map. -/
def terminalImage (H A : Subgroup G) :
    Subgroup ((s.marking.Li 1 ⊔ H : Subgroup G) ⧸ pCore 2 (s.marking.Li 1 ⊔ H : Subgroup G)) :=
  (A.subgroupOf (s.marking.Li 1 ⊔ H)).map (QuotientGroup.mk' (pCore 2 (s.marking.Li 1 ⊔ H : Subgroup G)))

omit [Finite G] in
/-- Kernel-image counting uses the actual intersection A ∩ Q_H. -/
theorem terminal_corank_eq_log_card_image {H A : Subgroup G}
    (hAJ : A ≤ s.marking.Li 1 ⊔ H) :
    subgroupCorank A (A ⊓ terminalCore s.marking H) = Nat.log 2 (Nat.card (s.terminalImage H A)) := by
  unfold subgroupCorank terminalImage
  congr 1
  rw [inf_relIndex_left, ← relIndex_ker, QuotientGroup.ker_mk']
  have he : (terminalCore s.marking H).subgroupOf (s.marking.Li 1 ⊔ H) =
      pCore 2 (s.marking.Li 1 ⊔ H : Subgroup G) :=
    comap_map_eq_self_of_injective (s.marking.Li 1 ⊔ H).subtype_injective _
  rw [← he, relIndex_subgroupOf hAJ]

/-- The rank bound is applied to the original C_T(V) image, not to an
unrelated abstract copy of the residual. -/
theorem terminal_corank_le_two_of_centralizer_image {H : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H)
    (hsmall : primeRank 2 (s.terminalImage H ((T : Subgroup G) ⊓ centralizer (V : Set G))) ≤ 2)
    {g : G} (hAT : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (hAC : V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) :
    subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (terminalIntersection s.marking H g) ≤ 2 := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let J := s.marking.Li 1 ⊔ H
  let hAJ : A ≤ J := hAT.trans (hTH.trans le_sup_right)
  let := D.elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (A.subgroupOf J) := IsElementaryAbelian.subgroupOf hAJ
  let : IsElementaryAbelian 2 (s.terminalImage H A) := IsElementaryAbelian.map _
  have hI : s.terminalImage H A ≤
      s.terminalImage H ((T : Subgroup G) ⊓ centralizer (V : Set G)) :=
    map_mono (comap_mono (le_inf hAT hAC))
  have hrI : Representation.BinaryOffender.rank (s.terminalImage H A) ≤
      primeRank 2 (s.terminalImage H A) := by
    let : IsElementaryAbelian 2 (⊤ : Subgroup (s.terminalImage H A)) :=
      IsElementaryAbelian.of_injective (⊤ : Subgroup (s.terminalImage H A)).subtype
        Subtype.val_injective
    simpa only [Representation.BinaryOffender.rank, Subgroup.card_top] using
      (offender_rank_le_primeRank (⊤ : Subgroup (s.terminalImage H A)))
  have hr := hrI.trans ((primeRank_mono 2 hI).trans hsmall)
  exact (s.terminal_corank_eq_log_card_image hAJ).trans_le hr

variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
  (structural : Structural1222At KnownSimple.IsKnownSimple T)
include h structural

/-- Construct the terminal record from the actual source section. The three
retained premises are the incidence, image-rank and faithful-action steps
on p.822; no conjugate, weak closure, commutator or normalization is assumed. -/
theorem terminalConfiguration_of_HStar_section {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHG : H ≤ s.marking.Gi 1)
    (hM : s.marking.Mi 1 ≤ s.marking.Li 1 ⊔ H)
    (hsmall : primeRank 2 (s.terminalImage H ((T : Subgroup G) ⊓ centralizer (V : Set G))) ≤ 2)
    (hkernel : H ⊓ centralizer (s.marking.UH H : Set G) ≤ terminalCore s.marking H) :
    Nonempty (TerminalConfiguration s.marking) := by
  obtain ⟨g,hAT,_,hAC,hescape⟩ := s.exists_conjugate_escaping_HStar_core h structural hH
  have hcor := s.terminal_corank_le_two_of_centralizer_image hH.1.1.2 hsmall hAT hAC
  have hcomm := s.terminal_commutator_line_of_point_parabolic_le h hHG hM g
  have hAH := hAT.trans hH.1.1.2
  let := s.HStar_span_elementary h structural hHG
  exact ⟨{
    H := H
    sylow_le := hH.1.1.2
    point_le := hHG
    g := g
    conjugate_le := hAH
    escapes_core := hescape
    span_two := IsElementaryAbelian.isPGroup 2 (s.marking.UH H)
    span_normalizes := s.terminal_span_normalizes_of_corank_two h structural hHG hAH hcomm hcor
    commutator_line := hcomm
    small_corank := s.terminal_corank_lt_globalS h structural hcor
    action_kernel := hkernel }⟩

/-- Literal application of the constructed configuration to the original
exterior contradiction; the same source section premises remain explicit. -/
theorem exterior_false_of_HStar_section {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHG : H ≤ s.marking.Gi 1)
    (hM : s.marking.Mi 1 ≤ s.marking.Li 1 ⊔ H)
    (hsmall : primeRank 2 (s.terminalImage H ((T : Subgroup G) ⊓ centralizer (V : Set G))) ≤ 2)
    (hkernel : H ⊓ centralizer (s.marking.UH H : Set G) ≤ terminalCore s.marking H) : False := by
  obtain ⟨d⟩ := s.terminalConfiguration_of_HStar_section h structural hH hHG hM hsmall hkernel
  exact s.exterior_contradiction_from_source_and_terminal h structural d

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
