module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardSpanDerived
/-!
# The Baumann kernel is central in the moved terminal span

For the terminal normal span P, its derived subgroup is fixed by the starting
component, while the component moves P intersect B only into Z_alpha. Since
Z_alpha centralizes P, the three-subgroups lemma shows that [P,L_alpha]
centralizes P intersect B. Thus the literal Baumann kernel in this moved
subgroup is central. This is the group input for recognizing its natural
central quotient; no natural-module identification is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), the opening commutator
calculation in (3.10), printed p.880, used by the terminal paragraph of
(5.12), printed p.927. The final consumer retains the actual characteristic
replacement from SourceData.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- The moved terminal span centralizes its literal Baumann kernel. -/
theorem forward_span_moved_B_kernel_central
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    let P := localZSpan R (p.walk.getVert 2) (alpha R)
    let P₀ := ⁅P,Ltilde R (alpha R)⁆
    ⁅P₀,P⊓B R (alpha R) (s.geometry.Z_normal _)⁆=⊥ ∧
      P₀⊓B R (alpha R) (s.geometry.Z_normal _)≤(center P₀).map P₀.subtype := by
  let P := localZSpan R (p.walk.getVert 2) (alpha R)
  let P₀ := ⁅P,Ltilde R (alpha R)⁆
  let K := P⊓B R (alpha R) (s.geometry.Z_normal _)
  have hb2 : 2<s.geometry.b R := by omega
  have hPV : P≤V R (alpha R) := localZSpan_le_V R (by
    rw [SimpleGraph.dist_comm,p.dist_start (by have hl := p.length_eq_b; omega)])
  have hPQ : P≤Q R (alpha R) := hPV.trans (s.geometry.V_le_Q hb2 _ rfl)
  have hP₀P : P₀≤P := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer _).trans (localZSpan_normalized R _ _))
  have hZaC : Z R (alpha R)≤centralizer (P:Set (FreeAmalgam R)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R (alpha R) rfl)).trans
      (centralizer_le hPQ)
  have hLK : ⁅Ltilde R (alpha R),K⁆≤Z R (alpha R) := by
    apply commutator_le.mpr
    intro l hl k hk
    exact ((mem_B_iff R _ (s.geometry.Z_normal _) (s.geometry.V_local _ rfl hb2) k).mp hk.2).2 l hl
  have hPK : ⁅K,P⁆≤centralizer (Ltilde R (alpha R):Set (FreeAmalgam R)) :=
    ((commutator_mono inf_le_left le_rfl).trans
      (s.forward_span_derived_eq_line h u hfull hb p).2.2.1).trans
        (centralizer_le (Ltilde_le_stabilizer _))
  have hz : ⁅P₀,K⁆=⊥ := commutator_commutator_eq_bot_of_rotate
    (commutator_eq_bot_iff_le_centralizer.mpr (hLK.trans hZaC))
    (commutator_eq_bot_iff_le_centralizer.mpr hPK)
  refine ⟨hz,?_⟩
  intro z hzB
  refine ⟨⟨z,hzB.1⟩,?_,rfl⟩
  apply mem_center_iff.mpr
  intro w
  exact Subtype.ext ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))
    ⟨hP₀P hzB.1,hzB.2⟩ w w.property)
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K] {L W : Subgroup K} [L.Normal] [W.Normal]
  {T : Sylow 2 K} (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- The central Baumann kernel in the actual reduced moving span. -/
theorem reducedSource_block_or_forward_span_moved_B_kernel_central
    (r : CharacteristicReduction (L.subgroupOf J) R) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : ((originalSource d hm).reduce r).geometry.b r.radical=4) :
    IsAlternatingBlock L 6 ∨
      (let P := localZSpan r.radical (p.walk.getVert 2) (alpha r.radical)
       let P₀ := ⁅P,Ltilde r.radical (alpha r.radical)⁆
       P₀⊓B r.radical (alpha r.radical) (((originalSource d hm).reduce r).geometry.Z_normal _)≤
         (center P₀).map P₀.subtype) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact (s.forward_span_moved_B_kernel_central (reduced_nativeCentralLayer d hm r) _ hf hb p).2
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
