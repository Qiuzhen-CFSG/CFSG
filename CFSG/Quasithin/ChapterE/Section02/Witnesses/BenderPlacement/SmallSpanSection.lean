module

public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallCenter
public import Theory.GroupTheory.ConjugateSpanCentralSection
/-!
# The elementary span section in the solvable small-pair branch

Use the original marked pair and put P=O₂(I), Z=Z(P), B=P∩V and L=⟨Bᴴ⟩.
The central-line theorem gives ambient normality of Z. The actual product
U=P C_U(V) places O₂(H) in P C_H(B). Since P is extraspecial, the general
conjugate-span lemma gives [L,O₂(H)]≤Z and an elementary abelian image LZ/Z.
These are the literal section-action inputs used in the residual-nine and
residual-twenty-seven branches of Aschbacher--Smith E.2.17, printed p.229.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]
  {S : Sylow 2 H} {W U : Subgroup H} [IsElementaryAbelian 2 W] {n : ℕ}
theorem OriginalWitness.small_span_section_of_solvable
    {κ : GroupClass} (hH : IsSQTK κ H)
    (hP : ChapterB.IsMinimalParabolicOver S ⊤) (hs : Group.IsSolvable H)
    (w : OriginalWitness S (ChapterB.minimalParabolicMax S hP) W n)
    (hWS : W ≤ (S : Subgroup H))
    (hSW : (S : Subgroup H) ≤ normalizer (W : Set H))
    (hcore : W ≤ (ChapterB.minimalParabolicMax S hP).pCoreIn 2)
    (hout : ¬ W ≤ ChapterB.minimalParabolicCore S hP)
    (hfit : generalizedFitting H = pCore 2 H) (hW : Nat.card W = 16)
    (hSU : (S : Subgroup H) ≤ U) (hU : U ≤ normalizer (W : Set H))
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (W : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U W hU q hq hk))
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax S hP)).map
      (ChapterB.minimalParabolicMax S hP).subtype ≤ centralizer (W : Set H)) :
    let P := w.pair.subgroup.pCoreIn 2
    let Z := (center P).map P.subtype
    let L := conjugateSpanBy (P ⊓ W) ⊤
    ∃ hZn : Z.Normal, letI := hZn
      Z ≤ center H ∧ ⁅L,pCore 2 H⁆ ≤ Z ∧
        IsElementaryAbelian 2 (L.map (QuotientGroup.mk' Z)) := by
  let P := w.pair.subgroup.pCoreIn 2
  let Z := (center P).map P.subtype
  let B := P ⊓ W
  let L := conjugateSpanBy B ⊤
  have hcenter := w.small_center_of_solvable hH hP hs hWS hSW hcore hout hfit hW
    hSU hU q hq hk hD hratio hres
  have hZn : Z.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [←centralizer_eq_top_iff_subset.mpr hcenter.1]
    exact Subgroup.centralizer_le_normalizer (Z : Set H)))
  let := hZn
  have hn := ChapterE.minimalParabolic_normalizer_le S hP W
    (IsElementaryAbelian.isPGroup 2 W) hSW hout
  have hplacement := w.small_core_placement_of_solvable hH hP hs hWS hSW hcore hout
    hfit hW hSU hU q hq hk hD hratio
  have hsmall := w.small_quaternion_core hWS hSW hcore hn hfit hW hSU hU q hq hk hD hratio
  obtain ⟨d⟩ := hsmall.1
  let : IsExtraspecial 2 P := d.extraspecial
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (p := 2) inf_le_right
  have hcomm : ⁅P,P⁆ ≤ Z := by
    rw [←map_subtype_commutator]
    exact map_mono (IsExtraspecial.commutator_eq_center (p := 2)).le
  have hQ : pCore 2 H ≤ P ⊔ centralizer (B : Set H) := by
    apply le_trans ((pCore_isPGroup.le_sylow_of_normal S).trans hSU)
    rw [hsmall.2.1]
    exact sup_le_sup_left (inf_le_right.trans (centralizer_le (show B ≤ W from inf_le_right))) P
  obtain ⟨hCQ,hE⟩ := conjugateSpan_central_section_of_centralizing_supplement
    (pCore 2 H) P B Z hplacement.1 inf_le_left hQ hcomm
  exact ⟨hZn,hcenter.1,hCQ,hE⟩

end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
