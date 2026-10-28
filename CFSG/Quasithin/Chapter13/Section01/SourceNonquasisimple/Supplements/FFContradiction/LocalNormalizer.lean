module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.KernelSelection
public import Theory.GroupTheory.FrattiniHyperplaneNormalizer

/-!
# The local Frattini normalizer on the source XR

Use the same maximal normal kernel, maximum elementary actor A, hyperplane B
and odd quotient line selected from the failed normalizer product. The literal
subgroups I = SB, Q = (R ∩ S)B and H = preimage(D Abar) satisfy I normal in H,
Q Sylow in I, A <= N_H(Q), A not contained in I, and H = N_H(Q) I. The original
two-core is contained in Q. These are constructions from the original source
quotient, not extra local normality or Sylow assumptions.

The remaining local step transfers the selected odd line and its noncoverage
to N_H(Q)/(I ∩ N_H(Q)), then applies the checked envelope obstruction. The
proper-overgroup induction and final ControlledIndexFactorization discharge
remain in qt-d-1319-ff-contradiction. Earlier canonical geometry remains with
qt-d-1317-supplements.

Source: GLS, Number 2, G.26.18(a), printed pp.152–153; Aschbacher–Smith 13.1.9,
printed pp.870–871.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin ChapterB
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02 Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The actual local subgroups selected from failure of the source product.
The only additional input is the source's proper-overgroup induction premise. -/
theorem controlledIndex_local_normalizer_of_proper_factorizations (h : Hypothesis1311 T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (p : ℕ) [Fact p.Prime] (ho : Odd p)
    (hf : ¬ ControlledIndexFactorization (XiP p L) (radicalSylowCentralizer T L))
    (hproper : let R := radicalSylowCentralizer T L
      let W := XiP p L ⊔ R
      let U := (normalizer (thompsonJ R 0 : Set G)).subgroupOf W
      let V := (normalizer (omegaOneCenterAmbient (thompsonJ R 1) : Set G)).subgroupOf W
      ∀ D : Subgroup W, D.Normal → D ⊔ R.subgroupOf W ≠ ⊤ →
        NormalizerProductOn (R.subgroupOf W) U V D) :
    let R := radicalSylowCentralizer T L
    let W := XiP p L ⊔ R
    let V := (normalizer (omegaOneCenterAmbient (thompsonJ R 1) : Set G)).subgroupOf W
    ∃ S : Subgroup W, ∃ n : S.Normal, letI := n
      ∃ (r : ℕ) (A B : Subgroup W) (D : Subgroup (W ⧸ S)), r.Prime ∧ Odd r ∧
        A ∈ elementaryAbelianMaxSubgroups (R.subgroupOf W) ∧
        B ∈ thompsonFamily (R.subgroupOf W) 1 ∧ B ≤ A ∧
        Nat.card D = r ∧ A.map (QuotientGroup.mk' S) ≤ normalizer (D : Set (W ⧸ S)) ∧
        ⁅D,A.map (QuotientGroup.mk' S)⁆ = D ∧
        D ≤ centralizer (B.map (QuotientGroup.mk' S) : Set (W ⧸ S)) ∧
        ¬ D ≤ V.map (QuotientGroup.mk' S) ∧
        let H := (D ⊔ A.map (QuotientGroup.mk' S)).comap (QuotientGroup.mk' S)
        let I := S ⊔ B
        let Q := (R.subgroupOf W ⊓ S) ⊔ B
        let N := H ⊓ normalizer (Q : Set W)
        I ≤ H ∧ H ≤ normalizer (I : Set W) ∧
          (∃ QI : Sylow 2 I, (QI : Subgroup I).map I.subtype = Q) ∧
          B ≤ Q ∧ Q ≤ R.subgroupOf W ∧ pCore 2 W ≤ Q ∧
          Q ≤ N ∧ A ≤ N ∧ ¬ A ≤ I ∧ N ⊔ I = H := by
  let R := radicalSylowCentralizer T L
  let W := XiP p L ⊔ R
  obtain ⟨S,n,hcore,_,r,A,B,D,hr,hor,hA,_,hB,hBA,hi,hASB,hcard,hAD,hcomm,hDB,hout⟩ :=
    controlledIndex_odd_line_of_proper_factorizations h hL hn p ho hf hproper
  let := n
  let : IsElementaryAbelian 2 A := hA.2.1
  obtain ⟨P,hP⟩ := controlledIndex_XR_sylow h hL hn p ho
  have hPw : (P : Subgroup W) = R.subgroupOf W := by
    apply map_injective W.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (show R ≤ W from le_sup_right)]
  have hlocal := hyperplane_local_normalizer P S A B (by simpa only [hPw] using hA.1)
    hBA hi hASB D hDB
  rw [hPw] at hlocal
  obtain ⟨hIH,hHI,hsyl,hQR,hQN,hAN,hAI,hfr⟩ := hlocal
  have hcoreQ : pCore 2 W ≤ (R.subgroupOf W ⊓ S) ⊔ B :=
    (le_inf (hPw ▸ pCore_isPGroup.le_sylow_of_normal P) hcore).trans le_sup_left
  exact ⟨S,n,r,A,B,D,hr,hor,hA,hB,hBA,hcard,hAD,hcomm,hDB,hout,
    hIH,hHI,hsyl,le_sup_right,hQR,hcoreQ,hQN,hAN,hAI,hfr⟩
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
