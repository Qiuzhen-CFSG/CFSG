module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.Factorization
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Factorization.KernelSelection

/-!
# Maximal-kernel and odd-line selection on the source XR

Failure of the literal normalizer product constructs a maximal normal kernel,
absorbs O2(XR), and gives a two-core-free quotient with an odd elementary chief
section uncovered by either original normalizer. Frattini chooses an actual
maximum elementary subgroup outside that kernel.

Under the proper-overgroup induction premise, the same quotient supplies an
invariant odd prime line outside the second normalizer. Pulling its fixing
hyperplane back to the original actor gives B in A1(R), including its exact
image, index and kernel containment. No tensor or FF hypothesis is changed.
The Frattini normalizer construction and final induction discharge remain with
qt-d-1319-ff-contradiction; this module does not assert the full factorization.

Source: GLS, Number 2, G.26.18(a), printed pp.152–153; Aschbacher–Smith 13.1.9,
printed pp.870–871. Earlier canonical geometry remains with
qt-d-1317-supplements.
-/

public section
open scoped Pointwise
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin ChapterB
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02 Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

omit [Finite G] in
private theorem relative_top_product (W P U V : Subgroup G) :
    NormalizerProductOn (P.subgroupOf W) (U.subgroupOf W) (V.subgroupOf W) ⊤ ↔
      (W : Set G) = ((W ⊓ U : Subgroup G) : Set G) * ((W ⊓ V : Subgroup G) : Set G) := by
  simp only [NormalizerProductOn,top_sup_eq,top_inf_eq,coe_top]
  constructor
  · intro h
    apply Set.Subset.antisymm
    · intro x hx
      have hh : (⟨x,hx⟩ : W) ∈ (U.subgroupOf W : Set W) * (V.subgroupOf W : Set W) :=
        h ▸ Set.mem_univ _
      obtain ⟨a,ha,b,hb,he⟩ := hh
      exact ⟨a,⟨a.property,ha⟩,b,⟨b.property,hb⟩,congrArg Subtype.val he⟩
    · rintro x ⟨a,ha,b,hb,rfl⟩
      exact W.mul_mem ha.1 hb.1
  · intro h
    apply Set.Subset.antisymm
    · intro x _
      have hx : (x : G) ∈ (W : Set G) := x.property
      rw [h] at hx
      obtain ⟨a,ha,b,hb,he⟩ := hx
      exact ⟨⟨a,ha.1⟩,ha.2,⟨b,hb.1⟩,hb.2,Subtype.ext he⟩
    · exact Set.subset_univ _

omit [Finite G] in
private theorem kernel_omega_normalizer (J : Subgroup G) :
    normalizer (J : Set G) ≤ normalizer (omegaOneCenterAmbient J : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq] at hx ⊢
  change J.map (MulAut.conj x).toMonoidHom = J at hx
  change (omegaOneCenterAmbient J).map (MulAut.conj x).toMonoidHom = _
  rw [←omegaOneCenterAmbient_map_injective _ (MulAut.conj x).injective,hx]

/-- Failure of the actual source product constructs its maximal normal kernel,
the original escaping maximum elementary actor, and an uncovered odd chief
section. No proper-overgroup induction premise is needed for this selection. -/
theorem controlledIndex_maximal_kernel (h : Hypothesis1311 T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (p : ℕ) [Fact p.Prime] (ho : Odd p)
    (hf : ¬ ControlledIndexFactorization (XiP p L) (radicalSylowCentralizer T L)) :
    let R := radicalSylowCentralizer T L
    let W := XiP p L ⊔ R
    let U := (normalizer (thompsonJ R 0 : Set G)).subgroupOf W
    let V := (normalizer (omegaOneCenterAmbient (thompsonJ R 1) : Set G)).subgroupOf W
    ∃ S : Subgroup W, ∃ n : S.Normal, letI := n
      IsMaximalProductKernel (R.subgroupOf W) U V S ∧ pCore 2 W ≤ S ∧
      pCore 2 (W ⧸ S) = ⊥ ∧
      (∃ A : Subgroup W, A ∈ elementaryAbelianMaxSubgroups (R.subgroupOf W) ∧ ¬ A ≤ S) ∧
      ∃ (r : ℕ) (Y : Subgroup (W ⧸ S)), r.Prime ∧ Odd r ∧ Y.Normal ∧ Y ≠ ⊥ ∧
        IsElementaryAbelian r Y ∧
        (∀ D : Subgroup (W ⧸ S), D.Normal → D ≤ Y → D = ⊥ ∨ D = Y) ∧
        ¬ Y ≤ U.map (QuotientGroup.mk' S) ∧ ¬ Y ≤ V.map (QuotientGroup.mk' S) := by
  let R := radicalSylowCentralizer T L
  let W := XiP p L ⊔ R
  let U := (normalizer (thompsonJ R 0 : Set G)).subgroupOf W
  let V := (normalizer (omegaOneCenterAmbient (thompsonJ R 1) : Set G)).subgroupOf W
  obtain ⟨P,hP⟩ := controlledIndex_XR_sylow h hL hn p ho
  have hPw : (P : Subgroup W) = R.subgroupOf W := by
    apply map_injective W.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (show R ≤ W from le_sup_right)]
  have hPU : (P : Subgroup W) ≤ U := by
    rw [hPw]
    exact subgroupOf_mono W (R.le_normalizer.trans (normalizer_le_thompson R 0))
  have hPV : (P : Subgroup W) ≤ V := by
    rw [hPw]
    exact subgroupOf_mono W (R.le_normalizer.trans
      ((normalizer_le_thompson R 1).trans (kernel_omega_normalizer _)))
  have hJU : normalizer (thompsonJ (P : Subgroup W) 0 : Set W) ≤ U := by
    have hJmap : (thompsonJ (P : Subgroup W) 0).map W.subtype = thompsonJ R 0 := by
      rw [thompsonJ_zero,←elementaryAbelianMaxJ_map_injective W.subtype W.subtype_injective,
        hP,thompsonJ_zero]
    intro x hx
    have hh := (thompsonJ (P : Subgroup W) 0).le_normalizer_map W.subtype
      (mem_map_of_mem W.subtype hx)
    rwa [hJmap] at hh
  have hfail : ¬ NormalizerProductOn (P : Subgroup W) U V ⊤ := by
    rw [hPw]
    exact fun hh => hf ((relative_top_product W R _ _).mp hh)
  obtain ⟨S,hS⟩ := exists_maximalProductKernel (P : Subgroup W) U V hPU hPV
  let := hS.normal
  let : Group.IsSolvable W := controlledIndex_XR_solvable h hL hn p ho
  refine ⟨S,hS.normal,?_,hS.pCore_le P U V S,hS.pCore_quotient_eq_bot P U V S,?_,
    hS.odd_chief P U V S hPU hPV hfail⟩
  · exact hPw ▸ hS
  · simpa only [hPw] using maximalProductKernel_exists_maximum_outside P U V S hS hPU hJU hfail

/-- The source induction premise selects the original near-maximum B and an
odd prime line in the same quotient. Its kernel containment and fixing action
are retained for I = SB and Q = (R ∩ S)B in the Frattini construction. -/
theorem controlledIndex_odd_line_of_proper_factorizations (h : Hypothesis1311 T)
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
      pCore 2 W ≤ S ∧ pCore 2 (W ⧸ S) = ⊥ ∧
      ∃ (r : ℕ) (A B : Subgroup W) (D : Subgroup (W ⧸ S)), r.Prime ∧ Odd r ∧
        A ∈ elementaryAbelianMaxSubgroups (R.subgroupOf W) ∧ ¬ A ≤ S ∧
        B ∈ thompsonFamily (R.subgroupOf W) 1 ∧ B ≤ A ∧ B.relIndex A = 2 ∧ A ⊓ S ≤ B ∧
        Nat.card D = r ∧ A.map (QuotientGroup.mk' S) ≤ normalizer (D : Set (W ⧸ S)) ∧
        ⁅D,A.map (QuotientGroup.mk' S)⁆ = D ∧
        D ≤ centralizer (B.map (QuotientGroup.mk' S) : Set (W ⧸ S)) ∧
        ¬ D ≤ V.map (QuotientGroup.mk' S) := by
  let R := radicalSylowCentralizer T L
  let W := XiP p L ⊔ R
  let U := (normalizer (thompsonJ R 0 : Set G)).subgroupOf W
  let V := (normalizer (omegaOneCenterAmbient (thompsonJ R 1) : Set G)).subgroupOf W
  obtain ⟨S,n,hK,hcore,hquot,_,_⟩ := controlledIndex_maximal_kernel h hL hn p ho hf
  let := n
  obtain ⟨P,hP⟩ := controlledIndex_XR_sylow h hL hn p ho
  have hPw : (P : Subgroup W) = R.subgroupOf W := by
    apply map_injective W.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (show R ≤ W from le_sup_right)]
  have hPU : (P : Subgroup W) ≤ U := by
    rw [hPw]
    exact subgroupOf_mono W (R.le_normalizer.trans (normalizer_le_thompson R 0))
  have hPV : (P : Subgroup W) ≤ V := by
    rw [hPw]
    exact subgroupOf_mono W (R.le_normalizer.trans
      ((normalizer_le_thompson R 1).trans (kernel_omega_normalizer _)))
  have hJU : normalizer (thompsonJ (P : Subgroup W) 0 : Set W) ≤ U := by
    have hJmap : (thompsonJ (P : Subgroup W) 0).map W.subtype = thompsonJ R 0 := by
      rw [thompsonJ_zero,←elementaryAbelianMaxJ_map_injective W.subtype W.subtype_injective,
        hP,thompsonJ_zero]
    intro x hx
    have hh := (thompsonJ (P : Subgroup W) 0).le_normalizer_map W.subtype
      (mem_map_of_mem W.subtype hx)
    rwa [hJmap] at hh
  have hfail : ¬ NormalizerProductOn (P : Subgroup W) U V ⊤ := by
    rw [hPw]
    exact fun hh => hf ((relative_top_product W R _ _).mp hh)
  let : Group.IsSolvable W := controlledIndex_XR_solvable h hL hn p ho
  obtain ⟨r,A,hr,hor,hA,hAS,Bbar,D,hBbar,hcard,hAD,hcomm,hfix,hout⟩ :=
    maximalProductKernel_odd_line P U V S (hPw ▸ hK) hPU hPV hJU hfail
      (by simpa only [hPw] using hproper)
  obtain ⟨B,hB,hBA,hi,hker,hmap⟩ :=
    thompson_hyperplane_preimage (P : Subgroup W) A hA (QuotientGroup.mk' S) Bbar hBbar
  refine ⟨S,n,hcore,hquot,r,A,B,D,hr,hor,?_,hAS,?_,hBA,hi,?_,hcard,hAD,hcomm,?_,hout⟩
  · simpa only [hPw] using hA
  · simpa only [hPw] using hB
  · simpa only [QuotientGroup.ker_mk'] using hker
  · rwa [hmap]
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
