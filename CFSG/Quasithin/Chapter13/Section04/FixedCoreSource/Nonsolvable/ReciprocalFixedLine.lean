module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.WeightFourResidual
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentContainment
public import Theory.GroupTheory.Commutator.QuotientCenterCard

/-!
# Fixed-line placement in the reciprocal augmentation A₆ residual

For a nonfixed vector of an augmentation core, either it or its product
with the fixed generator has weight four. The weight-four double
commutator lies in the literal point residual. Consequently a point belongs
to that residual whenever the fixed generator does.

In the selected augmentation A₆ branch, the original weight-four calculation
puts z in J = O^{3′}(C_L(z)). The component marking identifies its fixed
line with ⟨z⟩, and the reciprocal residual is this same J. Applying the
point calculation to the original fixed generator d gives C_V(L) ≤ J.
Thus P C_V(L), where P=[V,J], is the actual sixteen-group in O₂(J), and
its image in the literal quotient O₂(J)/⟨z⟩ is central of order eight.
The final application derives the original weight-four condition from the
same mixed conjugator and both reciprocal radical containments.

The nonzero component fixed-space alternative is retained explicitly;
this file does not exclude the selected natural A₆ alternative or prove
the source upper bound |Z(O₂(J)/⟨z⟩)| ≤ 4. Those block calculations, mixed
and product reciprocity, the graph argument and the final offender
contradiction remain with this source owner. Earlier universal Structural1222
and original 13.3.2 inputs retain their existing producers and final discharge.

Source: Aschbacher–Smith 13.4.15, final paragraph, printed p.912,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V K : Subgroup G}

omit [Finite G] in
private theorem residual_mul_constant (D : ChosenModule T L V) (m : CoreMarking D)
    (v : V) : Solvable.firstCentralizerResidual L (v * m.constant).val =
      Solvable.firstCentralizerResidual L v.val := by
  have he : L ⊓ centralizer ({(v * m.constant).val} : Set G) =
      L ⊓ centralizer ({v.val} : Set G) := by
    ext a
    constructor
    · rintro ⟨ha,hac⟩
      refine ⟨ha,mem_centralizer_singleton_iff.mpr ?_⟩
      have hc : m.constant.val ∈ centralizer ({a} : Set G) :=
        mem_centralizer_singleton_iff.mpr (m.constant_fixed a ha).symm
      have hv : v.val * m.constant.val ∈ centralizer ({a} : Set G) :=
        mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hac).symm
      have hh := (centralizer ({a} : Set G)).mul_mem hv
        ((centralizer ({a} : Set G)).inv_mem hc)
      simp only [mul_inv_cancel_right] at hh
      exact (mem_centralizer_singleton_iff.mp hh).symm
    · rintro ⟨ha,hav⟩
      refine ⟨ha,mem_centralizer_singleton_iff.mpr ?_⟩
      have hv : v.val ∈ centralizer ({a} : Set G) :=
        mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hav).symm
      have hc : m.constant.val ∈ centralizer ({a} : Set G) :=
        mem_centralizer_singleton_iff.mpr (m.constant_fixed a ha).symm
      exact (mem_centralizer_singleton_iff.mp
        ((centralizer ({a} : Set G)).mul_mem hv hc)).symm
  simp only [Solvable.firstCentralizerResidual_eq]
  exact congrArg (fun C : Subgroup G => (primeToResidual 3 C).map C.subtype) he

theorem core_point_mem_residual_of_fixed_mem
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (v : V) (hv : v.val ∉ centralizer (L : Set G))
    (hc : m.constant.val ∈ Solvable.firstCentralizerResidual L v.val) :
    v.val ∈ Solvable.firstCentralizerResidual L v.val := by
  have weight_four (w : V) (hw : w.val ∉ centralizer (L : Set G))
      (hweight : m.weight w = 4) : w.val ∈ Solvable.firstCentralizerResidual L w.val := by
    have hh := (original_weight_four_residual_sixteen D m eL w hw hweight).2.1
    exact ((Subgroup.commutator_le_sup _ _).trans (sup_le (pCoreIn_le 2 _) (pCoreIn_le 2 _))) hh
  rcases m.nonfixed_weight v hv with h2 | h4
  · have hw : m.weight (v * m.constant) = 4 := by rw [m.weight_mul_constant,h2]
    have hnf : (v * m.constant).val ∉ centralizer (L : Set G) := by
      intro hh
      rcases (m.fixed_iff _).mp hh with hh | hh
      · rw [hh,m.weight_one] at hw
        contradiction
      · rw [hh,m.weight_constant] at hw
        contradiction
    have hh := weight_four (v * m.constant) hnf hw
    rw [residual_mul_constant D m v] at hh
    have hp := (Solvable.firstCentralizerResidual L v.val).mul_mem hh
      ((Solvable.firstCentralizerResidual L v.val).inv_mem hc)
    simpa only [Subgroup.coe_mul,mul_inv_cancel_right] using hp
  · exact weight_four v hv h4

/-- In the actual selected augmentation A₆ branch, the original weight-four
point puts the entire original fixed line in the common reciprocal residual. -/
theorem original_weight_four_reciprocal_fixed_line
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) (hw : m.weight z = 4)
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) :
    V ⊓ centralizer (L : Set G) ≤ Solvable.firstCentralizerResidual L z.val := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  let J := Solvable.firstCentralizerResidual L z.val
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  obtain ⟨DK,⟨mK⟩,hfix,_,_,_,_⟩ := component_core_marking_of_source_fixed
    h₀ h structural m h1332 fixed hindex z.property hzT hz1 hK.1 hHN hKM hfK hfixed
  have hzJ : z.val ∈ J := ((Subgroup.commutator_le_sup _ _).trans (sup_le (pCoreIn_le 2 J) (pCoreIn_le 2 J)))
    (original_weight_four_residual_sixteen D m eL z hzL hw).2.1
  have hsplit : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K = U := by
    have hh := component_seed_split h₀ hzT hz1 hK.1 (h1332 K hfK).1
    rw [component_full_fixed_line h structural z.val hz1 hzT hindex K hK.1 hKM,
      sup_eq_left.mpr (show zpowers z.val ≤ U from hfix.symm ▸ inf_le_left)] at hh
    exact hh
  have hdU : m.constant.val ∈ U := hsplit ▸
    le_conjugateSpanBy _ _ (m.constant_mem_central_four h structural).2
  have hdK : m.constant.val ∉ centralizer (K : Set G) := by
    intro hd
    apply hKM
    rw [←fixed_generator_centralizer h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun he => m.constant_ne_one (Subtype.ext he))]
    exact fun k hk => mem_centralizer_singleton_iff.mpr (hd k hk)
  have hrec := component_reciprocal_residual_of_ordinary_six h₀ h structural m hzT hz1
    hK hHN (component_quotient_quasisimple h1332 hfK) eK eL
  have hcJ : mK.constant.val ∈ J := (zpowers_le.mpr hzJ)
    (hfix.le ⟨mK.constant.property,mK.constant_fixed⟩)
  have hdJ : m.constant.val ∈ J := by
    have hc : mK.constant.val ∈ Solvable.firstCentralizerResidual K m.constant.val :=
      hrec.symm ▸ hcJ
    have hh := core_point_mem_residual_of_fixed_mem DK mK eK ⟨m.constant.val,hdU⟩ hdK hc
    rwa [hrec] at hh
  intro x hx
  rcases (m.fixed_iff ⟨x,hx.1⟩).mp hx.2 with he | he
  · have he' : x = 1 := congrArg Subtype.val he
    rw [he']
    exact one_mem J
  · have he' : x = m.constant.val := congrArg Subtype.val he
    rw [he']
    exact hdJ

/-- The literal sixteen-group yields an eight-group in the center of
O₂(L₁)/⟨z⟩. Normality of the quotient line is stated explicitly and no
upper bound for this center is assumed. -/
theorem original_weight_four_residual_center_lower
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzL : z.val ∉ centralizer (L : Set G)) (hw : m.weight z = 4)
    (hF : V ⊓ centralizer (L : Set G) ≤ Solvable.firstCentralizerResidual L z.val) :
    let Q := (Solvable.firstCentralizerResidual L z.val).pCoreIn 2
    ∃ hn : ((zpowers z.val).subgroupOf Q).Normal,
      letI := hn
      8 ≤ Nat.card (center (Q ⧸ (zpowers z.val).subgroupOf Q)) := by
  let J := Solvable.firstCentralizerResidual L z.val
  let Q := J.pCoreIn 2
  let E := ⁅V,J⁆ ⊔ (V ⊓ centralizer (L : Set G))
  let N := (zpowers z.val).subgroupOf Q
  obtain ⟨hPQ,hz,hE,hcomm,hEQ⟩ := original_weight_four_residual_sixteen D m eL z hzL hw
  have hEQ : E ≤ Q := hEQ hF
  have hzQ : z.val ∈ Q := ((Subgroup.commutator_le_sup _ _).trans (sup_le le_rfl le_rfl)) hz
  have hNQ : zpowers z.val ≤ Q := zpowers_le.mpr hzQ
  have hJz : J ≤ centralizer ({z.val} : Set G) :=
    (Solvable.firstCentralizerResidual_le L z.val).trans inf_le_right
  have hNZ : N ≤ center Q := by
    intro n hn
    apply mem_center_iff.mpr
    intro q
    have hc : zpowers z.val ≤ centralizer ({q.val} : Set G) := zpowers_le.mpr
      (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp (hJz (pCoreIn_le 2 J q.property))).symm)
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hc hn)).symm
  let hn : N.Normal := ⟨fun n hn q => by
    rw [(mem_center_iff.mp (hNZ hn)) q,mul_inv_cancel_right]
    exact hn⟩
  refine ⟨hn,?_⟩
  let Ei := E.subgroupOf Q
  have hNE : N ≤ Ei := by
    intro x hx
    have hline : zpowers z.val ≤ ⁅V,J⁆ := by
      rw [←(original_weight_four_residual_geometry D m eL z hzL hw).2.2]
      exact le_normalizer_iff_commutator_le_left.mp
        ((pCoreIn_le 2 J).trans (normalizer_commutator_ge_right V J))
    exact (show ⁅V,J⁆ ≤ E from le_sup_left) (hline hx)
  have hci : ⁅Ei,⊤⁆ ≤ N := by
    apply commutator_le.mpr
    intro a ha b _
    exact hcomm.le (commutator_mem_commutator ha b.property)
  have hc := card_le_card_center_quotient_mul Ei N hNE hci
  have hEi : Nat.card Ei = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEQ).toEquiv).trans hE
  have hN : Nat.card N = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hNQ).toEquiv,Nat.card_zpowers]
    let := D.elementary
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ z.property)
      (fun hh => hzL (hh ▸ one_mem _))
  rw [hEi,hN] at hc
  change 8 ≤ Nat.card (center (Q ⧸ N))
  omega

open Section03.Noncentrality.SupercriticalSource
variable {A B : Subgroup G}

/-- The original mixed pair in the selected augmentation A₆ branch has its
fixed line in the residual, and its sixteen-group lies in the literal two-core.
Its image gives the center lower bound for the final source comparison. -/
theorem original_linear_pair_mixed_reciprocal_center_lower
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hlin : Solvable.LinearAmalgamConclusion T (A ⊔ B))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hAz : A ≤ centralizer ({z.val} : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) :
    let X := A ⊔ B
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    let J := Solvable.firstCentralizerResidual L z.val
    let P := ⁅V,J⁆
    let F := V ⊓ centralizer (L : Set G)
    let Q := J.pCoreIn 2
    ∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → V ≤ (B.pCoreIn 2).conjBy g →
      ⁅V,U.conjBy g⁆ ≠ ⊥ →
      F ≤ J ∧ P ⊔ F ≤ Q ∧ Nat.card (P ⊔ F : Subgroup G) = 16 ∧
        ⁅P ⊔ F,Q⁆ = zpowers z.val ∧
        ∃ hn : ((zpowers z.val).subgroupOf Q).Normal,
          letI := hn
          8 ≤ Nat.card (center (Q ⧸ (zpowers z.val).subgroupOf Q)) := by
  dsimp only
  intro g h₁ h₂ hm
  obtain ⟨_,_,hw,_,_⟩ := original_linear_pair_mixed_weight_four
    h₀ h structural D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres
    h1332 hlin eL hM hZV W hW hTW hB hfusion z hzT hzL hAz g h₁ h₂ hm
  have hF := original_weight_four_reciprocal_fixed_line h₀ h structural D m h1332 fixed
    hindexL eL z hzT hzL hw hK hHN hKM hfK eK hfixed
  obtain ⟨_,_,hc,hd,hPQ⟩ := original_weight_four_residual_sixteen D m eL z hzL hw
  exact ⟨hF,hPQ hF,hc,hd,original_weight_four_residual_center_lower D m eL z hzL hw hF⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
