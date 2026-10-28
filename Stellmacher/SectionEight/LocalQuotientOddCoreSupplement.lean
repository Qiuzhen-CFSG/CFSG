module
public import Stellmacher.SectionEight.LocalQuotientCore
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionThree.ResidualImageOddPGroup
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift
public import Stellmacher.TwoResidualSylowSupplement
/-!
# The full odd core in the faithful local center quotient

For the initial vertex of a critical path under Section Seven hypotheses,
the full odd core of any supplied faithful center-action quotient is an odd
prime-power group. It is exactly the image of the initial two-residual and
supplements the image of the distinguished Sylow. No length, neighbor-index,
or commuting-critical-center hypothesis is required.

The vertex center lies in the omega-center of the native two-core by (7.3),
so that core belongs to the action kernel. The reusable (3.3) residual-image
theorem makes the actual quotient residual image an odd p-group. Residual
functoriality identifies this image with the quotient's two-residual. Its
normality and odd order put it in the odd core; conversely the odd core has
trivial image in the resulting two-group quotient. Thus they coincide, and
the prime-power structure applies to the full odd core. Mapping the genuine
residual–Sylow generation equation proves the original supplement API.

This shared proof supplies the relative-commutator generation in (9.1)(8),
the full faithful quotient recognition there, and the (1.7) action setup in
(9.2). The original containment and supplement wrappers retain their exact
statements and witnesses. Source: Stellmacher, Journal of Algebra 190 (1997),
(3.3)(a), pp.21–22, (7.3), pp.33–34, and (9.1)–(9.2), pp.47–48;
refs/files/stellmacher-n-group.pdf.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
private theorem local_quotient_oddCore_data
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B)
    (Γ : CosetGraphContext G T A B) (cp : CriticalPath Γ)
    (w : QuotientModuleWitness (GAt Γ cp.a)
      (GAt Γ cp.a ⊓ Subgroup.centralizer (ZAt Γ cp.a : Set G)) (ZAt Γ cp.a)) :
    let _ := w.groupX
    let _ := w.finiteX
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup p (SectionOne.oddCore w.X) ∧
      (twoResidualAmbient (⊤ : Subgroup (GAt Γ cp.a))).map w.projection =
        SectionOne.oddCore w.X := by
  classical
  let := w.groupX
  let := w.finiteX
  let P := GAt Γ cp.a
  let Q := pCore 2 P
  let E := twoResidualAmbient (⊤ : Subgroup P)
  have hQker : Q ≤ w.projection.ker := by
    intro r hr
    rw [w.kernel_eq]
    refine ⟨r.property, ?_⟩
    have hrq : (r : G) ∈ q Γ cp.a := by
      rw [q, Γ.twoCoreAt_def]
      exact Subgroup.mem_map_of_mem P.subtype hr
    change (r : G) ∈ Subgroup.centralizer (ZAt Γ cp.a : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hZomega := (lemma_seven_three h Γ).center_core cp.a cp.firstStep
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)
    have hzc := SevenSix.centerAmbient_le_centralizer (q Γ cp.a)
      (SevenSix.omegaOneCenter_le_centerAmbient (q Γ cp.a) (hZomega hz))
    exact (Subgroup.mem_centralizer_iff.mp hzc r hrq).symm
  obtain ⟨p,hp,hodd,him⟩ := SectionThree.pSet_residual_image_is_odd_pGroup
    T (SevenSix.sectionThreeHypotheses h) P
    ((pFamily_iff_pSet _ _ _).mp (SevenSix.edge_local_data h Γ cp).1.1)
    (SevenSix.edge_local_data h Γ cp).1.2 w.projection hQker
  let _ : Fact p.Prime := ⟨hp⟩
  have hE : twoResidualSubgroup P = E := by
    rw [SectionThree.twoResidualSubgroup_eq_hktPResidual']
    exact SectionThree.twoResidualAmbient_top_eq_hktPResidual.symm
  rw [hE] at him
  let R := BenderSuzuki.External.hktPResidual 2 w.X
  let _ : R.Normal := BenderSuzuki.External.hktPResidual_normal
  have himR : E.map w.projection = R := by
    rw [map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup P) w.projection ⊤
      (Subgroup.map_top_of_surjective w.projection w.surjective)]
    exact SectionThree.twoResidualAmbient_top_eq_hktPResidual
  have hRp : IsPGroup p R := himR ▸ him
  have hRodd : Nat.Coprime 2 (Nat.card R) := by
    obtain ⟨n,hn⟩ := hRp.exists_card_eq
    rw [hn]
    exact (show Odd (p ^ n) from hodd.pow).coprime_two_left
  have hRle : R ≤ SectionOne.oddCore w.X := le_sSup ⟨inferInstance,hRodd⟩
  let qR := QuotientGroup.mk' R
  have hQp : IsPGroup 2 (w.X ⧸ R) :=
    BenderSuzuki.External.hktPResidual_quotient_isPGroup
  have hWp : IsPGroup 2 ((SectionOne.oddCore w.X).map qR) := hQp.to_subgroup _
  have hWodd : Nat.Coprime 2 (Nat.card ((SectionOne.oddCore w.X).map qR)) :=
    (pPrimeCore_coprime_card (p := 2) (G := w.X)).of_dvd_right
      (Subgroup.card_map_dvd (H := SectionOne.oddCore w.X) qR)
  have hWbot : (SectionOne.oddCore w.X).map qR = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rcases hWp.card_eq_or_dvd with hc | hd
    · exact hc
    · exact False.elim ((Nat.prime_two.coprime_iff_not_dvd.mp hWodd) hd)
  have hWeq : SectionOne.oddCore w.X = R := le_antisymm (by
    have hh := (Subgroup.map_eq_bot_iff (f := qR) (H := SectionOne.oddCore w.X)).mp hWbot
    simpa only [qR,QuotientGroup.ker_mk'] using hh) hRle
  exact ⟨p,hp,hodd,hWeq ▸ hRp,himR.trans hWeq.symm⟩

public theorem local_quotient_oddCore_is_odd_pGroup
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B)
    (Γ : CosetGraphContext G T A B) (cp : CriticalPath Γ)
    (w : QuotientModuleWitness (GAt Γ cp.a)
      (GAt Γ cp.a ⊓ Subgroup.centralizer (ZAt Γ cp.a : Set G)) (ZAt Γ cp.a)) :
    let _ := w.groupX
    let _ := w.finiteX
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup p (SectionOne.oddCore w.X) := by
  obtain ⟨p,hp,hodd,hpg,_⟩ := local_quotient_oddCore_data h Γ cp w
  exact ⟨p,hp,hodd,hpg⟩
/-- The local two-residual has odd image in the supplied faithful quotient. -/
public theorem local_quotient_residual_image_le_oddCore
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B)
    (Γ : CosetGraphContext G T A B) (cp : CriticalPath Γ)
    (w : QuotientModuleWitness (GAt Γ cp.a)
      (GAt Γ cp.a ⊓ Subgroup.centralizer (ZAt Γ cp.a : Set G)) (ZAt Γ cp.a)) :
    let _ := w.groupX
    let _ := w.finiteX
    (twoResidualAmbient (⊤ : Subgroup (GAt Γ cp.a))).map w.projection ≤
      SectionOne.oddCore w.X := by
  obtain ⟨_,_,_,_,heq⟩ := local_quotient_oddCore_data h Γ cp w
  exact heq.le

/-- The local odd core supplements the actual Sylow image. -/
public theorem local_quotient_oddCore_sup_sylow
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B)
    (Γ : CosetGraphContext G T A B) (cp : CriticalPath Γ)
    (w : QuotientModuleWitness (GAt Γ cp.a)
      (GAt Γ cp.a ⊓ Subgroup.centralizer (ZAt Γ cp.a : Set G)) (ZAt Γ cp.a)) :
    let _ := w.groupX
    let _ := w.finiteX
    SectionOne.oddCore w.X ⊔ ((T.subgroupOf (GAt Γ cp.a)).map w.projection) = ⊤ := by
  let := w.groupX
  let := w.finiteX
  let P := GAt Γ cp.a
  obtain ⟨hSPle, S, hS⟩ := (SevenSix.edge_sylow_data h Γ cp).1
  have hSnative : (S : Subgroup P) = T.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [hS, Subgroup.map_subgroupOf_eq_of_le hSPle]
  have himageLe := local_quotient_residual_image_le_oddCore h Γ cp w
  have hgen := twoResidualAmbient_top_sup_sylow S
  rw [hSnative] at hgen
  have hmapgen := congrArg (Subgroup.map w.projection) hgen
  rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ w.surjective] at hmapgen
  exact top_unique (hmapgen.symm.le.trans (sup_le_sup_right himageLe _))

end Stellmacher.SectionEight
