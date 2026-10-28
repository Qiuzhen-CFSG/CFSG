module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.Selection
public import Theory.Representation.BinaryOffender.FaithfulRankOne

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.BestWeights.RankObstruction

/-!
# Best weights and the first remaining obstruction in 15.3.49(h)

A faithful binary offender with fixed-space codimension at most two is best:
every proper nontrivial subgroup loses at least one rank and has positive
fixed-space codimension, so its weight cannot exceed the original weight.
The trivial subgroup is handled by the ordinary offender inequality.

Apply this to the two actual star images in Geometry.Selection. The image of
the actual D_H lies in both fixed spaces, and its quotient dimension is
log₂ |U_H:D_H|. This proves both B.1.2 weight comparisons in the branch where
that dimension is at most two. The numerator U_H = localSpan Z_S H and the
conjugate-seed endpoint spans, section-centralizer kernel and faithful
SectionAction remain literal throughout.

This does not finish 15.3.49(h). No bound on that corank has been proved here;
the branch of corank at least three remains open. At corank three, the new
obstruction theorem shows that any failure is witnessed by a hyperplane of
one of the two actual images, of rank at least two, fixing a hyperplane of
the module. This follows by comparing the rank lost with the increase in the
fixed space; faithfulness makes every nontrivial subgroup's codimension
positive. No exclusion of this configuration is assumed or proved.

RankObstruction proves
that the representation-level conclusions of Selection, including
quadraticity and even equality of the full fixed spaces, do not establish
the unrestricted claim. Further source geometry is required.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.49(h),
printed p.1143; F.9.12–16, printed pp.322–324; B.1.2–3, printed p.68.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry

private theorem best_of_codim_le_two
    {K W : Type*} [Group K] [Finite K] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (rho : Representation (ZMod 2) K W)
    (hfaithful : Function.Injective rho) {A : Subgroup K}
    (hA : IsOffender rho A) (hcodim : fixedCodim rho A ≤ 2) : IsBestOffender rho A := by
  refine ⟨hA.1, fun B hBA => ?_⟩
  by_cases he : B = A
  · subst B
    exact le_rfl
  by_cases hB : B = ⊥
  · simpa [hB] using (fixedCodim_le_rank_iff rho A).mp hA.2
  have hBe := hA.1.of_le hBA hB
  have hr : rank B < rank A := by
    by_contra hn
    have hc := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hn)
    rw [← hA.1.card_eq_two_pow_rank, ← hBe.card_eq_two_pow_rank] at hc
    exact he (Subgroup.eq_of_le_of_card_ge hBA hc)
  have hpos := fixedCodim_pos_of_faithful rho hfaithful hB
  have hdimB := fixedCodim_add_finrank rho B
  have hdimA := fixedCodim_add_finrank rho A
  unfold weight
  omega

private theorem failure_of_best_of_codim_le_three
    {K W : Type*} [Group K] [Finite K] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (rho : Representation (ZMod 2) K W)
    (hfaithful : Function.Injective rho) {A : Subgroup K}
    (hA : IsOffender rho A) (hcodim : fixedCodim rho A ≤ 3)
    (hnot : ¬ IsBestOffender rho A) :
    fixedCodim rho A = 3 ∧ ∃ B < A,
      rank A = rank B + 1 ∧ fixedCodim rho B = 1 ∧ IsStrongOffender rho B := by
  classical
  have hbad : ∃ B ≤ A, weight rho A < weight rho B := by
    by_contra hn
    apply hnot
    refine ⟨hA.1, fun B hBA => ?_⟩
    exact le_of_not_gt (fun h => hn ⟨B, hBA, h⟩)
  obtain ⟨B, hBA, hweight⟩ := hbad
  have hB : B ≠ ⊥ := by
    intro he
    rw [he, weight_bot] at hweight
    exact (not_lt_of_ge ((fixedCodim_le_rank_iff rho A).mp hA.2)) hweight
  have hBe := hA.1.of_le hBA hB
  have he : B ≠ A := by
    intro he
    subst B
    exact (Nat.lt_irrefl _) hweight
  have hr : rank B < rank A := by
    by_contra hn
    have hc := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hn)
    rw [← hA.1.card_eq_two_pow_rank, ← hBe.card_eq_two_pow_rank] at hc
    exact he (Subgroup.eq_of_le_of_card_ge hBA hc)
  have hpos := fixedCodim_pos_of_faithful rho hfaithful hB
  have hdimB := fixedCodim_add_finrank rho B
  have hdimA := fixedCodim_add_finrank rho A
  have hoff := hA.2
  unfold weight at hweight
  refine ⟨by omega, B, lt_of_le_of_ne hBA he, by omega, by omega, hBe, ?_⟩
  omega

private theorem codim_bound
    {K W : Type*} [Group K] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (rho : Representation (ZMod 2) K W)
    (D : Submodule (ZMod 2) W) (A : Subgroup K)
    {n : ℕ} (hD : D ≤ fixedSpace rho A) (hcodim : Module.finrank (ZMod 2) (W ⧸ D) ≤ n) :
    fixedCodim rho A ≤ n := by
  have hmono := Submodule.finrank_mono hD
  have hd := D.finrank_quotient_add_finrank
  have ha := fixedCodim_add_finrank rho A
  omega

variable {G : Type*} [Group G] [Finite G]

/-- Both actual endpoint images are quadratic best offenders in the branch
where U_H/D_H has dimension at most two. The final corank premise is a branch
condition, not a claimed consequence of F.9.16 or of 15.3.49(a)–(f). -/
theorem selected_best_offenders_of_corank_le_two
    (V ZS Z H K : Subgroup G) (t : G)
    [IsElementaryAbelian 2 (localSpan ZS H)]
    [IsElementaryAbelian 2 (localSpan (ZS.map (MulAut.conj t).toMonoidHom) K)]
    [IsElementaryAbelian 2 (localSpan (V.map (MulAut.conj t).toMonoidHom) K)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hZS : ZS ≤ V)
    (hVgH : localSpan (V.map (MulAut.conj t).toMonoidHom) K ≤ H)
    (hHZ : H ≤ centralizer (Z : Set G))
    (hUHZg : localSpan ZS H ≤ normalizer (Z.map (MulAut.conj t).toMonoidHom : Set G))
    (hcross : sectionCentralizer (localSpan V H)
      (localSpan (ZS.map (MulAut.conj t).toMonoidHom) K)
      (Z.map (MulAut.conj t).toMonoidHom) ≤
        centralizer (localSpan (V.map (MulAut.conj t).toMonoidHom) K : Set G))
    (hcomm : ⁅localSpan ZS H, localSpan (V.map (MulAut.conj t).toMonoidHom) K⁆ ≤
      localSpan (V.map (MulAut.conj t).toMonoidHom) K)
    (hselected : 0 < Nat.log 2 ((sectionCentralizer
        (localSpan (ZS.map (MulAut.conj t).toMonoidHom) K) (localSpan ZS H) Z).relIndex
          (localSpan (ZS.map (MulAut.conj t).toMonoidHom) K)) ∧
      Nat.log 2 ((sectionCentralizer (localSpan ZS H)
        (localSpan (ZS.map (MulAut.conj t).toMonoidHom) K)
        (Z.map (MulAut.conj t).toMonoidHom)).relIndex (localSpan ZS H)) ≤
      Nat.log 2 ((sectionCentralizer (localSpan (ZS.map (MulAut.conj t).toMonoidHom) K)
        (localSpan ZS H) Z).relIndex (localSpan (ZS.map (MulAut.conj t).toMonoidHom) K)))
    (hcorank : Nat.log 2 ((sectionCentralizer (localSpan ZS H)
      (localSpan (ZS.map (MulAut.conj t).toMonoidHom) K)
      (Z.map (MulAut.conj t).toMonoidHom)).relIndex (localSpan ZS H)) ≤ 2) :
    IsBestOffender action.representation
        (starImage H (localSpan (ZS.map (MulAut.conj t).toMonoidHom) K)) ∧
      IsBestOffender action.representation
        (starImage H (localSpan (V.map (MulAut.conj t).toMonoidHom) K)) ∧
      IsQuadratic action.representation
        (starImage H (localSpan (ZS.map (MulAut.conj t).toMonoidHom) K)) ∧
      IsQuadratic action.representation
        (starImage H (localSpan (V.map (MulAut.conj t).toMonoidHom) K)) := by
  let Ug := localSpan (ZS.map (MulAut.conj t).toMonoidHom) K
  let Vg := localSpan (V.map (MulAut.conj t).toMonoidHom) K
  let Zg := Z.map (MulAut.conj t).toMonoidHom
  let D := sectionImage (localSpan ZS H) Z (sectionCentralizer (localSpan ZS H) Ug Zg)
  have hUV : Ug ≤ Vg := conjugateSpanBy_mono (map_mono hZS) le_rfl
  obtain ⟨hfixed, _, hU, hV, hquadU, hquadV⟩ :=
    selected_rank_and_quadratic_offenders V ZS Z H Ug Vg Zg action
      hZS hUV hVgH hHZ hUHZg hcross hcomm hselected
  have hZD : Z ≤ sectionCentralizer (localSpan ZS H) Ug Zg := by
    apply le_commutatorPreimage action.layer_le
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp ((hUV.trans hVgH).trans hHZ))).le.trans bot_le
  have hdim : Module.finrank (ZMod 2)
      (Additive (localSpan ZS H ⧸ Z.subgroupOf (localSpan ZS H)) ⧸ D) ≤ 2 := by
    rw [sectionImage_quotient_finrank _ _ _ hZD]
    exact hcorank
  have hstar : starImage H Ug ≤ starImage H Vg := map_mono (fun _ hx => hUV hx)
  have hDsmall : D ≤ fixedSpace action.representation (starImage H Ug) := by
    intro v hv a
    exact hfixed hv ⟨a, hstar a.property⟩
  exact ⟨best_of_codim_le_two action.representation action.faithful hU
      (codim_bound _ D _ hDsmall hdim),
    best_of_codim_le_two action.representation action.faithful hV
      (codim_bound _ D _ hfixed hdim), hquadU, hquadV⟩
/-- The first unresolved corank is exactly three. If either actual selected
image fails the B.1.2 comparisons in this branch, that same image has a
proper hyperplane subgroup of rank at least two fixing a hyperplane of the
module. The subgroup is quadratic and strong. Excluding this configuration
requires further geometry; no such exclusion or corank bound is asserted. -/
theorem selected_hyperplane_obstruction_of_corank_le_three
    (V ZS Z H K : Subgroup G) (t : G)
    [IsElementaryAbelian 2 (localSpan ZS H)]
    [IsElementaryAbelian 2 (localSpan (ZS.map (MulAut.conj t).toMonoidHom) K)]
    [IsElementaryAbelian 2 (localSpan (V.map (MulAut.conj t).toMonoidHom) K)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hZS : ZS ≤ V)
    (hVgH : localSpan (V.map (MulAut.conj t).toMonoidHom) K ≤ H)
    (hHZ : H ≤ centralizer (Z : Set G))
    (hUHZg : localSpan ZS H ≤ normalizer (Z.map (MulAut.conj t).toMonoidHom : Set G))
    (hcross : sectionCentralizer (localSpan V H)
      (localSpan (ZS.map (MulAut.conj t).toMonoidHom) K)
      (Z.map (MulAut.conj t).toMonoidHom) ≤
        centralizer (localSpan (V.map (MulAut.conj t).toMonoidHom) K : Set G))
    (hcomm : ⁅localSpan ZS H, localSpan (V.map (MulAut.conj t).toMonoidHom) K⁆ ≤
      localSpan (V.map (MulAut.conj t).toMonoidHom) K)
    (hselected : 0 < Nat.log 2 ((sectionCentralizer
        (localSpan (ZS.map (MulAut.conj t).toMonoidHom) K) (localSpan ZS H) Z).relIndex
          (localSpan (ZS.map (MulAut.conj t).toMonoidHom) K)) ∧
      Nat.log 2 ((sectionCentralizer (localSpan ZS H)
        (localSpan (ZS.map (MulAut.conj t).toMonoidHom) K)
        (Z.map (MulAut.conj t).toMonoidHom)).relIndex (localSpan ZS H)) ≤
      Nat.log 2 ((sectionCentralizer (localSpan (ZS.map (MulAut.conj t).toMonoidHom) K)
        (localSpan ZS H) Z).relIndex (localSpan (ZS.map (MulAut.conj t).toMonoidHom) K)))
    (hcorank : Nat.log 2 ((sectionCentralizer (localSpan ZS H)
      (localSpan (ZS.map (MulAut.conj t).toMonoidHom) K)
      (Z.map (MulAut.conj t).toMonoidHom)).relIndex (localSpan ZS H)) ≤ 3)
    (hfailure : ¬ (IsBestOffender action.representation
        (starImage H (localSpan (ZS.map (MulAut.conj t).toMonoidHom) K)) ∧
      IsBestOffender action.representation
        (starImage H (localSpan (V.map (MulAut.conj t).toMonoidHom) K)))) :
    ∃ A B : Subgroup (H ⧸ pCore 2 H),
      (A = starImage H (localSpan (ZS.map (MulAut.conj t).toMonoidHom) K) ∨
        A = starImage H (localSpan (V.map (MulAut.conj t).toMonoidHom) K)) ∧
      B < A ∧ fixedCodim action.representation A = 3 ∧
      rank A = rank B + 1 ∧ fixedCodim action.representation B = 1 ∧
      2 ≤ rank B ∧ IsStrongOffender action.representation B ∧
      IsQuadratic action.representation B := by
  let Ug := localSpan (ZS.map (MulAut.conj t).toMonoidHom) K
  let Vg := localSpan (V.map (MulAut.conj t).toMonoidHom) K
  let Zg := Z.map (MulAut.conj t).toMonoidHom
  let D := sectionImage (localSpan ZS H) Z (sectionCentralizer (localSpan ZS H) Ug Zg)
  have hUV : Ug ≤ Vg := conjugateSpanBy_mono (map_mono hZS) le_rfl
  obtain ⟨hfixed, _, hU, hV, hquadU, hquadV⟩ :=
    selected_rank_and_quadratic_offenders V ZS Z H Ug Vg Zg action
      hZS hUV hVgH hHZ hUHZg hcross hcomm hselected
  have hZD : Z ≤ sectionCentralizer (localSpan ZS H) Ug Zg := by
    apply le_commutatorPreimage action.layer_le
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp ((hUV.trans hVgH).trans hHZ))).le.trans bot_le
  have hdim : Module.finrank (ZMod 2)
      (Additive (localSpan ZS H ⧸ Z.subgroupOf (localSpan ZS H)) ⧸ D) ≤ 3 := by
    rw [sectionImage_quotient_finrank _ _ _ hZD]
    exact hcorank
  have hstar : starImage H Ug ≤ starImage H Vg := map_mono (fun _ hx => hUV hx)
  have hDsmall : D ≤ fixedSpace action.representation (starImage H Ug) := by
    intro v hv a
    exact hfixed hv ⟨a, hstar a.property⟩
  have hcase (A : Subgroup (H ⧸ pCore 2 H))
      (heq : A = starImage H Ug ∨ A = starImage H Vg)
      (hoff : IsOffender action.representation A)
      (hc : fixedCodim action.representation A ≤ 3)
      (hq : IsQuadratic action.representation A)
      (hn : ¬ IsBestOffender action.representation A) :
      ∃ A B : Subgroup (H ⧸ pCore 2 H),
        (A = starImage H Ug ∨ A = starImage H Vg) ∧
        B < A ∧ fixedCodim action.representation A = 3 ∧
        rank A = rank B + 1 ∧ fixedCodim action.representation B = 1 ∧
        2 ≤ rank B ∧ IsStrongOffender action.representation B ∧
        IsQuadratic action.representation B := by
    obtain ⟨hcodim, B, hBA, hr, hBcodim, hstrong⟩ :=
      failure_of_best_of_codim_le_three action.representation action.faithful hoff hc hn
    refine ⟨A, B, heq, hBA, hcodim, hr, hBcodim, ?_, hstrong, ?_⟩
    · have := hoff.2
      omega
    · exact fun a ha b hb v => hq a (hBA.le ha) b (hBA.le hb) v
  by_cases hbestU : IsBestOffender action.representation (starImage H Ug)
  · exact hcase _ (Or.inr rfl) hV (codim_bound _ D _ hfixed hdim) hquadV
      (fun hbestV => hfailure ⟨hbestU, hbestV⟩)
  · exact hcase _ (Or.inl rfl) hU (codim_bound _ D _ hDsmall hdim) hquadU hbestU

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry
