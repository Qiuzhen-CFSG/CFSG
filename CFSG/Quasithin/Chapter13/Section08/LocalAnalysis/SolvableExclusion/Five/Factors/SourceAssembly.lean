module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.EqualityCase
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Decomposition
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.ActorAlternatives
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Exclusion
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.FinalAssembly
public import Theory.Representation.BinaryOffender.CubicEndField

/-!
# Constructing the five-primary rank-one action

Starting with the supplied five-primary reduction and genuine minimal solvable
membership in Hz, ambient quasithinness bounds the five-rank of H. The source
kernel identity constructs a faithful action on the literal U_H/V₁. The exact
universal D.2.13(1–2) input, localized inside P*Uγ*, constructs a canonical
five-commutator. Frattini irreducibility and D.2.12 then construct all the
factors in the supplied P, with their independent supports of order sixteen.
This checked D.2.13 route avoids assuming that H* satisfies the additional
indecomposable hypotheses of D.2.17.

The endpoint construction gives both actor alternatives, including the full
fixed index and displacement order sixteen in the order-four case. The
selected rank comparison makes the F.9.16 index chain an equality. Binary
pairing then identifies the actual centralizer and puts the common center
in U_H. Faithfulness on the image of D_H follows from the source kernel and
the disjoint lines. Both involution factors act nontrivially there; their
moved planes contain the same line and cannot generate a space of order
sixteen. Thus the surviving factors have a rank-one actor, factor zero is
moved, every other factor is fixed, and the full displacement has order four.

The explicit earlier inputs are the standing flag, the exact source kernel,
elementary abelianness from 13.8.2, F.9.11/13/15 (`EarlierGeometry`), and the
selected endpoint's rank comparison, Q-membership and core placement from
13.8.8(2). The independent universal D.2.13 producer is `qt-d-02`; the
universal geometry producer is `qt-f09-geometry`. Their source assembly
remains upstream. No factor, actor-rank, common-center or solvable-exclusion
conclusion is an input. Final localization and solvable exclusion remain
with the parent 13.8.13 theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951 (PDF p.968), D.2.12–13, pp.183–185, and F.9.16(2), pp.323–324.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
universe u
variable {G : Type u} [Group G] [Finite G]
variable {H U Z : Subgroup G} [(Z.subgroupOf U).Normal]

open Representation.BinaryOffender
open Three.Supercritical.Offenders
open CriticalGeometry CriticalGeometry.Reorientation

/-- D.2.1's ratio bound is the squared-order bound on the literal quotient. -/
theorem StarAction.fixed_index_le_square_of_Q [IsElementaryAbelian 2 U]
    (a : StarAction H U Z) (B : Subgroup G)
    (hQ : Source.starImage H B ∈ ChapterD.Q (linearAction a)) :
    (FixedPoints.subgroup (a.actors B) (U ⧸ Z.subgroupOf U)).index ≤
      Nat.card (Source.starImage H B) ^ 2 := by
  let F := FixedPoints.subgroup (a.actors B) (U ⧸ Z.subgroupOf U)
  let C := fixedSpace (linearAction a) (Source.starImage H B)
  have he : Nat.card F = Nat.card C := by
    apply Nat.card_congr
    exact {
      toFun := fun x => ⟨Additive.ofMul x.val, fun g =>
        x.property ⟨a.action g, mem_map_of_mem a.action g.property⟩⟩
      invFun := fun x => ⟨x.val.toMul, by
        rintro ⟨b, ⟨g, hg, rfl⟩⟩
        exact x.property ⟨g, hg⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc := (fixedCodim_le_mul_rank_iff_card_pow (linearAction a)
    (Source.starImage H B) hQ.1 2).mp
      ((actionRatio_le_nat_iff (linearAction a) hQ.1 2).mp hQ.2.2)
  change Nat.card (U ⧸ Z.subgroupOf U) ≤ Nat.card (Source.starImage H B) ^ 2 * Nat.card C at hc
  rw [← he, ← F.index_mul_card] at hc
  have hp : 0 < Nat.card F := Nat.card_pos
  nlinarith only [hc, hp]

/-- Nontrivial local two-core places H in a genuine two-local normalizer,
so ambient quasithinness supplies the five-rank bound. -/
theorem five_rank_le_of_source_member {L₁ T G₁ M : Subgroup G}
    (hqt : _root_.IsQuasithin G) (hH : H ∈ Source.Hz L₁ T G₁ M) : primeRank 5 H ≤ 2 := by
  have hn : H ≤ normalizer (Source.QH H : Set G) :=
    H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hlocal : IsTwoLocal (normalizer (Source.QH H : Set G)) :=
    ⟨Source.QH H, hH.1.1, isPGroup_pCoreIn 2 H, rfl⟩
  exact (Theory.GroupTheory.primeRank_le_of_injective 5 (inclusion hn)
    (inclusion_injective hn)).trans
      (Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hqt _ hlocal 5 (by decide) (by decide))

/-- Construct the rank-one factors from the literal critical endpoint,
source five-primary reduction, and the consumed standing/earlier conclusions.
The sole universal classification input is D.2.13(1--2); the required
F.9.16 equality calculation is proved by binary pairing in this development.
Neither factor existence nor either actor alternative is a premise. -/
theorem rankOneFactors_of_critical_pair
    {L T V V₃ V₁ L₁ G₁ M Vα : Subgroup G}
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    (src : SourceD213PrimeInput.{u})
    (r : ReducedFive H L₁ T M Vα)
    (c : CriticalPair L T H V)
    (a : StarAction H (Source.UH H V₃) V₁)
    (hqt : _root_.IsQuasithin G)
    (hminimal : Minimal (· ∈ Source.Hz L₁ T G₁ M) H)
    (hsolvable : Group.IsSolvable H)
    (hV₃ : V₃ ≤ V) (hline : V₁ ≤ V₃) (hcard : Nat.card V₁ = 2)
    (hz : G₁ ≤ normalizer (V₁ : Set G))
    (hk : Source.QH H = commutatorPreimage H (Source.UH H V₃) V₁)
    (hgeo : EarlierGeometry c V₃ V₁)
    (hcomp : denominatorRank V₃ V₁ c ≤ rank (Source.starImage H (c.Ugamma V₃)))
    (hQ : Source.starImage H (c.Ugamma V₃) ∈ ChapterD.Q (linearAction a))
    (hplacement : ∃ h : H,
      c.Vgamma.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    Nonempty (RankOneFactors a r.P (c.Ugamma V₃)) := by
  let _ := hsolvable
  let _ : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le (B := Source.VH H V) (le_conjugateSpanBy V H)
  let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  have hfaith := a.injective_of_kernel hk
  have hzH := hminimal.prop.2.1.trans hz
  have hV₁ : V₁ ≤ Source.UH H V₃ := hline.trans (le_conjugateSpanBy V₃ H)
  have hγH : c.Ugamma V₃ ≤ H :=
    (map_mono (conjugateSpanBy_mono hV₃ le_rfl)).trans hgeo.Vgamma_H
  have hUend : Source.UH H V₃ ≤ vertexGroup L T H c.gamma :=
    (conjugateSpanBy_mono hV₃ le_rfl).trans hgeo.VH_endpoint
  have hn : Source.UH H V₃ ≤ normalizer (c.Ugamma V₃ : Set G) :=
    hUend.trans (c.normalizes_Ugamma V₃)
  have hnA : Source.UH H V₃ ≤ normalizer (c.Aone V₁ : Set G) := by
    have hh := map_mono (f := (MulAut.conj (c.gb : G)).toMonoidHom) hzH
    rw [map_equiv_normalizer_eq, ← c.vertexGroup_gamma] at hh
    exact hUend.trans hh
  have hAγ : c.Aone V₁ ≤ c.Ugamma V₃ := map_mono hV₁
  have hAc : Nat.card (c.Aone V₁) = 2 :=
    (card_map_of_injective (MulAut.conj (c.gb : G)).injective).trans hcard
  have hp : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃ := by
    apply lt_of_le_of_ne (commutatorPreimage_le _ _ _)
    intro he
    have hi := dgamma_index_eq_star_card (c.Ugamma V₃) hγH hzH hk
    change Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃ at he
    rw [he, relIndex_self] at hi
    exact hQ.1.1 (card_eq_one.mp hi.symm)
  obtain ⟨h, hplace⟩ := hplacement
  obtain ⟨f⟩ := factorization_of_critical_pair src r c a hfaith
    (five_rank_le_of_source_member hqt hminimal.prop) hV₃ hQ h hplace
  apply rankOneFactors_of_alternatives a r.P (c.Ugamma V₃) (c.Aone V₁)
  · exact ActorAlternatives.exists_rank_alternatives c a hfaith r f hminimal hsolvable
      hV₃ hV₁ hn hgeo.Dgamma_kernel hp
      (a.fixed_index_le_square_of_Q _ hQ) ⟨h, hplace⟩
  · intro hactor hfixed
    have hi := c.index_comparison_of_selected_rank V₃ V₁ hγH hgeo.Dgamma_kernel hcomp
    obtain ⟨hAU, hindex, hcentralizer⟩ := rank_two_equality_case a (c.Ugamma V₃)
      (c.Aone V₁) hγH hzH hk hAγ hAc hnA hgeo.cross_centralizes hi hactor hfixed
    exact commonCenterOnDH_of_centralizer_equality a (c.Ugamma V₃) (c.Aone V₁)
      hγH hzH hk hAU hAγ hAc (disjoint_iff.mpr hgeo.lines_disjoint)
      hindex hactor hcentralizer

/-- Construct both the faithful action and the rank-one factors. The earlier
13.8.8(2) conclusion is quantified over faithful realizations of the prescribed
conjugation action; `StarAction.action_eq` proves their uniqueness. The kernel
identity constructs that realization here. -/
theorem exists_faithful_rankOneFactors_of_source
    {L T V V₃ V₁ L₁ G₁ M Vα : Subgroup G}
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    (src : SourceD213PrimeInput.{u})
    (r : ReducedFive H L₁ T M Vα)
    (c : CriticalPair L T H V)
    (hqt : _root_.IsQuasithin G)
    (hminimal : Minimal (· ∈ Source.Hz L₁ T G₁ M) H)
    (hsolvable : Group.IsSolvable H)
    (hV₃ : V₃ ≤ V) (hline : V₁ ≤ V₃) (hcard : Nat.card V₁ = 2)
    (hz : G₁ ≤ normalizer (V₁ : Set G))
    (hk : Source.QH H = commutatorPreimage H (Source.UH H V₃) V₁)
    (hgeo : EarlierGeometry c V₃ V₁)
    (hcomp : denominatorRank V₃ V₁ c ≤ rank (Source.starImage H (c.Ugamma V₃)))
    (hQ : ∀ a : StarAction H (Source.UH H V₃) V₁, Function.Injective a.action →
      Source.starImage H (c.Ugamma V₃) ∈ ChapterD.Q (linearAction a))
    (hplacement : ∃ h : H,
      c.Vgamma.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    ∃ a : StarAction H (Source.UH H V₃) V₁,
      Function.Injective a.action ∧ Nonempty (RankOneFactors a r.P (c.Ugamma V₃)) := by
  obtain ⟨a, ha⟩ := exists_faithful_source_starAction H V₃ V₁
    (hminimal.prop.2.1.trans hz) hk
  exact ⟨a, ha, rankOneFactors_of_critical_pair src r c a hqt hminimal hsolvable
    hV₃ hline hcard hz hk hgeo hcomp (hQ a ha) hplacement⟩

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
