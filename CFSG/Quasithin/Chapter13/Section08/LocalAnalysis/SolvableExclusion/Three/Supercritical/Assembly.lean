module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Frattini
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.Supercritical.SourceAssembly

/-!
# The small odd reduction with prime three or five

A.1.21 supplies the supercritical subgroup and coprime detection; the proved
A.1.24 discharges its rank-two structure premise. Nontriviality of the
13.8.8(2) actor Uγ* passes to Vα* through the actual conjugator h ∈ H.
The construction then chooses a minimal moved normal image and lifts it to
an actual odd subgroup P ≤ H. Its Frattini action is irreducible by the
minimal-movement argument, and the offender selection in P*Uγ* supplies
all local hypotheses of D.2.13(1).

`exists_reducedOdd` is the first two paragraphs of the 13.8.13 reduction,
for the selected critical pair of 13.8.8(2). The only universal Appendix
implication still supplied is D.2.13(1); A.1.21 and A.1.24 are discharged.
The exact 13.8.12 residual alternative and the genuine earlier quadratic
membership on U_H/V₁ remain explicit source inputs. `SourceApplication`
constructs that action and membership from the earlier geometric inputs.
No irreducibility, small odd subgroup, or moving minimal offender is assumed.
The subsequent exclusions of the three-primary branches belong to Three.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.1.21 and
A.1.24, printed pp.24–25; 13.8.8(2) and 13.8.13, pp.949–951.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Supercritical
open CFSG.Quasithin.Chapter1.XiEmbedding
universe u

/-- The proved A.1.24 supplies exactly the structure input of the construction. -/
theorem source_rankTwoStructure : RankTwoStructure.{u} := by
  intro p _ ho Y _ _ hp hω hr hc
  let _ := hp.isNilpotent
  have hd : _root_.commutator Y ≤ center Y := by
    apply commutator_top_right_eq_bot_iff_le_center.mp
    have h := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hc
    rw [show 2 = 1 + 1 from rfl, Subgroup.lowerCentralSeries_succ,
      top_lowerCentralSeries_one] at h
    exact h
  have hp2 : p ≠ 2 := by rintro rfl; obtain ⟨k, hk⟩ := ho; omega
  rcases ChapterA.lemma_A_1_24 hp2 hp hω hd hr with ⟨hcard, _⟩ | ⟨hcard, he, _⟩
  · exact Or.inl ⟨{
      toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
      exponent_dvd_p := (ChapterA.lemma_A_1_24_exponent hp2 hω hd hr).dvd }, hcard⟩
  · exact Or.inr ⟨he, hcard⟩

variable {G : Type u} [Group G] [Finite G]

/-- Construct the required small odd reduction for the genuine selected actor
of 13.8.8(2), including its Frattini irreducibility and prime restriction. -/
theorem exists_reducedOdd
    (hD213 : Offenders.D213PrimeRestriction.{u, u})
    {H Z L L₁ L₁plus T G₁ M V Vα V₃ V₁ : Subgroup G}
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (hs : Group.IsSolvable H) (hr : IsStronglyQuasithin H)
    (hZ : Z ≠ ⊥) (hpZ : IsPGroup 2 Z) (hZLT : Z ≤ L₁ ⊔ T)
    (hGZ : G₁ ≤ normalizer (Z : Set G))
    (hH : Minimal (· ∈ Source.Hz L₁ T G₁ M) H)
    (hres : ResidualAlternative L L₁ L₁plus (residualInM H M))
    (hplus : L₁plus ≤ L₁)
    (e : CriticalGeometry.CriticalPair L T H V) (hV₃ : V₃ ≤ V) (h : H)
    (hα : e.Vgamma.map (MulAut.conj (h : G)).toMonoidHom = Vα)
    (hplace : Vα ≤ (L₁ ⊔ T).pCoreIn 2)
    (a : Five.StarAction H (Source.UH H V₃) V₁)
    (hk : Source.QH H = commutatorPreimage H (Source.UH H V₃) V₁)
    (hQ : CriticalGeometry.Reorientation.QuadraticMember (Offenders.linearAction a)
      (Source.starImage H (e.Ugamma V₃))) :
    ∃ p, (p = 3 ∨ p = 5) ∧ Nonempty (ReducedOdd p H L₁ T M Vα) := by
  have hpA : IsPGroup 2 Vα :=
    ((isPGroup_pCoreIn 2 (L₁ ⊔ T)).to_subgroup
      (Vα.subgroupOf ((L₁ ⊔ T).pCoreIn 2))).of_equiv (subgroupOfEquivOfLe hplace)
  have hne : Source.starImage H Vα ≠ ⊥ := by
    intro hz
    apply hQ.1.1
    apply bot_unique
    rintro _ ⟨x, hx, rfl⟩
    let q := QuotientGroup.mk' (pCore 2 H)
    have hxV : (x : G) ∈ e.Vgamma :=
      map_mono (conjugateSpanBy_mono hV₃ le_rfl) hx
    have hm : q (h * x * h⁻¹) ∈ Source.starImage H Vα := by
      refine ⟨h * x * h⁻¹, ?_, rfl⟩
      rw [← hα]
      exact mem_map_of_mem (MulAut.conj (h : G)).toMonoidHom hxV
    have he : q h * q x * (q h)⁻¹ = 1 := by
      simpa only [hz, mem_bot, map_mul, map_inv] using hm
    exact mem_bot.mpr
      (mul_left_cancel ((mul_inv_eq_one.mp he).trans (mul_one (q h)).symm))
  obtain ⟨p, ⟨c⟩⟩ := exists_oddConstruction source_supercriticalExistence
    source_supercriticalCoprimeDetection source_rankTwoStructure hs hr hpA hne
    hZ hpZ hZLT hGZ hH hplace hres hplus
  exact ⟨p, Offenders.prime_restriction_on_Utilde hD213 c e hV₃ h hα hplace a hk hQ,
    ⟨{ prime := c.prime
       odd := c.odd
       P := c.P
       P_le := c.P_le
       P_isPGroup := c.P_isPGroup
       Pstar_small := c.Pstar_small
       Pstar_normal := c.Pstar_normal
       moved := c.moved
       outside := c.outside
       generated := c.generated
       irreducible := c.starFrattiniIrreducible hplace }⟩⟩

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Supercritical

end
