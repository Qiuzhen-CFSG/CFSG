module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.PointCubic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.OmegaCenter
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesComplete

/-!
# Original comparison reduced to the whole-center Hall displacement

The completed guarded source 3.2.5 theorem is instantiated at the same
original Sylow using S.many. Thus no separate Source325Alternatives input
remains in the normalizer-contained equality or the escaping-block result.

In a strict comparison, maximality, quasisimplicity, the full model sieve
and inner radical placement construct a full odd Sylow actor of the literal
radical normalizer. It has rank two, fixes the original z, and its action on
the whole omega-center is the quotient-normalizer action constructed in
Hall.OmegaCenter. The remaining block identity forces its displacement to
have order less than q. All original block clauses are retained.

The model lower bound on this same whole-center action remains with
qt-d-1222-shadow-component-comparison. The positive normalized-module
implication retains qt-d-1222-normalized-nonff, and earlier geometry retains
final discharge by qt-d-1222-shadow-components. This is not full 11.4.2.
Source: Aschbacher–Smith 11.4.2, printed pp.776–777, and 11.1.5.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
open Quasisimple Quasisimple.Hall Overcomponent.EmbeddingProof
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- Source 3.2.5 is instantiated at every chosen module using the same
original Sylow and the already present multiple-overgroup hypothesis. -/
theorem ofFlag_eq_of_normalizer_of_positive_source
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      PSL(2,S.field.Carrier))
    (hpositive : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ (J : Subgroup G),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      ∀ (W : Subgroup G) (D : Chapter12.Section02.ChosenModule T J W),
        IsFFModule D.sourceOrbitNormalizerRepresentation ∨
          Chapter7.NormalizedSource.OrthogonalMinusAlternative D.orbitRepresentation D.orbitComponent)
    (hNM : normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G)) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K :=
  ofFlag_eq_of_normalizer_of_normalized_source S f X z H h hlinear h1132 hcent hline hXR e
    (fun _ hJ _ D' => D'.source325_of_many hJ S.many) hpositive hNM

/-- The remaining original block supplies a full Sylow Hall actor, with
its nontrivial fixed point and strict whole-center displacement bound. -/
theorem ofFlag_eq_or_omegaCenter_sylow_bound
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      PSL(2,S.field.Carrier))
    (hpositive : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ (J : Subgroup G),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      ∀ (W : Subgroup G) (D : Chapter12.Section02.ChosenModule T J W),
        IsFFModule D.sourceOrbitNormalizerRepresentation ∨
          Chapter7.NormalizedSource.OrthogonalMinusAlternative D.orbitRepresentation D.orbitComponent)
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V
      (ofFlag S f X z H).V₁ (ofFlag S f X z H).R₁ (normalizer (L : Set G)) L S.field.degree) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K ∨
      (((ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) ∧
        V = Source.conjugateSpan (normalizer (L : Set G)) V ∧
        (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧
        (ofFlag S f X z H).V₁ = radicalOmega (ofFlag S f X z H) ∧
        ¬ normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G)) ∧
      ∃ (p : ℕ) (P : Sylow p (normalizer
        (radical (ofFlag S f X z H) : Set (localGroup (ofFlag S f X z H))))),
        p.Prime ∧ Odd p ∧ p ∣ 2^S.field.degree - 1 ∧
        radicalSylowActor (ofFlag S f X z H) p P ≤ (ofFlag S f X z H).Kz ∧
        radicalSylowActor (ofFlag S f X z H) p P ≤ normalizer ((ofFlag S f X z H).R₁ : Set G) ∧
        2 ≤ primeRank p (radicalSylowActor (ofFlag S f X z H) p P) ∧
        z ∈ radicalOmega (ofFlag S f X z H) ⊓
          centralizer (radicalSylowActor (ofFlag S f X z H) p P : Set G) ∧
        Nat.card (⁅radicalOmega (ofFlag S f X z H),
          radicalSylowActor (ofFlag S f X z H) p P⁆ : Subgroup G) < 2^S.field.degree) := by
  have h325 := fun (J : Subgroup G)
    (hJ : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J)
    (W : Subgroup G) (D' : Chapter12.Section02.ChosenModule T J W) =>
      D'.source325_of_many hJ S.many
  by_cases hne : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K
  · exact .inl hne
  obtain he | hb := ofFlag_eq_or_block_of_normalized_source S f X z H h hlinear h1132
    hcent hline hXR e h325 hpositive hradical
  · exact .inl he
  have hs := ofFlag_point_mem_LStar_of_normalized_source S f X z H h hne hlinear h1132 e hcent
    h325 hpositive
  let := ofFlag_point_quasisimple_of_maximal S f X z H h hlinear h1132 hcent hline hXR e hne hs
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  have hc := ofFlag_overcomponent_alternative S f X z H e h.point_mem_local_family le_rfl
  have hm := Quasisimple.Classification.ofFlag_rankTwo_of_componentAlternative
    S f X z H h hne hs hlinear h1132 hcent hline hXR hc e
  have hi := rankTwo_radical_image_le_component (ofFlag S f X z H)
    h hf hne hs hcent (f.invariant 0) e hm
  have hn : 2 ≤ S.field.degree := by have := S.nonbinary; omega
  have hpow : 4 ≤ 2^S.field.degree :=
    pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) hn
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (show 2^S.field.degree - 1 ≠ 1 by omega)
  let : Fact p.Prime := ⟨hp⟩
  have ho : Odd p := hp.odd_of_ne_two (by
    intro he
    subst p
    have h2 : 2 ∣ 2^S.field.degree := dvd_pow_self 2 (by have := S.nonbinary; omega)
    have hx := Nat.mod_eq_zero_of_dvd hd
    have hy := Nat.mod_eq_zero_of_dvd h2
    omega)
  let P : Sylow p (normalizer (radical (ofFlag S f X z H) : Set (localGroup (ofFlag S f X z H)))) := default
  obtain ⟨hYK,hYR,hY,hrY⟩ := radicalSylowActor_properties (ofFlag S f X z H)
    h hf hne hs hcent hm hi ho hd P
  exact .inr ⟨hb,p,P,hp,ho,hd,hYK,hYR,hrY,
    point_mem_radicalOmega_fixed (ofFlag S f X z H) h hs hcent _ hYK,
    ofFlag_radicalOmega_moved_card_lt_field S f X z H h hf hs hcent hb.2.2.2.1
      ho _ hYK hYR hY⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
