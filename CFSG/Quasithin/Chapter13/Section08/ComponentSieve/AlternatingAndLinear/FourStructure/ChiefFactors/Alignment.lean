module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.Geometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.Dual
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.Models
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.Source
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.ExteriorTransport

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.ExteriorGeometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.HeadHypotheses
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.SourceInputs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource.Markings
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.NaturalSeed

/-!
# Aligning the four-dimensional maximal quotients

The marked plane stabilizer identifies the image of the generating two-space
in every natural or dual head. If both orientations occurred, the subgroup
fixing the seed would be a two-group. Thus one orientation works for all heads;
in the dual case a single contragredient automorphism changes the common actor
identification.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.25, printed pp.960–961, PDF pp.977–978.

`exists_marked_allNaturalHeads_of_source` completes this step for the literal
source action. It constructs the seed from the earlier invariant-subgroup
criterion and relative index four, obtains the marked end-node parabolic from
the covered source reduction, verifies B.4 on every maximal quotient, and excludes
the exterior square by its proved absence of invariant planes. The actual L₀*
fixes the seed and has a cubic quotient, forcing one common orientation.

The explicit earlier inputs are the genuine covered natural setup, source
component/Sylow placement, 13.2.2 factorization and normalizer bound, the original
irreducible flag section, the elementary quadratic actor of 13.8.8, and the
universal faithful-irreducible B.4 specialization. No head classification,
common orientation, marked parabolic, or exterior obstruction is an extra premise.
The subsequent six-dimensional chief-factor and central-factor arguments belong
to the parent; they are not needed to classify maximal quotients.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment
open Representation
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

/-- Natural and dual heads cannot coexist when the actual marked subgroup
fixes the generating two-space and has a nontrivial odd part. -/
theorem exists_allNaturalHeads_of_naturalOrDual
    (ρ : Representation (ZMod 2) H U) (s : GeneratingSeed ρ)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (P : Submodule (ZMod 2) NaturalSpace)
    (hP : s.parabolic.map eH.toMonoidHom = BinaryLinear.parabolic P)
    (R : Subgroup H) (hR : ∀ g ∈ R, ∀ v ∈ s.space, ρ g v = v)
    (hRodd : ¬ IsPGroup 2 R)
    (hheads : ∀ W : Subrepresentation ρ, IsCoatom W →
      IsNaturalOrDual W.quotientRepresentation eH) :
    ∃ e : H ≃* BinaryLinear.GL NaturalSpace, AllNaturalHeads ρ e := by
  classical
  by_cases hn : ∃ W : Subrepresentation ρ, IsCoatom W ∧ IsNatural W.quotientRepresentation eH
  · obtain ⟨W, hW, hN⟩ := hn
    refine ⟨eH, ?_⟩
    intro X hX
    rcases hheads X hX with hXn | hXd
    · exact hXn
    · exact False.elim (hRodd
        (two_group_of_opposite_heads ρ s eH P hP R hR W X hW.1 hX.1 hN hXd))
  · refine ⟨eH.trans dualActor, ?_⟩
    intro W hW
    rcases hheads W hW with hWn | ⟨e, he⟩
    · exact False.elim (hn ⟨W, hW, hWn⟩)
    · exact dual_is_natural W.quotientRepresentation eH e he

/-- Align the heads while retaining the actual marked parabolic in the same
coordinates. In the dual branch the plane becomes its dual annihilator. -/
theorem exists_marked_allNaturalHeads_of_naturalOrDual
    (ρ : Representation (ZMod 2) H U) (s : GeneratingSeed ρ)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (P : Submodule (ZMod 2) NaturalSpace)
    (hdim : Module.finrank (ZMod 2) P = 2)
    (hP : s.parabolic.map eH.toMonoidHom = BinaryLinear.parabolic P)
    (R : Subgroup H) (hR : ∀ g ∈ R, ∀ v ∈ s.space, ρ g v = v)
    (hRodd : ¬ IsPGroup 2 R)
    (hheads : ∀ W : Subrepresentation ρ, IsCoatom W →
      IsNaturalOrDual W.quotientRepresentation eH) :
    ∃ (e : H ≃* BinaryLinear.GL NaturalSpace) (P' : Submodule (ZMod 2) NaturalSpace),
      (e = eH ∨ e = eH.trans dualActor) ∧ Module.finrank (ZMod 2) P' = 2 ∧
      s.parabolic.map e.toMonoidHom = BinaryLinear.parabolic P' ∧ AllNaturalHeads ρ e := by
  classical
  by_cases hn : ∃ W : Subrepresentation ρ, IsCoatom W ∧ IsNatural W.quotientRepresentation eH
  · obtain ⟨W, hW, hN⟩ := hn
    refine ⟨eH, P, Or.inl rfl, hdim, hP, ?_⟩
    intro X hX
    rcases hheads X hX with hXn | hXd
    · exact hXn
    · exact False.elim (hRodd
        (two_group_of_opposite_heads ρ s eH P hP R hR W X hW.1 hX.1 hN hXd))
  · refine ⟨eH.trans dualActor, dualPlane P, Or.inr rfl, dualPlane_finrank P hdim, ?_, ?_⟩
    · change s.parabolic.map (dualActor.toMonoidHom.comp eH.toMonoidHom) = _
      rw [← Subgroup.map_map, hP, dualActor_map_parabolic]
    · intro W hW
      rcases hheads W hW with hWn | ⟨e, he⟩
      · exact False.elim (hn ⟨W, hW, hWn⟩)
      · exact dual_is_natural W.quotientRepresentation eH e he


/-- The source assembly after the marked-parabolic six-dimensional exclusion.
The alternatives are the actual equivariant models from B.4.2/B.4.5; the
marked calculation is retained as the explicit premise `hnoSix`. -/
theorem allNaturalHeads_of_headAlternatives
    (ρ : Representation (ZMod 2) H U) (s : GeneratingSeed ρ)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (P : Submodule (ZMod 2) NaturalSpace)
    (hP : s.parabolic.map eH.toMonoidHom = BinaryLinear.parabolic P)
    (R : Subgroup H) (hR : ∀ g ∈ R, ∀ v ∈ s.space, ρ g v = v)
    (hRodd : ¬ IsPGroup 2 R)
    (halt : ∀ W : Subrepresentation ρ, IsCoatom W →
      IsNaturalOrDual W.quotientRepresentation eH ∨ IsExteriorSquare W.quotientRepresentation eH)
    (hnoSix : ∀ W : Subrepresentation ρ, IsCoatom W →
      ¬ IsExteriorSquare W.quotientRepresentation eH) :
    ∃ e : H ≃* BinaryLinear.GL NaturalSpace, AllNaturalHeads ρ e := by
  apply exists_allNaturalHeads_of_naturalOrDual ρ s eH P hP R hR hRodd
  intro W hW
  rcases halt W hW with h | h
  · exact h
  · exact False.elim (hnoSix W hW h)

/-- The model calculation is restricted to the actual exterior-square action
of the marked parabolic. The source assembly must discharge `hgeometry` and
derive the representation alternatives with their B.4 hypotheses. -/
theorem exists_marked_allNaturalHeads_of_plane_obstruction
    (ρ : Representation (ZMod 2) H U) (s : GeneratingSeed ρ)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (P : Submodule (ZMod 2) NaturalSpace)
    (hdim : Module.finrank (ZMod 2) P = 2)
    (hP : s.parabolic.map eH.toMonoidHom = BinaryLinear.parabolic P)
    (R : Subgroup H) (hR : ∀ g ∈ R, ∀ v ∈ s.space, ρ g v = v)
    (hRodd : ¬ IsPGroup 2 R)
    (halt : ∀ W : Subrepresentation ρ, IsCoatom W →
      HeadAlternatives W.quotientRepresentation eH)
    (hgeometry : ∀ S : Submodule (ZMod 2) ExteriorSquare,
      Module.finrank (ZMod 2) S = 2 →
      (∀ g ∈ BinaryLinear.parabolic P, ∀ v ∈ S,
        exteriorPower.map 2 g.toLinearMap v ∈ S) → False) :
    ∃ (e : H ≃* BinaryLinear.GL NaturalSpace) (P' : Submodule (ZMod 2) NaturalSpace),
      (e = eH ∨ e = eH.trans dualActor) ∧ Module.finrank (ZMod 2) P' = 2 ∧
      s.parabolic.map e.toMonoidHom = BinaryLinear.parabolic P' ∧ AllNaturalHeads ρ e := by
  apply exists_marked_allNaturalHeads_of_naturalOrDual ρ s eH P hdim hP R hR hRodd
  intro W hW
  rcases halt W hW with h | h
  · exact h
  · exact (not_exteriorSquare_head_of_plane_obstruction ρ s eH P hP hgeometry W hW.1 h).elim

section Source
open Subgroup
open scoped commutatorElement IsMulCommutative
variable {G : Type*} [Group G] [Finite G] (H V₃ V₁ L₀ L₁ T : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- Conditional transport for the literal source action and the actual marked
subgroups. Generation, L₀*-fixation and its odd part are proved from the
conjugation identity, commutator bound and cubic quotient. The intrinsic
exterior calculation and the source parabolic identification remain explicit;
this theorem alone does not complete 13.8.25. -/
theorem exists_marked_allNaturalHeads_of_source_inputs
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    (hT : IsPGroup 2 (Source.starImage H T))
    (hstable : ∀ g : Source.starImage H (L₁ ⊔ T),
      ∀ v ∈ sourceSeedSpace H V₃ V₁, ρ g v ∈ sourceSeedSpace H V₃ V₁)
    (hirr : IsAtom (⟨sourceSeedSpace H V₃ V₁, hstable⟩ :
      Subrepresentation (ρ.comp (Source.starImage H (L₁ ⊔ T)).subtype)))
    (hseed : Module.finrank (ZMod 2) (sourceSeedSpace H V₃ V₁) = 2)
    (hL₀H : L₀ ≤ H) (hL₀ : Nat.card (L₀ ⧸ pCore 2 L₀) = 3)
    (hcomm : ⁅L₀, V₃⁆ ≤ V₁)
    (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
    (P : Submodule (ZMod 2) NaturalSpace) (hdim : Module.finrank (ZMod 2) P = 2)
    (hP : (Source.starImage H (L₁ ⊔ T)).map eH.toMonoidHom = BinaryLinear.parabolic P)
    (halt : ∀ W : Subrepresentation ρ, IsCoatom W →
      HeadAlternatives W.quotientRepresentation eH)
    (hgeometry : ∀ S : Submodule (ZMod 2) ExteriorSquare,
      Module.finrank (ZMod 2) S = 2 →
      (∀ g ∈ BinaryLinear.parabolic P, ∀ v ∈ S,
        exteriorPower.map 2 g.toLinearMap v ∈ S) → False) :
    ∃ (e : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
      (P' : Submodule (ZMod 2) NaturalSpace),
      (e = eH ∨ e = eH.trans dualActor) ∧ Module.finrank (ZMod 2) P' = 2 ∧
      (Source.starImage H (L₁ ⊔ T)).map e.toMonoidHom = BinaryLinear.parabolic P' ∧
      AllNaturalHeads ρ e := by
  have hTP : Source.starImage H T ≤ Source.starImage H (L₁ ⊔ T) := by
    rintro _ ⟨t, ht, rfl⟩
    exact mem_map_of_mem _ (show (t : G) ∈ L₁ ⊔ T from (le_sup_right : T ≤ L₁ ⊔ T) ht)
  let s := sourceSeed H V₃ V₁ ρ hρ (Source.starImage H (L₁ ⊔ T))
    (Source.starImage H T) hTP hT hstable hirr hseed
  exact exists_marked_allNaturalHeads_of_plane_obstruction ρ s eH P hdim hP
    (Source.starImage H L₀) (sourceSeed_fixed_of_commutator_le H V₃ V₁ L₀ ρ hρ hcomm)
    (starImage_not_two_of_cubic_quotient H L₀ hL₀H hL₀) halt hgeometry

end Source

section SourceAssembly
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
open Chapter2.ComponentRefinement.LieType.Binary
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LinearReduction.Parabolics
universe v
variable {G : Type v} [Group G] [Finite G]

/-- The two deleted endpoint nodes leave precisely the two-dimensional cut. -/
theorem endNodes_parabolic (b : Basis 3) (beta delta : Fin 3)
    (hend : (beta = 0 ∧ delta = 2) ∨ (beta = 2 ∧ delta = 0)) :
    fourParabolic b {beta, delta} = BinaryLinear.parabolic (cutSpace b 1) := by
  have hs : ({beta, delta} : Set (Fin 3))ᶜ = {1} := by
    rcases hend with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> ext i <;> fin_cases i <;> simp
  simp only [fourParabolic, hs, cutStabilizer, Set.mem_singleton_iff, iInf_iInf_eq_left]

/-- Compatible natural identifications for every maximal quotient of the literal
source module. The original ordered residuals and Sylow flag remain recorded
under `e₀`; the single final marking `e` is either `e₀` or its contragredient.
The source parabolic and exterior-square exclusion are proved here from the
earlier covered setup. `hirr` and `hindex` are the original V₃/V₁ statements
used already in 13.8.16, and `hA`, `hquad`, `hbound` are the earlier quadratic
actor conclusion. The only representation classification input is universal B.4. -/
theorem exists_marked_allNaturalHeads_of_source
    (H K M L T V V₁ V₃ Uγ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (d : LocalAction.NaturalSetup L T V V₁ V₃)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    (hKH : K ≤ H) (hLK : one L T V₁ ≤ K)
    (hLM : one L T V₁ ≤ M) (hTM : T ≤ M)
    (hK : (K.subgroupOf H).IsCComponent) (hKn : (K.subgroupOf H).Normal)
    (hT : Chapter1.IsSylowIn 2 T H) (hKT : K ⊔ T = H)
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hrel : ((one L T V₁).subgroupOf (H ⊓ M)).Normal)
    (hNM : normalizer (zero L : Set G) ≤ M)
    (eK : (K ⧸ pCore 2 K) ≃* PSL 4)
    (hindex : V₁.relIndex V₃ = 4)
    (hirr : ∀ X : Subgroup G, V₁ ≤ X → X ≤ V₃ →
      one L T V₁ ≤ normalizer (X : Set G) → X = V₁ ∨ X = V₃)
    (hA : IsElementaryTwo (Source.starImage H Uγ))
    (hquad : IsQuadratic ρ (Source.starImage H Uγ))
    (hbound : fixedCodim ρ (Source.starImage H Uγ) ≤ 2 * rank (Source.starImage H Uγ))
    (hB4 : ∀ e : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace, LinearB4.{v} e) :
    ∃ (e₀ : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
      (b : Basis 3) (beta delta : Fin 3)
      (e : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
      (P : Submodule (ZMod 2) NaturalSpace),
      ((beta = 0 ∧ delta = 2) ∨ (beta = 2 ∧ delta = 0)) ∧
      (Source.starImage H (one L T V₁ ⊔ T)).map e₀.toMonoidHom = fourParabolic b {beta, delta} ∧
      (Source.starImage H (zero L)).map e₀.toMonoidHom = fourNodeResidual b beta ∧
      (Source.starImage H (plus L T V₁)).map e₀.toMonoidHom = fourNodeResidual b delta ∧
      (Source.starImage H T).map e₀.toMonoidHom = cutStabilizer b Set.univ ∧
      (e = e₀ ∨ e = e₀.trans dualActor) ∧ Module.finrank (ZMod 2) P = 2 ∧
      (Source.starImage H (one L T V₁ ⊔ T)).map e.toMonoidHom = BinaryLinear.parabolic P ∧
      AllNaturalHeads ρ e := by
  have hTH := (Chapter1.isSylowIn_iff.mp hT).2.1
  have ht := (Chapter1.isSylowIn_iff.mp hT).1
  obtain ⟨S, hS⟩ := hT
  have hS' : (S : Subgroup H) = T.subgroupOf H := by
    rw [← hS, Subgroup.subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
  obtain ⟨hs, b, beta, delta, _, _, hbase, hzero, hplus, hflag, _, _, _, _, hend, hdim⟩ :=
    CoverSource.four_source_markings H K M L T V V₁ V₃ d hKH hTH hLK hLM hTM
      hK hKn hKT hcover hfactor S hS' hrel hNM eK
  let e₀ := CoverSource.wholeLinearModel H K T hKH hTH hK hKT hs eK
  have hPH : one L T V₁ ⊔ T ≤ H := sup_le (hLK.trans hKH) hTH
  have hN : one L T V₁ ⊔ T ≤ normalizer (V₃ : Set G) := by
    apply sup_le _ d.seed_stable
    rw [hfactor]
    exact sup_le d.plus_normalizes_seed
      ((d.zero_centralizes.trans (centralizer_le d.seed_le)).trans (Subgroup.centralizer_le_normalizer _))
  have hline : V₁ < V₃ := lt_of_le_of_ne d.line_le_seed (by
    intro he
    rw [he, relIndex_self] at hindex
    contradiction)
  let s := sourceSeedOfEarlier H V₃ V₁ ρ hρ (one L T V₁ ⊔ T) T hPH le_sup_right ht hN
    hline (fun X hx hy hn => hirr X hx hy (le_sup_left.trans hn)) hindex
  have hP : s.parabolic.map e₀.toMonoidHom = BinaryLinear.parabolic (cutSpace b 1) :=
    hbase.trans (endNodes_parabolic b beta delta hend)
  have hRH : zero L ≤ H := (by rw [hfactor]; exact le_sup_right : zero L ≤ one L T V₁).trans
    (hLK.trans hKH)
  obtain ⟨e, P, he, hd, hmark, hheads⟩ :=
    exists_marked_allNaturalHeads_of_plane_obstruction ρ s e₀ (cutSpace b 1) hdim hP
      (Source.starImage H (zero L))
      (sourceSeed_fixed_of_commutator_le H V₃ V₁ (zero L) ρ hρ d.zero_seed_commutator)
      (starImage_not_two_of_cubic_quotient H (zero L) hRH d.zero_core_card)
      (maximal_quotient_alternatives ρ s e₀ (hB4 e₀) (Source.starImage H Uγ) hA hquad hbound)
      (ExteriorGeometry.no_invariant_plane (cutSpace b 1) hdim)
  exact ⟨e₀, b, beta, delta, e, P, hend, hbase, hzero, hplus, hflag, he, hd, hmark, hheads⟩


end SourceAssembly

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment
