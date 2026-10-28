module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.Borel
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.ModelReduction

/-!
# Original external-cubic structure in the higher-field argument

The actual special groups with trivial scalar center are transported through
their canonical projective maps. In the external branch the original
involution centralizer supplies SQTK on H; the normal cubic image outside K*
forces three-rank one. The intrinsic model sieve gives the three surviving
carriers and centerlessness. The preceding Fitting alternatives and the
solvable local supplement then construct a marked S₃ centralizing K*.

The original Borel application proves B ≤ C_G(V) through the corrected
full-product calculation, and retains V₃=[V₃,X], the prescribed inverter
and the covered zero-direction fixation. It asserts neither W=U nor any
representation-classification premise. Excluding this external branch and
the exceptional outer branch remains with qt-d-138-fields-source; the
original source context is supplied by qt-d-1381-source.
Source: Aschbacher–Smith, 13.8.20(a), printed p.954 (1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LocalBorel LocalBorel.CentralizingCalculation
open ExternalModules
open Chapter1.Section02.LocalModels Components.Models
open BenderSuzuki.MatrixGroups.HermitianForm
universe u

/-- Normalize the special groups with trivial scalar center through the actual
canonical projective maps. All seven higher-field rows are retained. -/
theorem higher_field_carrier {A : Type u} [Group A]
    (h : HigherFieldAlternative A) : Structure.HigherFieldCarrier A := by
  obtain ⟨n,hn,h⟩ := h
  rcases h with h | ⟨unitary,h | h⟩ | h | h
  · exact .linearTwo n hn h
  · exact .projectiveThree unitary n hn h
  · have hp := Nat.BinaryTorusParity.two_pow_mod_three n
    cases unitary with
    | false =>
      rcases Nat.even_or_odd n with he | ho
      · exact .specialThree false n hn (by simpa [Nat.even_iff.mp he] using hp) h
      · obtain ⟨F,hF,hfin,hc,⟨e⟩⟩ := h
        exact .projectiveThree false n hn ⟨F,hF,hfin,hc,
          ⟨e.trans (Matrix.PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv hc ho)⟩⟩
    | true =>
      rcases Nat.even_or_odd n with he | ho
      · obtain ⟨F,hF,hfin,J,hc,hconj,⟨e⟩⟩ := h
        exact .projectiveThree true n hn ⟨F,hF,hfin,J,hc,hconj,
          ⟨e.trans (EvenProjectiveComparison.specialProjectiveEquiv J he hconj)⟩⟩
      · exact .specialThree true n hn (by simpa [Nat.odd_iff.mp ho] using hp) h
  · exact .symplectic n hn h
  · exact .g2 n hn h

private theorem higher_field_transport {A B : Type*} [Group A] [Group B]
    (h : HigherFieldAlternative A) (e : B ≃* A) : HigherFieldAlternative B := by
  obtain ⟨n,hn,h⟩ := h
  refine ⟨n,hn,?_⟩
  rcases h with h | ⟨unitary,h | h⟩ | h | h
  · exact Or.inl (h.of_mulEquiv e)
  · refine Or.inr (Or.inl ⟨unitary,Or.inl ?_⟩)
    cases unitary
    · exact ClassicalGroup.IsPSL.of_mulEquiv h e
    · exact ClassicalGroup.IsPSU.of_mulEquiv h e
  · refine Or.inr (Or.inl ⟨unitary,Or.inr ?_⟩)
    cases unitary
    · obtain ⟨F,hF,hfin,hc,⟨a⟩⟩ := h
      exact ⟨F,hF,hfin,hc,⟨e.trans a⟩⟩
    · obtain ⟨F,hF,hfin,J,hc,hconj,⟨a⟩⟩ := h
      exact ⟨F,hF,hfin,J,hc,hconj,⟨e.trans a⟩⟩
  · exact Or.inr (Or.inr (Or.inl (h.of_mulEquiv e)))
  · exact Or.inr (Or.inr (Or.inr (h.of_mulEquiv e)))

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The original involution-centralizer hypothesis gives SQTK on H itself. -/
theorem source_sqtk (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K) :
    IsSQTK KnownSimple.IsKnownSimple H := by
  obtain ⟨z,hz,_,_,_,hG⟩ := LocalFitting.line_involution c.localSetup
  have hHN : H ≤ centralizer ({z} : Set G) := c.component.local_overgroup.2.1.trans hG
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
    ((c.localSetup.counterexample.qtke.involution_centralizer_sqtk hz).subgroup
      (H.subgroupOf (centralizer ({z} : Set G))))

/-- Derived structural conclusions of the external branch, on the literal
star images. The symmetric-three embedding retains the marked cubic image. -/
@[expose] def ExternalSourceData (H K X : Subgroup G) : Prop :=
  Nat.card (Source.starImage H X) = 3 ∧
    ¬ Source.starImage H X ≤ Source.starImage H K ∧
    (Source.starImage H X).Normal ∧
    Structure.ExternalCarrier (Source.starImage H K) ∧
    center (Source.starImage H K) = ⊥ ∧
    3 ∣ Nat.card (Source.starImage H K) ∧
    primeRank 3 K = 1 ∧ primeRank 3 (Source.starImage H K) = 1 ∧
    ∃ s : Equiv.Perm (Fin 3) →* Source.Hstar H,
      Function.Injective s ∧
      s.range ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)) ∧
      (alternatingGroup (Fin 3)).map s = Source.starImage H X

private theorem external_source_data
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K))
    (X : Subgroup G) (hX : IsPPerfect 2 X)
    (hcard : Nat.card (X ⧸ pCore 2 X) = 3)
    (hs : Group.IsSolvable (one L T V₁ ⊔ (T : Subgroup G) : Subgroup G))
    (hfit : Components.Fitting.twoFittingResidual H = ⊥ ∨
      Components.Fitting.twoFittingResidual H = X)
    (ha : ExternalXAlternative H K X) : ExternalSourceData H K X := by
  let : (K.subgroupOf H).Normal := c.component.normal
  let : Group.IsSolvable (one L T V₁ ⊔ (T : Subgroup G) : Subgroup G) := hs
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  obtain ⟨hc,hnot,hn,hr⟩ := Structure.external_cubic_rank KnownSimple.IsKnownSimple
    H K X (source_sqtk c) hKH c.component.component hX hcard ha
  have hrstar : primeRank 3 (Source.starImage H K) ≤ 1 := by
    rw [← Structure.threeRank_eq_star H K hKH c.component.component.subnormal]
    exact hr
  have hm := higher_field_carrier (higher_field_transport hfield
    (Components.componentStarEquiv H K hKH c.component.component).symm)
  obtain ⟨he,hz,hdiv,hreq⟩ := hm.external_structure hrstar
  have hgen : H = K ⊔ (one L T V₁ ⊔ (T : Subgroup G)) := by
    simpa only [sup_assoc] using c.component.generated.symm
  refine ⟨hc,hnot,hn,he,hz,hdiv,?_,hreq,?_⟩
  · rw [Structure.threeRank_eq_star H K hKH c.component.component.subnormal]
    exact hreq
  · exact Structure.source_symmetric_embedding H K X (one L T V₁) (T : Subgroup G)
      hgen hcard ha hz hfit

/-- Full original group-theoretic reduction of 13.8.20. The external branch
has B centralizing V, its rank-one carrier and the marked S₃; the other
branch retains precisely the exceptional carrier and outer actor. -/
theorem source_borel_structure
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    letI : (Source.starImage H K).Normal :=
      c.component.normal.map _ (QuotientGroup.mk'_surjective _)
    ∃ (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 (T : Subgroup G) H),
      borel H K (T : Subgroup G) hKH hT ≤ M ∧
      ∃ (X : Subgroup G) (t : ((T : Subgroup G) ⊓ L : Subgroup G)),
        ((Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = one L T V₁) ∨
          (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
            X = plus L T V₁ ∧
            coreAction (zero L) ⟨t.val,L_normalizes_zero L t.property.2⟩ = 1)) ∧
        InvertsTwoCoreQuotient X t.val ∧ V₃ = ⁅V₃,X⁆ ∧
        ((SylowExternalXAlternative H K (T : Subgroup G) X ∧
            borel H K (T : Subgroup G) hKH hT ≤ centralizer (V : Set G) ∧
            ExternalSourceData H K X) ∨
          ExceptionalOuterAlternative.{u,0} H K
            (QuotientGroup.mk' (pCore 2 H)
              ⟨t.val,c.component.local_overgroup.1.2 (mem_sup_right t.property.1)⟩)) := by
  let : (K.subgroupOf H).Normal := c.component.normal
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  obtain ⟨n,hn,unitary,four,m⟩ := torus_model_of_higher_field hfield
  let i := sourceInput c hn (Placement.model_transport m
    (Components.componentStarEquiv H K hKH c.component.component).symm)
  have h12 := LocalFitting.intersection_residual c.localSetup
    c.component.local_overgroup c.earlier1339
  have hseed := (Section07.ModelExclusions.seed_commutator_point_residual
    (localNaturalSetup c.localSetup)).symm
  refine ⟨i.component_le,i.sylow_H,?_⟩
  rcases local_quotient_alternatives c.localSetup with ⟨e,he⟩ | ⟨e,he⟩
  · obtain ⟨a⟩ := LocalFitting.ordinary_natural c.localSetup e he
    let d := i.ordinarySourceContext a
    obtain ⟨hB,t,hinv,hb⟩ := i.sylowBorelAlternative_ordinary a
    refine ⟨hB,one L T V₁,t,Or.inl ⟨⟨e⟩,rfl⟩,hinv,hseed,?_⟩
    rcases hb with hx | ho
    · have hc := AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource.source_residual_quotient_card a (one L T V₁) rfl
      obtain ⟨hp,hs⟩ := Structure.MarkedBorel.ordinary_local_inputs L (T : Subgroup G) V₁
        T.isPGroup' c.localSetup.line_stable hc
      have hf := Structure.selected_fitting_alternative H L (one L T V₁) (plus L T V₁)
        (one L T V₁) (Or.inl ⟨⟨e⟩,rfl⟩)
        (SourceAssembly.fitting_alternative d hs i.universal h12)
      exact Or.inl ⟨hx,SourceAssembly.ordinary_borel_centralizes d a hx,
        external_source_data c hfield _ hp hc hs hf hx.1⟩
    · exact Or.inr ho
  · obtain ⟨a⟩ := local_covered_flag_model c.localSetup e he
    have hfactor := CoverFactorization.source_factorization a
    let d := i.coveredSourceContext a hfactor
    obtain ⟨hp,hc,hs,hseedX⟩ := Structure.MarkedBorel.covered_local_inputs
      L (T : Subgroup G) V V₁ V₃ a hfactor hseed
    obtain ⟨hB,t,hinv,hz,hb⟩ := i.sylowBorelAlternative_covered a hfactor
    refine ⟨hB,plus L T V₁,t,Or.inr ⟨⟨e⟩,rfl,hz⟩,hinv,hseedX,?_⟩
    rcases hb with hx | ho
    · have hf := Structure.selected_fitting_alternative H L (one L T V₁) (plus L T V₁)
        (plus L T V₁) (Or.inr ⟨SourceAssembly.tripleCover_of_hex_mark e,rfl⟩)
        (SourceAssembly.fitting_alternative d hs i.universal h12)
      exact Or.inl ⟨hx,
        Covered.ZeroPlacement.FullProduct.External.borel_centralizes_of_Tstar_inverter
          d a hfactor hx.1.2.2.2.1 hx.2,
        external_source_data c hfield _ hp hc hs hf hx.1⟩
    · exact Or.inr ho

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
