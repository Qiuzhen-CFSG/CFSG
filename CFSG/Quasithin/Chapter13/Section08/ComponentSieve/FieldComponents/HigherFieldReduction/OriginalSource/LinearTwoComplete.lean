module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.Multiplicity
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.Unitary
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.ExternalTerminals

/-!
# The original external PSL₂ exclusion

The source quadratic actor supplies a faithful FF multiplicity action. The
absence of strong PSL₂ offenders makes its selected Irr⁺ constituent the
whole component-moved multiplicity. Its actual inclusion into the original
module constructs the realized central-section action. Cubic pair coordinates
identify the constituent orbit with the component moved space, preserving
any component-central complement. The two summands are distinct.

The quotient and multiplicity maps therefore instantiate the proved native
natural-or-five recognition. Original Borel centralization excludes the
natural layer, and original critical geometry excludes the marked-five case.
No FullF918Four, constituent-realization or whole-space premise remains.
The actual source Borel application retains only odd-degree PSL₃ in its
external branch, with all local covers and exceptional outer markings intact.

The odd PSL₃, exceptional outer and binary branches, and the final field-source
assembly remain with qt-d-138-fields-source. The original preceding context
retains its producer qt-d-1381-source. Source: Aschbacher–Smith, 13.8.20(a),
printed pp.954–955, with B.1.5, B.1.11, B.4.2 and F.9.18.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory InvertedCubicTensor
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ExternalModules ExternalModules.FFSections
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Representation.BinaryOffender.Homogeneous
universe u w
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K X : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The original faithful FF multiplicity action constructs the actual
constituent and its cubic orbit, discharging the realization premise in the
external PSL₂ terminal contradiction. -/
theorem source_external_linearTwo_false
    [(Source.starImage H K).Normal]
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (ha : ExternalXAlternative H K X) (hx : ExternalSourceData H K X)
    (hseed : V₃ = ⁅V₃,X⁆)
    (hlocal : (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = one L T V₁) ∨
      (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧ X = plus L T V₁))
    (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 (T : Subgroup G) H)
    (hcentral : LocalBorel.borel H K (T : Subgroup G) hKH hT ≤ centralizer (V : Set G))
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2^n)) : False := by
  let Ks := Source.starImage H K
  let : Ks.Normal := c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple Ks :=
    (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339 c.component.local_overgroup K
      c.component.component).2
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨s,_,hmark,hfree,A,_,hs,μ,hμ,hf,hoff,hfit,hS⟩ :=
    source_external_ff_multiplicity c act X ha hx hseed
  subst μ
  let E := Ks ⊔ A
  let K₀ := Ks.subgroupOf E
  let j := (multiplicitySpace (act.representation.comp s)).subtype
  let μ := multiplicity (act.representation.comp s) (act.representation.comp E.subtype)
    (ambient_commute act.representation E.subtype s hs)
  let b : K₀ ≃* Ks := subgroupOfEquivOfLe le_sup_left
  let : IsQuasisimple K₀ := IsQuasisimple.of_mulEquiv b.symm
  have hfit₀ : generalizedFitting E = K₀ := hfit
  let : K₀.Normal := hfit₀ ▸ generalizedFitting_normal
  have hKm : K₀.map E.subtype = Ks := map_subgroupOf_eq_of_le le_sup_left
  obtain ⟨B,I,hJI,hB4,hFF,r,hr,hImoved⟩ :=
    LinearTwo.faithful_ff_moved_realization μ hf K₀ hfit₀ hS (b.trans e)
      ⟨A.subgroupOf E,hoff⟩
  let : Finite (centralQuotient μ K₀ I) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective ((fixedSpace μ K₀).comap I.subtype))
  obtain ⟨r',hr'⟩ := r.exists_mapEmbedding μ act.representation E.subtype E.subtype_injective
    j (multiplicitySpace _).subtype_injective (fun _ _ => rfl) Ks hKm
  have hspace : r'.space = I.map j := hr'.trans (congrArg (fun J => J.map j) hr)
  have hpair : subspaceCommutator act.representation ⊤ Ks =
      r'.space ⊔ r'.space.map (act.representation (s cubic)) := by
    have hp := moved_pair (act.representation.comp s) (act.representation.comp E.subtype)
      (ambient_commute act.representation E.subtype s hs) hfree K₀
    change subspaceCommutator (act.representation.comp E.subtype) ⊤ K₀ =
      (subspaceCommutator μ ⊤ K₀).map j ⊔
        ((subspaceCommutator μ ⊤ K₀).map j).map (act.representation (s cubic)) at hp
    have he : subspaceCommutator (act.representation.comp E.subtype) ⊤ K₀ =
        subspaceCommutator act.representation ⊤ Ks :=
      (subspaceCommutator_comp_map act.representation E.subtype ⊤ K₀).trans
        (congrArg (subspaceCommutator act.representation ⊤) hKm)
    have hi : (subspaceCommutator μ ⊤ K₀).map j = r'.space :=
      (congrArg (fun J => J.map j) hImoved.symm).trans hspace.symm
    exact he.symm.trans (hp.trans
      (congrArg₂ (· ⊔ ·) hi (congrArg (fun J => J.map (act.representation (s cubic))) hi)))
  have horbit := orbit_pair_of_moved act.representation Ks (s cubic) r'.space hpair
  have hne : r'.space ≠ r'.space.map (act.representation (s cubic)) := by
    have hd := multiplicity_subspace_disjoint (act.representation.comp s) hfree I
    change Disjoint (I.map j) ((I.map j).map (act.representation (s cubic))) at hd
    have hd' : Disjoint r'.space (r'.space.map (act.representation (s cubic))) :=
      (congrArg₂ Disjoint hspace
        (congrArg (fun J => J.map (act.representation (s cubic))) hspace)).mpr hd
    exact Disjoint.ne (r'.irrPlus.ne_bot act.representation) hd'
  have hc : ∀ (k : Ks) g, Commute (k : Source.Hstar H) (s g) :=
    fun k g => hs ⟨k,mem_sup_left k.property⟩ g
  have hgen : subspaceCommutator act.representation ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤ := by
    apply LinearTwo.NoStrongMoved.full_of_fixedFree _ act.representation (s cubic) _ hfree
    exact Subgroup.mem_map_of_mem s
      (show cubic ∈ alternatingGroup (Fin 3) from by change Equiv.Perm.sign cubic = 1; decide +kernel)
  obtain ⟨a,ha'⟩ := r'.exists_multiplicityCoordinates act.representation Ks s hc horbit hgen
  exact source_external_linearTwo_realization_false c act ha hx hseed hlocal hKH hT hcentral
    s hc hmark _ hB4 hFF r' (SourceOrbit.selectedOrbitUpper act.representation r'.space)
    hne horbit a ha' hn ⟨F,hF,hfin,hcard,⟨e⟩⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The actual original Borel reduction now leaves only odd-degree PSL₃
in its external branch. The full covers, specified inverter and exceptional
outer action are retained. No constituent-realization premise remains. -/
theorem source_borel_odd_linearThree_or_outer
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    letI : (Source.starImage H K).Normal :=
      c.component.normal.map _ (QuotientGroup.mk'_surjective _)
    ∃ (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 (T : Subgroup G) H),
      LocalBorel.borel H K (T : Subgroup G) hKH hT ≤ M ∧
      ∃ (X : Subgroup G) (t : ((T : Subgroup G) ⊓ L : Subgroup G)),
        ((Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = one L T V₁) ∨
          (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
            X = plus L T V₁ ∧ coreAction (zero L) ⟨t.val,L_normalizes_zero L t.property.2⟩ = 1)) ∧
        LocalBorel.CentralizingCalculation.InvertsTwoCoreQuotient X t.val ∧ V₃ = ⁅V₃,X⁆ ∧
        ((LocalBorel.SylowExternalXAlternative H K (T : Subgroup G) X ∧
          LocalBorel.borel H K (T : Subgroup G) hKH hT ≤ centralizer (V : Set G) ∧
          ExternalSourceData H K X ∧
          ∃ n : ℕ, 1 < n ∧ Odd n ∧
            ClassicalGroup.IsPSL (Source.starImage H K) 3 (2^n)) ∨
          ExceptionalOuterAlternative.{u,0} H K
            (QuotientGroup.mk' (pCore 2 H)
              ⟨t.val,c.component.local_overgroup.1.2 (mem_sup_right t.property.1)⟩)) := by
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨hKH,hT,hBM,X,t,hlocal,hinv,hseed,hcases⟩ := source_borel_structure c hfield
  refine ⟨hKH,hT,hBM,X,t,hlocal,hinv,hseed,?_⟩
  rcases hcases with ⟨ha,hcentral,hx⟩ | he
  · obtain ⟨n,hn,hm | ⟨ho,hm⟩⟩ := source_external_linear_carriers c act ha.1 hx hseed
    · exact (source_external_linearTwo_false c act ha.1 hx hseed
        (hlocal.imp id (fun h => ⟨h.1,h.2.1⟩)) hKH hT hcentral (by omega) hm).elim
    · exact Or.inl ⟨ha,hcentral,hx,n,hn,ho,hm⟩
  · exact Or.inr he
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
