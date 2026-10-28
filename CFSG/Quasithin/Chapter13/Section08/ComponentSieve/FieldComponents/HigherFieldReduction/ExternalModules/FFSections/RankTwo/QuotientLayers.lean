module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.CubicFF
/-!
# Lifting the second rank-two tensor layer

The ratio-two section inequality gives all three F.9.18(6b,c) possibilities.
The normal cubic subgroup makes each noncentral section faithful; the paired
PSL₃ bound excludes both strong-FF cases. Cubic FF recognition identifies the
full moved submodule of the remaining quotient, with zero central bottom.

Its inverse image is exactly the original moved module. The quotient map,
first isomorphism theorem and restriction to the inverter-fixed spaces give
actual equivariant coordinates on this literal second layer, under the same
component marking. No splitting of the two-layer extension is asserted.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, F.9.18(6),
printed pp.325–326, and proof of 13.8.20(a), printed pp.954–955.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory InvertedCubicTensor
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.QuotientLayers
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (W : Subrepresentation ρ)

/-- The inverse image of an invariant quotient submodule in the original module. -/
def upper (N : Subrepresentation W.quotientRepresentation) : Subrepresentation ρ where
  toSubmodule := N.toSubmodule.comap W.toSubmodule.mkQ
  apply_mem_toSubmodule g _v hv := N.apply_mem_toSubmodule g hv

/-- This inverse image contains the original denominator. -/
theorem le_upper (N : Subrepresentation W.quotientRepresentation) : W ≤ upper ρ W N := by
  intro v hv
  change W.toSubmodule.mkQ v ∈ N.toSubmodule
  have hz : W.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hv
  rw [hz]
  exact N.toSubmodule.zero_mem

private def upperMap (N : Subrepresentation W.quotientRepresentation) :
    (upper ρ W N).toSubmodule →ₗ[ZMod 2] N.toSubmodule :=
  (W.toSubmodule.mkQ.comp (upper ρ W N).toSubmodule.subtype).codRestrict _ (fun v => v.property)

private theorem upperMap_surjective (N : Subrepresentation W.quotientRepresentation) :
    Function.Surjective (upperMap ρ W N) := by
  intro v
  obtain ⟨w, hw⟩ := W.toSubmodule.mkQ_surjective v
  exact ⟨⟨w, by change W.toSubmodule.mkQ w ∈ N.toSubmodule; rw [hw]; exact v.property⟩,
    Subtype.ext hw⟩

private theorem upperMap_ker (N : Subrepresentation W.quotientRepresentation) :
    W.toSubmodule.comap (upper ρ W N).toSubmodule.subtype = (upperMap ρ W N).ker := by
  ext v
  change (v : V) ∈ W.toSubmodule ↔ upperMap ρ W N v = 0
  rw [Subtype.ext_iff]
  exact (Submodule.Quotient.mk_eq_zero _).symm

/-- The actual quotient map identifies the lifted section with the quotient submodule. -/
def sectionEquiv (N : Subrepresentation W.quotientRepresentation) :
    SectionSpace ρ W (upper ρ W N) ≃ₗ[ZMod 2] N.toSubmodule :=
  (Submodule.quotEquivOfEq _ _ (upperMap_ker ρ W N)).trans
    ((upperMap ρ W N).quotKerEquivOfSurjective (upperMap_surjective ρ W N))

/-- The first-isomorphism coordinates respect the whole original group action. -/
theorem sectionEquiv_equivariant (N : Subrepresentation W.quotientRepresentation)
    (g : G) (v : SectionSpace ρ W (upper ρ W N)) :
    sectionEquiv ρ W N (sectionRepresentation ρ W (upper ρ W N) g v) =
      N.toRepresentation g (sectionEquiv ρ W N v) := by
  induction v using Submodule.Quotient.induction_on with | _ v => rfl

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  (τ : Representation (ZMod 2) G U)

private def multiplicityEquiv (s : S₃ →* G) (a : V ≃ₗ[ZMod 2] U)
    (ha : ∀ g v, a (ρ g v) = τ g (a v)) :
    multiplicitySpace (ρ.comp s) ≃ₗ[ZMod 2] multiplicitySpace (τ.comp s) where
  toFun v := ⟨a v, by
    rw [mem_multiplicitySpace]
    change τ (s inverter) (a v) = a v
    rw [← ha]
    exact congrArg a ((mem_multiplicitySpace (ρ.comp s) v).mp v.property)⟩
  invFun v := ⟨a.symm v, by
    rw [mem_multiplicitySpace]
    apply a.injective
    change a (ρ (s inverter) (a.symm v)) = a (a.symm v)
    rw [ha, a.apply_symm_apply]
    exact (mem_multiplicitySpace (τ.comp s) v).mp v.property⟩
  left_inv v := Subtype.ext (a.symm_apply_apply v)
  right_inv v := Subtype.ext (a.apply_symm_apply v)
  map_add' v w := Subtype.ext (a.map_add v w)
  map_smul' c v := Subtype.ext (a.map_smul c v)

variable {K : Type*} [Group K]
private theorem multiplicityEquiv_equivariant (f : K →* G) (s : S₃ →* G)
    (hs : ∀ k g, Commute (f k) (s g)) (a : V ≃ₗ[ZMod 2] U)
    (ha : ∀ g v, a (ρ g v) = τ g (a v)) (k : K)
    (v : multiplicitySpace (ρ.comp s)) :
    multiplicityEquiv ρ τ s a ha
      (multiplicity (ρ.comp s) (ρ.comp f) (ambient_commute ρ f s hs) k v) =
    multiplicity (τ.comp s) (τ.comp f) (ambient_commute τ f s hs) k
      (multiplicityEquiv ρ τ s a ha v) :=
  by
    apply Subtype.ext
    change a (ρ (f k) v) = τ (f k) (a v)
    exact ha (f k) v

variable (N : Subrepresentation W.quotientRepresentation)
private def bottomEquiv : N.toSubmodule ≃ₗ[ZMod 2] SectionSpace W.quotientRepresentation ⊥ N :=
  LinearEquiv.ofBijective (sectionLower W.quotientRepresentation ⊥ N).toSubmodule.mkQ ⟨by
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero (sectionLower W.quotientRepresentation ⊥ N).toSubmodule).mp hv,
    Submodule.mkQ_surjective _⟩

/-- Compare the original section with the literal zero-bottom quotient section. -/
def liftedSectionEquiv : SectionSpace ρ W (upper ρ W N) ≃ₗ[ZMod 2]
    SectionSpace W.quotientRepresentation ⊥ N :=
  (sectionEquiv ρ W N).trans (bottomEquiv ρ W N)

/-- The comparison intertwines every original actor, including the marked inverter. -/
theorem liftedSectionEquiv_equivariant (g : G) (v : SectionSpace ρ W (upper ρ W N)) :
    liftedSectionEquiv ρ W N (sectionRepresentation ρ W (upper ρ W N) g v) =
      sectionRepresentation W.quotientRepresentation ⊥ N g (liftedSectionEquiv ρ W N v) := by
  change bottomEquiv ρ W N (sectionEquiv ρ W N (_)) = _
  rw [sectionEquiv_equivariant]
  rfl

/-- Restriction of the actual section comparison to the inverter-fixed spaces. -/
def liftedMultiplicityEquiv (s : S₃ →* G) :
    SectionMultiplicity ρ s W (upper ρ W N) ≃ₗ[ZMod 2]
      SectionMultiplicity W.quotientRepresentation s ⊥ N :=
  multiplicityEquiv _ _ s (liftedSectionEquiv ρ W N) (liftedSectionEquiv_equivariant ρ W N)

/-- The multiplicity comparison preserves the specified component embedding. -/
theorem liftedMultiplicityEquiv_equivariant (f : K →* G) (s : S₃ →* G)
    (hs : ∀ k g, Commute (f k) (s g)) (k : K)
    (v : SectionMultiplicity ρ s W (upper ρ W N)) :
    liftedMultiplicityEquiv ρ W N s (sectionMultiplicityAction ρ f s hs W (upper ρ W N) k v) =
      sectionMultiplicityAction W.quotientRepresentation f s hs ⊥ N k
        (liftedMultiplicityEquiv ρ W N s v) :=
  multiplicityEquiv_equivariant _ _ f s hs _ _ k v

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.QuotientLayers

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.QuotientLayers
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions
open LinearTwo.NoStrongMoved

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal]

/-- The invariant full moved submodule for a normal component. -/
def moved : Subrepresentation ρ where
  toSubmodule := subspaceCommutator ρ ⊤ K
  apply_mem_toSubmodule g _v hv :=
    ((subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by simp))
      (show (⊤ : Subgroup D) ≤ normalizer K by rw [normalizer_eq_top])) (mem_top g) _).mpr hv

/-- The moved subrepresentation has the literal component commutator as its
underlying space. This specification does not expose its invariant-action proof. -/
theorem moved_toSubmodule : (moved ρ K).toSubmodule = subspaceCommutator ρ ⊤ K := by rfl

/-- A fully moved denominator makes the lifted moved quotient exactly [V,K]. -/
theorem upper_moved (W : Subrepresentation ρ)
    (hW : subspaceCommutator ρ W.toSubmodule K = W.toSubmodule) :
    (upper ρ W (moved W.quotientRepresentation K)).toSubmodule = subspaceCommutator ρ ⊤ K := by
  have hm := subspaceCommutator_map_embedding W.quotientRepresentation ρ
    (MonoidHom.id D) W.toSubmodule.mkQ (fun _ _ => rfl) K ⊤
  have hm' : subspaceCommutator W.quotientRepresentation ⊤ K =
      (subspaceCommutator ρ ⊤ K).map W.toSubmodule.mkQ := by
    simpa only [Submodule.map_top, LinearMap.range_eq_top.mpr W.toSubmodule.mkQ_surjective,
      Subgroup.map_id] using hm
  change (subspaceCommutator W.quotientRepresentation ⊤ K).comap W.toSubmodule.mkQ = _
  rw [hm', Submodule.comap_map_eq, Submodule.ker_mkQ]
  apply sup_eq_left.mpr
  rw [← hW]
  exact subspaceCommutator_mono_left ρ le_top K

universe u v
variable {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (K X : Subgroup D)
    [K.Normal] [X.Normal] [IsQuasisimple K]
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦) (hInv : FullIrrInvariance.{u,v})
    (hS : IsSQTK 𝒦 D) (hx : Nat.card X = 3)
    (hc : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (s : S₃ →* D) (hs : ∀ (k : K) g, Commute (k : D) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = X)
    (hg : subspaceCommutator ρ ⊤ X = ⊤)
    {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F]
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n) (e : K ≃* PSL(3,F))

include hB42 hInv hS hx hc hs hmark hg hn ho hF e in
/-- Every proper nonzero fully moved submodule has a natural second layer up to
the full moved module. Faithfulness and exclusion of both strong-FF branches
are proved from the cubic structure and the original ratio-two actor. -/
theorem second_layer (W : Subrepresentation ρ)
    (hW : W.toSubmodule ≠ ⊥)
    (hfull : subspaceCommutator ρ W.toSubmodule K = W.toSubmodule)
    (hne : W.toSubmodule ≠ subspaceCommutator ρ ⊤ K)
    (A : Subgroup D) (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    ∃ M : Subrepresentation ρ, W ≤ M ∧
      M.toSubmodule = subspaceCommutator ρ ⊤ K ∧
      IsProjectiveNaturalOrDual ho hF
        ((sectionMultiplicityAction ρ K.subtype s hs W M).comp e.symm.toMonoidHom) := by
  have hxmem : s cubic ∈ X := by
    rw [← hmark]
    exact mem_map_of_mem s (show cubic ∈ alternatingGroup (Fin 3) from by
      change Equiv.Perm.sign cubic = 1
      decide +kernel)
  have hfree := ambient_fixedFree_of_commutator ρ s (by rw [hmark]; exact hg)
  have hwfree := fixedFree_of_injective (ρ.comp s) (W.toRepresentation.comp s)
    W.toSubmodule.subtype W.toSubmodule.subtype_injective (fun _ => rfl) hfree
  have hwfull := full_of_fixedFree X W.toRepresentation (s cubic) hxmem hwfree
  have hfW := faithful_of_cubic K X hx hc W.toRepresentation
    (subrepresentation_action_nontrivial ρ W K hW hfull) (s cubic) hxmem hwfree
  have hqfree := fixedFree_of_surjective (ρ.comp s) (W.quotientRepresentation.comp s)
    W.toSubmodule.mkQ W.toSubmodule.mkQ_surjective (fun _ => rfl) hfree
  let : Finite (V ⧸ W.toSubmodule) := Finite.of_surjective _ W.toSubmodule.mkQ_surjective
  have hqfull := full_of_fixedFree X W.quotientRepresentation (s cubic) hxmem hqfree
  have hfQ := faithful_of_cubic K X hx hc W.quotientRepresentation
    (quotient_action_nontrivial ρ W K hfull hne) (s cubic) hxmem hqfree
  have hqff : IsFFModule W.quotientRepresentation := by
    rcases ff_alternative_of_codim_bound ρ W hA hbound with hff | hwstrong | hqstrong
    · exact hff.2
    · exact (CubicFF.no_strong W.toRepresentation K hB42 hInv hS hfW X hx hc
        s hs hmark hwfull hn ho hF e hwstrong).elim
    · exact (CubicFF.no_strong W.quotientRepresentation K hB42 hInv hS hfQ X hx hc
        s hs hmark hqfull hn ho hF e hqstrong).elim
  let N := moved W.quotientRepresentation K
  have hnat := CubicFF.moved_natural_of_ff W.quotientRepresentation K hB42 hInv hS hfQ
    X hx hc s hs hmark hqfull hn ho hF e hqff N rfl
  refine ⟨upper ρ W N, le_upper ρ W N, upper_moved ρ K W hfull, ?_⟩
  let a := liftedMultiplicityEquiv ρ W N s
  have ha := liftedMultiplicityEquiv_equivariant ρ W N K.subtype s hs
  rcases hnat with ⟨b, hb⟩ | ⟨b, hb⟩
  · exact Or.inl ⟨a.trans b, fun g v => by
      change b (a (sectionMultiplicityAction ρ K.subtype s hs W (upper ρ W N) (e.symm g) v)) = _
      rw [ha]
      exact hb g (a v)⟩
  · exact Or.inr ⟨a.trans b, fun g v => by
      change b (a (sectionMultiplicityAction ρ K.subtype s hs W (upper ρ W N) (e.symm g) v)) = _
      rw [ha]
      exact hb g (a v)⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.QuotientLayers
