module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.Multiplicity
public import Theory.Representation.HigherFieldBorelFixedSpaces
public import Theory.Representation.BinaryOffender.Homogeneous.FixedSpaceOrbit
public import Theory.Representation.NormalComponentConstituents
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideModule.Multiplicity
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.NativeRecognition

/-!
# The original outside PSL₂ quotient has an A₅ constituent

The marked commuting S₃ action gives a faithful FF action on its inverter-fixed
multiplicity space. Native B.4.2 recognition on an actual central section leaves
a natural SL₂ constituent or the five-letter A₅ constituent. Ambient
irreducibility eliminates component-fixed vectors, so the central quotient
coordinates identify the actual constituent in the original module.

The two-residual of the original Sylow normalizer has no fixed vector on the
natural constituent or any ambient conjugate. Their orbit spans the whole
irreducible module. Its nonzero fixed seed therefore forces field degree two
and the A₅ constituent. This constituent lies in the inverter-fixed multiplicity
space; the cubic pair coordinates give ambient dimension at least eight.

Source: Aschbacher–Smith, 14.7.42, printed pp.1061–1062, using B.4.2 and
F.9.18, printed pp.86 and 325–326, refs/quasithin.pdf.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.BinaryOffender.Homogeneous Representation.HigherFieldBorelFixedSpaces
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoModule
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The literal Sylow-normalizer residual has no fixed vector on a natural
binary SL₂ module, under any compatible component marking. -/
theorem natural_borel_fixedSpace
    (K : Subgroup D) (σ : Representation (ZMod 2) K V)
    (F : BinaryField) (hn : 1 < F.degree)
    (e : ActionEquiv σ (linearNatural F 2)) (S : Sylow 2 K) :
    fixedSpace σ (twoResidualImage (normalizer (S : Set K))) = ⊥ := by
  let ν := linearNatural F 2
  obtain ⟨g,hg⟩ := LinearTwo.align_borel K e.groupEquiv S
  let a := e.groupEquiv.trans (MulAut.conj g)
  have hmap : (twoResidualImage (normalizer (S : Set K))).map a.toMonoidHom =
      twoResidualImage (Matrix.SpecialLinearGroup.rankOneBorel F.Carrier) := by
    rw [twoResidualImage,map_embedded_pResidual,hg]
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have hz : ν g (e.linearEquiv v) ∈ fixedSpace ν
      (twoResidualImage (Matrix.SpecialLinearGroup.rankOneBorel F.Carrier)) := by
    intro b
    have hb : b.val ∈ (twoResidualImage (normalizer (S : Set K))).map a.toMonoidHom :=
      hmap.symm ▸ b.property
    obtain ⟨x,hx,hxb⟩ := hb
    change ν b.val (ν g (e.linearEquiv v)) = ν g (e.linearEquiv v)
    rw [←hxb]
    change ν (g * e.groupEquiv x * g⁻¹) (ν g (e.linearEquiv v)) = _
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
    rw [map_mul,Module.End.mul_apply,←e.intertwines]
    have hvx : σ x v = v := hv ⟨x,hx⟩
    rw [hvx]
  have hzero : ν g (e.linearEquiv v) = 0 := by
    have h : fixedSpace ν
        (twoResidualImage (Matrix.SpecialLinearGroup.rankOneBorel F.Carrier)) = ⊥ :=
      (sl2_twoResidual_natural_fixedSpaces hn F.card_eq).1
    rwa [h,Submodule.mem_bot] at hz
  apply e.linearEquiv.injective
  rw [map_zero]
  have hh := congrArg (ν g⁻¹) hzero
  simpa only [map_zero,←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,
    Module.End.one_apply] using hh

/-- Every ambient conjugate of the natural constituent, and hence their
whole orbit span, has zero fixed space for the same original Borel residual. -/
theorem natural_orbit_fixedSpace
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal]
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (F : BinaryField) (hn : 1 < F.degree)
    (e : ActionEquiv (invariantSubspace ρ K I hI.choose).toRepresentation
      (linearNatural F 2)) (S : Sylow 2 K) :
    orbitSpan ρ ⊤ I ⊓ fixedSpace (ρ.comp K.subtype)
      (twoResidualImage (normalizer (S : Set K))) = ⊥ := by
  let B := twoResidualImage (normalizer (S : Set K))
  rw [fixedSpace_comp_map]
  apply orbitSpan_inf_fixedSpace_eq_bot ρ K (B.map K.subtype) (map_subtype_le _) I hI
  intro g
  rw [←fixedSpace_comp_map]
  let σ := (invariantSubspace ρ K I hI.choose).toRepresentation
  let a : MulAut K := MulAut.conjNormal g⁻¹
  let e' : ActionEquiv (σ.comp a.toMonoidHom) (linearNatural F 2) := {
    groupEquiv := a.trans e.groupEquiv
    linearEquiv := e.linearEquiv
    intertwines := fun k v => e.intertwines (a k) v }
  have hzero := natural_borel_fixedSpace K (σ.comp a.toMonoidHom) F hn e' S
  apply (Submodule.eq_bot_iff _).mpr
  rintro v ⟨⟨w,hw,rfl⟩,hv⟩
  have hwfix : (⟨w,hw⟩ : I) ∈ fixedSpace (σ.comp a.toMonoidHom) B := by
    intro b
    apply Subtype.ext
    change ρ (g⁻¹ * (b.val : D) * (g⁻¹)⁻¹) w = w
    rw [inv_inv]
    have h := congrArg (ρ g⁻¹) (hv b)
    change ρ g⁻¹ (ρ (b.val : D) (ρ g w)) = ρ g⁻¹ (ρ g w) at h
    simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,
      Module.End.one_apply,mul_assoc] using h
  have hh : (⟨w,hw⟩ : I) = 0 := by
    change (⟨w,hw⟩ : I) ∈ fixedSpace (σ.comp a.toMonoidHom)
      (twoResidualImage (normalizer (S : Set K))) at hwfix
    rwa [hzero,Submodule.mem_bot] at hwfix
  rw [show w = 0 from congrArg Subtype.val hh,map_zero]

/-- Ambient irreducibility and a nonzero Borel-fixed seed exclude the
actual natural constituent. -/
theorem natural_fixed_seed_false
    (ρ : Representation (ZMod 2) D V) (hi : IsIrreducible ρ)
    (K : Subgroup D) [K.Normal]
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (F : BinaryField) (hn : 1 < F.degree)
    (e : ActionEquiv (invariantSubspace ρ K I hI.choose).toRepresentation
      (linearNatural F 2)) (S : Sylow 2 K)
    (v : V) (hv : v ≠ 0)
    (hfix : ∀ b : twoResidualImage (normalizer (S : Set K)), ρ b.val.val v = v) :
    False := by
  let W : Subrepresentation ρ :=
    ⟨orbitSpan ρ ⊤ I,fun g v hv => (orbitSpan_invariant ρ ⊤ I (mem_top g) v).2 hv⟩
  have hW : W ≠ ⊥ := by
    intro he
    exact orbitSpan_ne_bot ρ hI (congrArg Subrepresentation.toSubmodule he)
  have ht : W = ⊤ := (hi.eq_bot_or_eq_top W).resolve_left hW
  have hWt : orbitSpan ρ ⊤ I = ⊤ := congrArg Subrepresentation.toSubmodule ht
  have hz := natural_orbit_fixedSpace ρ K I hI F hn e S
  rw [hWt,top_inf_eq] at hz
  have hh : v ∈ fixedSpace (ρ.comp K.subtype)
      (twoResidualImage (normalizer (S : Set K))) := hfix
  exact hv (by simpa only [hz,Submodule.mem_bot] using hh)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoModule


set_option backward.isDefEq.respectTransparency true
public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory InvertedCubicTensor
open Representation.BinaryOffender.Homogeneous Representation.HigherFieldBorelFixedSpaces
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoModule
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u
variable {D V : Type u} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]


private theorem realized_constituent_cases
    {G W E N : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    [Group E] [Finite E] [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) G W) (K : Subgroup G)
    (σ : Representation (ZMod 2) E N) (L J : Subgroup E)
    (r : LinearTwo.FiveReconstruction.ConstituentRealization ρ K σ L)
    (hfix : fixedSpace ρ K = ⊥) {n : ℕ}
    (hc : LinearTwo.ConstituentCase σ L J n) :
    (∃ F : BinaryField, F.degree = n ∧
      Nonempty (ActionEquiv (invariantSubspace ρ K r.space r.irrPlus.choose).toRepresentation
        (linearNatural F 2))) ∨
    (n = 2 ∧ Nonempty (ActionEquiv
      (invariantSubspace ρ K r.space r.irrPlus.choose).toRepresentation
      (BinaryPermutation.alternatingCoreRepresentation (Fin 5)))) := by
  let q := centralSectionEquiv ρ K r.space (by rw [hfix]; exact disjoint_bot_right)
  let a := q.trans r.linearEquiv
  let κ := (invariantSubspace ρ K r.space r.irrPlus.choose).toRepresentation
  have ha : ∀ k v, a (κ k v) = σ (r.component k) (a v) := by
    intro k v
    exact r.component_intertwines k (q v)
  cases hc with
  | natural F' hdeg _ enat =>
    left
    refine ⟨F',hdeg,⟨{
      groupEquiv := r.component.trans enat.groupEquiv
      linearEquiv := a.trans enat.linearEquiv
      intertwines := ?_ }⟩⟩
    intro k v
    change enat.linearEquiv (a (κ k v)) = _
    rw [ha]
    exact enat.intertwines (r.component k) (a v)
  | five hdeg efive =>
    right
    refine ⟨hdeg,⟨{
      groupEquiv := LinearTwo.FiveReconstruction.componentEquiv σ _ _ efive r.component
      linearEquiv := LinearTwo.FiveReconstruction.coreCoordinates σ _ _ efive a
      intertwines := ?_ }⟩⟩
    exact LinearTwo.FiveReconstruction.coreCoordinates_equivariant σ _ _ efive κ
      r.component a ha

/-- Native recognition constructs a natural or five-letter constituent in
the literal inverter-fixed multiplicity space of the original module. -/
theorem constituent_cases
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (hi : IsIrreducible ρ)
    (K X : Subgroup D) [K.Normal] [X.Normal] [IsQuasisimple K]
    (hS : IsSQTK KnownSimple.IsKnownSimple D) (hx : Nat.card X = 3)
    (hcommon : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (s : S₃ →* D) (hs : ∀ (k : K) g, Commute (k : D) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = X)
    (hg : subspaceCommutator ρ ⊤ X = ⊤)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hquad : IsQuadratic ρ A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : K ≃* PSL(2,F)) :
    ∃ (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I),
      I ≤ multiplicitySpace (ρ.comp s) ∧
      ((∃ E : BinaryField, E.degree = n ∧
        Nonempty (ActionEquiv (invariantSubspace ρ K I hI.choose).toRepresentation
          (linearNatural E 2))) ∨
      (n = 2 ∧ Nonempty (ActionEquiv
        (invariantSubspace ρ K I hI.choose).toRepresentation
        (BinaryPermutation.alternatingCoreRepresentation (Fin 5))))) := by
  obtain ⟨hsE,hfaith,hoff,hfit⟩ := OutsideModule.faithful_ff_multiplicity
    ρ hf K X hx hcommon s hs hmark hg A hA hquad hbound
  let E := K ⊔ A
  let K₀ := K.subgroupOf E
  let j := (multiplicitySpace (ρ.comp s)).subtype
  let μ := multiplicity (ρ.comp s) (ρ.comp E.subtype)
    (ambient_commute ρ E.subtype s hsE)
  let b : K₀ ≃* K := subgroupOfEquivOfLe le_sup_left
  let : IsQuasisimple K₀ := IsQuasisimple.of_mulEquiv b.symm
  have hfit₀ : generalizedFitting E = K₀ := hfit
  let : K₀.Normal := hfit₀ ▸ generalizedFitting_normal
  have hKm : K₀.map E.subtype = K := map_subgroupOf_eq_of_le le_sup_left
  have hz : center K₀ = ⊥ := LinearTwo.NoStrongMoved.psl_center_bot K₀ (b.trans e)
  obtain ⟨B,I,_,hI,hJI,hB4,hFF,hfit',_⟩ :=
    faithful_irreducible_ff_section μ hfaith K₀ hfit₀ hz (hS.subgroup E)
      ⟨A.subgroupOf E,hoff⟩
  let r := LinearTwo.centralImageRealization μ K₀ (K₀ ⊔ B) hz le_sup_left I hI hJI hfit'
  let : Finite (centralQuotient μ K₀ I) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective ((fixedSpace μ K₀).comap I.subtype))
  obtain ⟨r',hr'⟩ := r.exists_mapEmbedding μ ρ E.subtype E.subtype_injective
    j (multiplicitySpace _).subtype_injective (fun _ _ => rfl) K hKm
  let τ := centralSectionRepresentation μ K₀ (K₀ ⊔ B) I hJI le_normalizer_of_normal
  let σ := imageRepresentation τ
  have hmodel : ClassicalGroup.IsPSL (generalizedFitting (actionImage τ)) 2 (2^n) :=
    ⟨F,inferInstance,inferInstance,hF,⟨r'.component.symm.trans e⟩⟩
  have hKne : K ≠ ⊥ := by
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    exact (nontrivial_iff_ne_bot K).mp inferInstance
  have hfix : fixedSpace ρ K = ⊥ :=
    fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi K hKne
  have hplace : r'.space ≤ multiplicitySpace (ρ.comp s) := by
    rw [hr']
    exact (Submodule.map_mono le_top).trans (by rw [Submodule.map_top]; exact le_of_eq (Submodule.range_subtype _))
  exact ⟨r'.space,r'.irrPlus,hplace,realized_constituent_cases ρ K σ _ _ r' hfix
    (NativeRecognition.linearTwo_constituent σ hB4 hFF hn hmodel)⟩

/-- The original nonzero Borel-fixed vector selects field four and an actual
A₅ five-letter constituent inside the inverter-fixed multiplicity space. -/
theorem field_four_and_five_constituent
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (hi : IsIrreducible ρ)
    (K X : Subgroup D) [K.Normal] [X.Normal] [IsQuasisimple K]
    (hS : IsSQTK KnownSimple.IsKnownSimple D) (hx : Nat.card X = 3)
    (hcommon : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (s : S₃ →* D) (hs : ∀ (k : K) g, Commute (k : D) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = X)
    (hg : subspaceCommutator ρ ⊤ X = ⊤)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hquad : IsQuadratic ρ A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : K ≃* PSL(2,F)) (S : Sylow 2 K)
    (v : V) (hv : v ≠ 0)
    (hfix : ∀ b : twoResidualImage (normalizer (S : Set K)), ρ b.val.val v = v) :
    n = 2 ∧ ∃ (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I),
      I ≤ multiplicitySpace (ρ.comp s) ∧ Nonempty (ActionEquiv (invariantSubspace ρ K I hI.choose).toRepresentation
        (BinaryPermutation.alternatingCoreRepresentation (Fin 5))) := by
  obtain ⟨I,hI,hplace,hcase⟩ := constituent_cases ρ hf hi K X hS hx hcommon s hs hmark hg
    A hA hquad hbound hn hF e
  rcases hcase with ⟨E,hdeg,⟨enat⟩⟩ | ⟨hdeg,efive⟩
  · exact (natural_fixed_seed_false ρ hi K I hI E (by omega) enat S v hv hfix).elim
  · exact ⟨hdeg,I,hI,hplace,efive⟩

/-- Field four and dimension at least eight follow from the original actor
and Borel-fixed seed, without assuming component irreducibility. -/
theorem field_four_and_dimension_ge_eight
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (hi : IsIrreducible ρ)
    (K X : Subgroup D) [K.Normal] [X.Normal] [IsQuasisimple K]
    (hS : IsSQTK KnownSimple.IsKnownSimple D) (hx : Nat.card X = 3)
    (hcommon : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (s : S₃ →* D) (hs : ∀ (k : K) g, Commute (k : D) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = X)
    (hg : subspaceCommutator ρ ⊤ X = ⊤)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hquad : IsQuadratic ρ A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : K ≃* PSL(2,F)) (S : Sylow 2 K)
    (v : V) (hv : v ≠ 0)
    (hfix : ∀ b : twoResidualImage (normalizer (S : Set K)), ρ b.val.val v = v) :
    n = 2 ∧ 8 ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨hdeg,I,hI,hplace,⟨efive⟩⟩ := field_four_and_five_constituent ρ hf hi K X
    hS hx hcommon s hs hmark hg A hA hquad hbound hn hF e S v hv hfix
  have hdim : Module.finrank (ZMod 2)
      (invariantSubspace ρ K I hI.choose).toSubmodule = 4 := by
    have hd := efive.linearEquiv.finrank_eq
    simpa only [BinaryPermutation.finrank_core,Fintype.card_fin] using hd
  have hle := Submodule.finrank_mono hplace
  have hfree := ambient_fixedFree_of_commutator ρ s (by rw [hmark]; exact hg)
  have hd := (pairEquiv (ρ.comp s) hfree).finrank_eq
  rw [Module.finrank_prod] at hd
  have hmult : 4 ≤ Module.finrank (ZMod 2) (multiplicitySpace (ρ.comp s)) :=
    hdim ▸ hle
  change Module.finrank (ZMod 2) (multiplicitySpace (ρ.comp s)) +
    Module.finrank (ZMod 2) (multiplicitySpace (ρ.comp s)) = Module.finrank (ZMod 2) V at hd
  exact ⟨hdeg,by omega⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoModule
