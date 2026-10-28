module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.Setup
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.MaximalImages
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.SourceContracts

/-!
# The genuine Thompson action for the Fitting-center argument

Restrict U_v to G_v and its faithful star action to J(G_v)*. The images
of maximum elementary subgroups generate this actor and are best offenders,
by the checked maximum-order comparison. Thus B.5.3 applies to this precise
Thompson image, without identifying it with the full offender group of G_v*.
The cover is the inverse image under the literal star quotient map.

The optional classification adapter takes the complete universal B.5.6
implication, with the corrected projective-line convention in its referenced
B.4.2 clause. It does not assume or prove a factor decomposition independently
of that implication.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.2.5–7, p.76, B.5.3/6, pp.104–105, and the paragraph after 13.6.13, p.929.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FittingCenter
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
variable {G : Type u} [Group G]

/-- The internal module as a subgroup of its actual acting group G_v. -/
def internalModule (z v : G) : Subgroup (Gv v) := (Uv z v).subgroupOf (Gv v)

instance internalModule_normal (z v : G) : (internalModule z v).Normal :=
  normal_subgroupOf_of_le_normalizer (Gv_normalizes_Uv z v)

instance internalModule_elementary (z v : G) [IsElementaryAbelian 2 (Uv z v)] :
    IsElementaryAbelian 2 (internalModule z v) where
  toIsMulCommutative := Subgroup.subgroupOf_isMulCommutative (H := Uv z v) (K := Gv v)
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := Uv z v) _ x.property

/-- Both sides are the same relative centralizer, with the nested subtypes
made explicit. The seed containment gives U_v ≤ G_v. -/
theorem starMk_ker_internalModule (z v : G) (hz : z ∈ Gv v) :
    (starMk z v).ker = centralizer (internalModule z v : Set (Gv v)) := by
  rw [starMk_ker]
  ext x
  change (x : G) ∈ centralizer (Uv z v : Set G) ↔
    x ∈ centralizer (internalModule z v : Set (Gv v))
  constructor
  · intro hx
    apply mem_centralizer_iff.mpr
    intro y hy
    exact Subtype.ext (mem_centralizer_iff.mp hx y hy)
  · intro hx
    apply mem_centralizer_iff.mpr
    intro y hy
    exact congrArg (fun a : Gv v => (a : G))
      (mem_centralizer_iff.mp hx ⟨y, Uv_le_Gv z v hz hy⟩ hy)

/-- Faithful binary conjugation on the internal module. -/
noncomputable def internalRepresentation (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)] :
    Representation (ZMod 2) (Gstar z v) (Additive (internalModule z v)) :=
  NormalElementaryQuotient.representation (internalModule z v)
    (starMk z v) (starMk_surjective z v) (starMk_ker_internalModule z v hz)

/-- Restriction to the literal Thompson image. -/
noncomputable def thompsonRepresentation (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)] :
    Representation (ZMod 2) (JGstar z v) (Additive (internalModule z v)) :=
  (internalRepresentation z v hz).comp (JGstar z v).subtype

/-- The action retains the original ambient conjugation convention. -/
theorem internalRepresentation_mk_apply (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)] (g : Gv v)
    (w : Additive (internalModule z v)) :
    (((internalRepresentation z v hz (starMk z v g) w).toMul : Gv v) : G) =
      (g : G) * (w.toMul : Gv v) * (g : G)⁻¹ := by
  exact congrArg (fun x : Gv v => (x : G))
    (NormalElementaryQuotient.representation_apply (internalModule z v)
      (starMk z v) (starMk_surjective z v) (starMk_ker_internalModule z v hz) g w)

theorem thompsonRepresentation_faithful (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)] :
    Function.Injective (thompsonRepresentation z v hz) :=
  (NormalElementaryQuotient.representation_injective (internalModule z v)
    (starMk z v) (starMk_surjective z v) (starMk_ker_internalModule z v hz)).comp
      (JGstar z v).subtype_injective

theorem JGstar_eq_intrinsic_map (z v : G) :
    JGstar z v = (Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup (Gv v))).map
      (starMk z v) :=
  (starImage_intrinsic_thompson z v ⊤ (Gv v)
    (by rw [← MonoidHom.range_eq_map, range_subtype])).symm

variable [Finite G]

/-- Every B.5.3 generation hypothesis is proved inside J(G_v)* itself. -/
theorem thompsonRepresentation_generated (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)] :
    offenderSubgroup (thompsonRepresentation z v hz) = ⊤ := by
  apply map_injective (JGstar z v).subtype_injective
  apply le_antisymm (by simp)
  rw [← MonoidHom.range_eq_map, range_subtype]
  conv_lhs => rw [JGstar_eq_intrinsic_map]
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro A hA
  apply map_le_iff_le_comap.mp
  by_cases hn : A.map (starMk z v) = ⊥
  · rw [hn]; exact bot_le
  have ha := Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
    (internalModule z v) (starMk z v) (starMk_surjective z v)
    (starMk_ker_internalModule z v hz) ⊤ A le_top hA hn
  have hAJ : A.map (starMk z v) ≤ JGstar z v := by
    rw [JGstar_eq_intrinsic_map]
    exact map_mono (le_sSup hA)
  rw [← map_subgroupOf_eq_of_le hAJ]
  apply map_mono
  exact le_iSup_of_le ((A.map (starMk z v)).subgroupOf (JGstar z v))
    (le_iSup_of_le ⟨ha.subgroupOf _ hAJ, le_top⟩ le_rfl)

omit [Finite G] in
/-- Normality transfers the trivial two-core to the actual Thompson image. -/
theorem JGstar_twoCore (z v : G) (hcore : pCore 2 (Gstar z v) = ⊥) :
    pCore 2 (JGstar z v) = ⊥ := by
  let : (JGstar z v).Normal := JGstar_normal z v
  have hn : ((pCore 2 (JGstar z v)).map (JGstar z v).subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hl : (pCore 2 (JGstar z v)).map (JGstar z v).subtype ≤ pCore 2 (Gstar z v) :=
    le_sSup ⟨hn, pCore_isPGroup.map _⟩
  rw [hcore] at hl
  exact (map_eq_bot_iff_of_injective _ (JGstar z v).subtype_injective).mp (le_bot_iff.mp hl)

/-- The SQTK presentation uses the full inverse image under the star map. -/
noncomputable def thompsonCover (z v : G) {K : GroupClass.{u}}
    (hlocal : IsSQTK K (Gv v)) : SQTKQuotient K (JGstar z v) where
  Cover := (JGstar z v).comap (starMk z v)
  kernel := ((starMk z v).subgroupComap (JGstar z v)).ker
  sqtk := hlocal.subgroup _
  equiv := QuotientGroup.quotientKerEquivOfSurjective _
    ((starMk z v).subgroupComap_surjective_of_surjective _ (starMk_surjective z v))

/-- The source FF hypothesis, with no assumed decomposition or offender equality. -/
theorem thompson_hypothesis (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)] {K : GroupClass.{u}}
    (hlocal : IsSQTK K (Gv v)) (hcore : pCore 2 (Gstar z v) = ⊥) :
    FFHypothesis K (thompsonRepresentation z v hz) where
  finite_module := Module.Finite.of_finite
  faithful := thompsonRepresentation_faithful z v hz
  twoCore := JGstar_twoCore z v hcore
  generated := thompsonRepresentation_generated z v hz
  quotient := ⟨thompsonCover z v hlocal⟩

/-- The complete universal B.5.6 implication applies to this exact action. -/
theorem classify_thompson (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)] {K : GroupClass.{u}}
    (classification : FFAlternatives.ProjectiveLine.GeneralClassificationInput.{u,u} K)
    (hlocal : IsSQTK K (Gv v)) (hcore : pCore 2 (Gstar z v) = ⊥) :
    FFAlternatives.ProjectiveLine.SourceAlternative (thompsonRepresentation z v hz) :=
  classification _ _ _ (thompson_hypothesis z v hz hlocal hcore)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FittingCenter
