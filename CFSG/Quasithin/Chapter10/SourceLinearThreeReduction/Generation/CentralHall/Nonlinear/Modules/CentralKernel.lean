module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.RecognitionAction
public import CFSG.Quasithin.Chapter3.Section02.CenterObstruction
public import Theory.Representation.BinaryConjugationSection.Restriction

/-!
# Vanishing of the moved central kernel in the original Hall context

The central branch of 3.1.7 and the original 3.2.2 center obstruction force
C_{V_M}(L₀)=1 when the supplied H* centralizes Ω₁Z(T). Crossed geometry
then puts C_W(L), for W=[V_M,L], in this full fixed part: W centralizes the
other component, and the two components generate L₀. Thus C_W(L)=1.

Consequently genuine recognition of the faithful central quotient lifts to
whole-W coordinates in both the orthogonal and Suzuki rows. The natural
row retains its original central-quotient definition. The application to
the completed Hall calculations gives the original Hall exponent bound.

Exhaustive recognition and separated-seed construction still belong to
qt-d-10-nona5-central-hall-orders. They are explicit premises of the final
source assembly, not conclusions of the kernel argument.
Source: Aschbacher--Smith 3.1.7, 3.2.2(6), 10.1.1 and the centralizing-Z
branch of 10.2.3, printed pp.574,579,741,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} (c : Context D H B)

include c in
/-- In the original central Hall context the full orbit has no fixed part. -/
theorem fullCentralizer_eq_bot_of_central_hstar : D.fullCentralizer = ⊥ := by
  by_contra hc
  apply D.omega_center_not_le_center_of_fullCentralizer_ne_bot
    (source_module_nonsolvable_uniqueness D) hc c.hstar
  intro z hz
  have hzc := commutator_eq_bot_iff_le_centralizer.mp c.central hz
  have hzH : z ∈ H := c.hstar.1.1.2
    (((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
  refine ⟨⟨z,hzH⟩,mem_center_iff.mpr ?_,rfl⟩
  intro h
  exact Subtype.ext (hzc h h.property)

include c in
/-- Crossed geometry puts the moved fixed part in the full orbit fixed part,
so the literal central denominator vanishes in this particular Hall context. -/
theorem movedFixed_eq_bot_of_central_hstar (geometry : ModuleGeometry D) :
    sourceMovedFixed D = ⊥ := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  let W := ⁅D.fullModule,L⁆
  have htn' : t⁻¹ ∉ normalizer (L : Set G) := by
    intro hh
    exact htn (inv_mem_iff.mp hh)
  have hh := map_mono (f := (MulAut.conj t).toMonoidHom)
    (geometry.crossed t⁻¹ ((T : Subgroup G).inv_mem ht) htn')
  rw [Theory.GroupTheory.map_centralizer_equiv] at hh
  have hm : (W.map (MulAut.conj t⁻¹).toMonoidHom).map
      (MulAut.conj t).toMonoidHom = W := by
    rw [map_map]
    have he : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    rw [he,map_id]
  change (W.map (MulAut.conj t⁻¹).toMonoidHom).map (MulAut.conj t).toMonoidHom ≤ _ at hh
  rw [hm] at hh
  have hp : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 c.nonnormal)
      inf_le_right ht htn
  change W ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) at hh
  have hZC : sourceMovedFixed D ≤ centralizer (localOrbit T L : Set G) := by
    apply le_centralizer_iff.mpr
    rw [hp]
    exact sup_le (le_centralizer_iff.mp (show sourceMovedFixed D ≤ centralizer (L : Set G) from inf_le_right))
      (le_centralizer_iff.mp (inf_le_left.trans hh))
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  apply bot_unique
  intro w hw
  have hwC : w ∈ centralizer (localOrbit T L : Set G) := hZC hw
  have hm : (⟨w,hWV hw.1⟩ : D.fullModule) ∈ D.fullCentralizer := hwC
  rw [fullCentralizer_eq_bot_of_central_hstar D c] at hm
  exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hm))

local instance kernelMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The same original quotient coordinates now mark the whole moved module;
no model-specific central-cover assumption is needed in this Hall context. -/
def wholeMovedSection_of_central_hstar (geometry : ModuleGeometry D) :
    BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((movedQuotientAction D c.nonnormal).comp (QuotientGroup.mk' (pCore 2 L))) :=
  (movedQuotientSection D c.nonnormal).replaceKernel ⊥
    (movedFixed_eq_bot_of_central_hstar D c geometry)


open Representation.OrthogonalFourMinus.FiniteModel
local instance kernelFixedBinaryAlgebra (n : ℕ) : Algebra (ZMod 2) (fixedField n) :=
  ZMod.algebra _ 2
local instance kernelHermitianBinaryModule (n : ℕ) [NeZero n] : Module (ZMod 2) (Space n) :=
  Module.compHom (Space n) (algebraMap (ZMod 2) (fixedField n))

/-- The remaining recognition outputs on the faithful literal central quotient.
The orthogonal and Suzuki alternatives impose no vanishing-kernel premise. -/
inductive MovedQuotientRow
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) : Prop
  | natural (r : ℕ) (large : 1 < r)
      (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 r))
      (coordinates : letI : Algebra (ZMod 2) (GaloisField 2 r) := ZMod.algebra _ 2
        Nonempty ((movedQuotientAction D hn).Equiv
          (SL2.BinarySmall.natural.comp e.toMonoidHom))) : MovedQuotientRow hn
  | orthogonal (n : ℕ) [NeZero n] (large : 1 < n)
      (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field n))
      (coordinates : Nonempty ((movedQuotientAction D hn).Equiv
        ((SL2.BinarySmall.hermitian n).comp e.toMonoidHom))) : MovedQuotientRow hn
  | suzuki (m : ℕ) (positive : 0 < m)
      (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
      (coordinates : Nonempty ((movedQuotientAction D hn).Equiv
        ((SuzukiNatural.natural m).comp e.toMonoidHom))) : MovedQuotientRow hn

/-- Actual quotient recognition supplies all source rows, with both
whole-module kernels discharged from the original central-Hall hypotheses. -/
theorem moduleRow_of_movedQuotientRow (geometry : ModuleGeometry D)
    (row : MovedQuotientRow D c.nonnormal) : ModuleRow D := by
  cases row with
  | natural r hr e hE =>
    exact .natural r hr e ⟨natural_section_of_movedQuotient D c.nonnormal r e hE.some⟩
  | orthogonal n hn e hE =>
    exact .orthogonal n hn e ⟨(wholeMovedSection_of_central_hstar D c geometry).relabel
      (QuotientGroup.mk' (pCore 2 L)) hE.some⟩
  | suzuki m hm e hE =>
    exact .suzuki m hm e ⟨(wholeMovedSection_of_central_hstar D c geometry).relabel
      (QuotientGroup.mk' (pCore 2 L)) hE.some⟩

/-- The original Hall exponent conclusion now needs only the quotient models;
no central-cover callback remains for either whole-module row. -/
theorem hall_exponent_of_movedQuotientRow (geometry : ModuleGeometry D)
    (row : MovedQuotientRow D c.nonnormal) :
    ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2 ^ n + 1 := by
  have hall := HallGeometry.source_hallGeometryAt T L D H B c geometry
  cases moduleRow_of_movedQuotientRow D c geometry row with
  | natural r hr e hd => exact (hall.natural_excluded r hr e hd.some).elim
  | orthogonal n hn e hd =>
    obtain ⟨e',⟨p⟩⟩ := hall.orthogonal n hn e hd.some
    obtain ⟨f,hf⟩ := p.image_embedding c.faithful
    exact ⟨n,hn,exponent_dvd_of_image_embedding D B c.hall_le c.faithful n f hf⟩
  | suzuki m hm e hd => exact (hall.suzuki_excluded m hm e hd.some).elim

/-- The source recognition still to be proved, stated entirely on the literal
faithful central quotient. It has the same exact hypotheses as MovedRecognitionAt. -/
@[expose] def MovedQuotientRecognitionAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (H : Subgroup G) (B : Subgroup H) (c : Context D H B),
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    Chapter1.Section02.NonnormalCComponentModel (L ⧸ pCore 2 L) →
    SourceLocalModuleCubicBound D → SourceFullModuleCubicBound D →
    ModuleGeometry D → MovedMinimal D → MovedQuotientRow D c.nonnormal

/-- Discharge precisely the kernel and coordinate obligations in the original
moved-recognition contract; exhaustive quotient classification remains explicit. -/
theorem movedRecognition_of_quotientRecognition
    (h : MovedQuotientRecognitionAt T) : MovedRecognitionAt T := by
  intro L D H B c hnot hmodels hlocal hfull geometry hmin
  exact moduleRow_of_movedQuotientRow D c geometry
    (h L D H B c hnot hmodels hlocal hfull geometry hmin)

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
