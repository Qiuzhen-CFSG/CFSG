module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Trio.Conjugation
public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Trio.TensorSection
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.SourceFactors

/-!
# The native trio calculation for every marking

The actual M24 transporter carries the standard fixed three-space and both
commutator calculations to any native trio. It also transports the first-moment
identification of the middle section with the natural tensor product. The
quotient is by the intrinsic two-core of the stabilizer; the residual is its
intrinsic solvable residual mapped into M24. The full linear images give the
bottom and top irreducible factors, while the native tensor calculation gives
the middle irreducible factor.

Source: Aschbacher–Smith H.15.6, printed p.401, using H.14.1(3), printed p.396.
The middle section is V₉/V₃, correcting the printed V₉/V.
-/

@[expose] public section
open Representation Representation.BinaryOffender
open MathieuCode Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open scoped Pointwise
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
noncomputable section
open MathieuCode.TrioCalculation
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction

/-- Dimension of the intrinsic two-core fixed space, for every native trio. -/
theorem finrank_trioFixedSpace (T : Trio) :
    Module.finrank (ZMod 2) (trioFixedSpace T) = 3 := by
  obtain ⟨g, hg⟩ := trio_exists_smul_standard T
  rw [← (trioFixedTransport standardTrio T g hg).finrank_eq]
  exact finrank_standard_trioFixedSpace

theorem trioFixedSpace_le_trioPairSpace (T : Trio) :
    trioFixedSpace T ≤ trioPairSpace T := by
  obtain ⟨g, hg⟩ := trio_exists_smul_standard T
  rw [← trioFixedSpace_map standardTrio T g hg, ← trioPairSpace_map standardTrio T g hg]
  exact Submodule.map_mono standard_trioFixedSpace_le_trioPairSpace

theorem trioPairSpace_eq_kernel_commutator (T : Trio) :
    trioPairSpace T = subspaceCommutator cocodeRepresentation ⊤ (trioKernel T) := by
  obtain ⟨g, hg⟩ := trio_exists_smul_standard T
  rw [← trioPairSpace_map standardTrio T g hg, standard_trioPairSpace_eq_kernel_commutator,
    subspaceCommutator_top_map_conj, trioKernel_map standardTrio T g hg]

theorem trioPairSpace_eq_residual_commutator (T : Trio) :
    trioPairSpace T = subspaceCommutator cocodeRepresentation ⊤ (trioResidual T) := by
  obtain ⟨g, hg⟩ := trio_exists_smul_standard T
  rw [← trioPairSpace_map standardTrio T g hg, standard_trioPairSpace_eq_residual_commutator,
    subspaceCommutator_top_map_conj, trioResidual_map standardTrio T g hg]

theorem trioFixedSubrepresentation_surjective (T : Trio) :
    Function.Surjective (trioFixedSubrepresentation T).toRepresentation.asGroupHom := by
  obtain ⟨g, hg⟩ := trio_exists_smul_standard T
  let E := LinearMap.GeneralLinearGroup.congrLinearEquiv (trioFixedTransport standardTrio T g hg)
  intro f
  obtain ⟨h, hh⟩ := standard_trioFixedSubrepresentation_surjective (E.symm f)
  refine ⟨trioStabilizerTransport standardTrio T g hg h, ?_⟩
  have he : E ((trioFixedSubrepresentation standardTrio).toRepresentation.asGroupHom h) =
      (trioFixedSubrepresentation T).toRepresentation.asGroupHom
        (trioStabilizerTransport standardTrio T g hg h) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change trioFixedTransport standardTrio T g hg
      ((trioFixedSubrepresentation standardTrio).toRepresentation h
        ((trioFixedTransport standardTrio T g hg).symm v)) = _
    rw [trioFixedTransport_equivariant, LinearEquiv.apply_symm_apply]
    rfl
  rw [← he, hh]
  exact E.apply_symm_apply f

/-- A chosen actual M24 element carrying the standard partition to T. -/
def trioTransporter (T : Trio) : M24 := (trio_exists_smul_standard T).choose
lemma trioTransporter_spec (T : Trio) : trioTransporter T • standardTrio.parts = T.parts :=
  (trio_exists_smul_standard T).choose_spec

def trioMarking (T : Trio) : trioStabilizer standardTrio ≃* trioStabilizer T :=
  trioStabilizerTransport standardTrio T (trioTransporter T) (trioTransporter_spec T)

/-- Native affine quotient map in the chosen marking. -/
def trioAffineHom (T : Trio) : trioStabilizer T →* QuotientModel :=
  standardAffineHom.comp (trioMarking T).symm.toMonoidHom

theorem trioAffineHom_surjective (T : Trio) : Function.Surjective (trioAffineHom T) :=
  standardAffineHom_surjective.comp (trioMarking T).symm.surjective

theorem trioAffineHom_ker (T : Trio) :
    (trioAffineHom T).ker = pCore 2 (trioStabilizer T) := by
  rw [← pCore_map_iso 2 (trioMarking T)]
  ext h
  change (trioMarking T).symm h ∈ standardAffineHom.ker ↔ _
  rw [standardAffineHom_ker]
  constructor
  · intro hh
    exact ⟨(trioMarking T).symm h, hh, (trioMarking T).apply_symm_apply h⟩
  · rintro ⟨x, hx, rfl⟩
    change (trioMarking T).symm (trioMarking T x) ∈ pCore 2 (trioStabilizer standardTrio)
    rw [MulEquiv.symm_apply_apply]
    exact hx

/-- The literal stabilizer quotient by its intrinsic two-core. -/
def trioQuotientEquiv (T : Trio) :
    (trioStabilizer T ⧸ pCore 2 (trioStabilizer T)) ≃* QuotientModel :=
  (QuotientGroup.congr _ _ (trioMarking T).symm (pCore_map_iso 2 (trioMarking T).symm)).trans
    standardQuotientEquiv

lemma trioQuotientEquiv_mk (T : Trio) (h : trioStabilizer T) :
    trioQuotientEquiv T (QuotientGroup.mk h) = trioAffineHom T h := rfl

/-- The literal quotient, identified with the two factors in source order. -/
def trioSourceQuotientEquiv (T : Trio) :
    (trioStabilizer T ⧸ pCore 2 (trioStabilizer T)) ≃* SourceQuotientModel :=
  (trioQuotientEquiv T).trans sourceFactorsEquiv

def trioTensorRepresentation (T : Trio) :
    Representation (ZMod 2) (trioStabilizer T) NaturalTensor :=
  quotientTensorRepresentation.comp (trioAffineHom T)

/-- The literal middle section, identified using the native transporter and moment map. -/
def trioSectionEquiv (T : Trio) : TrioSection T ≃ₗ[ZMod 2] NaturalTensor :=
  (trioSectionTransport standardTrio T (trioTransporter T) (trioTransporter_spec T)).symm.trans
    standardSectionEquiv

lemma trioSectionEquiv_intertwines (T : Trio) (h : trioStabilizer T) (v : TrioSection T) :
    trioSectionEquiv T (trioSectionRepresentation T h v) =
      trioTensorRepresentation T h (trioSectionEquiv T v) := by
  let E := trioSectionTransport standardTrio T (trioTransporter T) (trioTransporter_spec T)
  have he : E.symm (trioSectionRepresentation T h v) =
      trioSectionRepresentation standardTrio ((trioMarking T).symm h) (E.symm v) := by
    apply E.injective
    rw [LinearEquiv.apply_symm_apply]
    rw [trioSectionTransport_equivariant]
    change trioSectionRepresentation T h v =
      trioSectionRepresentation T (trioMarking T ((trioMarking T).symm h)) (E (E.symm v))
    rw [MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  change standardSectionEquiv (E.symm (trioSectionRepresentation T h v)) =
    standardTensorRepresentation ((trioMarking T).symm h) (standardSectionEquiv (E.symm v))
  rw [he, standardSectionEquiv_intertwines]

def trioSectionRepresentationEquiv (T : Trio) :
    (trioSectionRepresentation T).Equiv (trioTensorRepresentation T) :=
  .mk (trioSectionEquiv T) (fun h => LinearMap.ext (trioSectionEquiv_intertwines T h))

theorem trioSection_irreducible (T : Trio) :
    Representation.IsIrreducible (trioSectionRepresentation T) := by
  apply Representation.RepEquiv.irreducible_of_euqiv
    (Representation.RepEquiv.ofRepresentationEquiv (trioSectionRepresentationEquiv T))
  exact (Representation.irreducible_comp_surjective_iff (trioAffineHom T)
    (trioAffineHom_surjective T) quotientTensorRepresentation).mpr
    quotientTensorRepresentation_irreducible

theorem trioFixed_irreducible (T : Trio) :
    Representation.IsIrreducible (trioFixedSubrepresentation T).toRepresentation := by
  let : Nontrivial (trioFixedSubrepresentation T).toSubmodule :=
    (show Nontrivial (trioFixedSpace T) from Module.nontrivial_of_finrank_pos
    (by rw [finrank_trioFixedSpace T]; decide : 0 < Module.finrank (ZMod 2) (trioFixedSpace T)))
  exact irreducible_of_full_linear_image _ (trioFixedSubrepresentation_surjective T)

theorem trioTop_irreducible (T : Trio) :
    Representation.IsIrreducible (trioTopRepresentation T) := by
  let : Nontrivial (Cocode ⧸ trioPairSpace T) := Module.nontrivial_of_finrank_pos
    (by rw [finrank_trioPairQuotient T]; decide : 0 < Module.finrank (ZMod 2) (Cocode ⧸ trioPairSpace T))
  exact irreducible_of_full_linear_image _ (trioTopRepresentation_surjective T)

/-- The tensor identification uses the actual quotient and the natural source factors. -/
theorem trioSectionEquiv_source_intertwines (T : Trio) (h : trioStabilizer T)
    (v : TrioSection T) :
    trioSectionEquiv T (trioSectionRepresentation T h v) =
      sourceTensorRepresentation (trioSourceQuotientEquiv T (QuotientGroup.mk h))
        (trioSectionEquiv T v) := by
  change trioSectionEquiv T (trioSectionRepresentation T h v) =
    sourceTensorRepresentation (sourceFactorsEquiv (trioQuotientEquiv T (QuotientGroup.mk h)))
      (trioSectionEquiv T v)
  rw [sourceTensorRepresentation_factors, trioQuotientEquiv_mk]
  exact trioSectionEquiv_intertwines T h v

end
end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
