module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionPreparation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5LocalFactorization
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.Triality
public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# The normalized right factor in an original triality extension

The native triality two-core theorem applies to the image of the actual
source S under its right-parabolic embedding in Aut(³D₄(2ᵐ)). Transport back
through that embedding proves O₂(RS) = O₂(R). The same marking identifies
R/O₂(R) with PSL₂ over the base or cubic field. The original normalized
right Borel and genuine relative Sylows then give S = O₂(R)(S ∩ R), hence
S ≤ R. Both triality nodes are retained; no ambient Sylow is transported
through a map defined only on a source parabolic.

Source: Aschbacher--Smith F.1.12, printed p.264, and the original selected
pair in 5.2.6, pp.650--651 (`refs/quasithin.pdf`). This is the native-core
step of `Triality`, where both full endpoint maps and their overlap are
restricted to construct the actual comparison.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace OriginalTriality
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.ParabolicOuterTwo

variable {X : Type*} [Group X]
  (m : ℕ) (hm : 0 < m) (K U : Subgroup X) (hU : IsPGroup 2 U)
  (hn : U ≤ normalizer (K : Set X))
  (f : X →* MulAut (BinaryCarrier m hm)) (hf : Function.Injective f) (a : Node)
  (hK : K.map f = (localFactor (binaryParameters m hm) a).map MulAut.conj)

include hU hn hf hK in
private theorem core_eq : (K ⊔ U).pCoreIn 2 = K.pCoreIn 2 := by
  apply Subgroup.map_injective hf
  rw [map_pCoreIn_of_injective 2 _ _ hf, map_pCoreIn_of_injective 2 _ _ hf,
    Subgroup.map_sup, hK]
  refine embeddedLocal_twoCore_eq_of_action m hm a MulAut.conj
    (Theory.GroupTheory.conj_injective_of_center_eq_bot (binaryCarrier_center_eq_bot m hm))
    (MonoidHom.id _) Function.injective_id ?_ (U.map f) (hU.map f) ?_
  · intro x g
    ext y
    simp
  · rw [← hK]
    exact (Subgroup.map_mono hn).trans (Subgroup.le_normalizer_map f)

/-- The original selected-factor quotient, transported through its endpoint. -/
private def quotientEquiv :
    (K ⧸ pCore 2 K) ≃*
      (localFactor (binaryParameters m hm) a ⧸
        pCore 2 (localFactor (binaryParameters m hm) a)) :=
  let e : K ≃* localFactor (binaryParameters m hm) a :=
    ((K.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hK)).trans
      ((localFactor (binaryParameters m hm) a).equivMapOfInjective MulAut.conj
        (Theory.GroupTheory.conj_injective_of_center_eq_bot (binaryCarrier_center_eq_bot m hm))).symm
  QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
end OriginalTriality

section SourceRestriction
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R)
  (h : Input κ T L W n) (hTH : (T : Subgroup G) ≤ H)
  (m : ℕ) (hm : 0 < m) (a : Node)
  (f : ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 →* MulAut (BinaryCarrier m hm))
  (hf : Function.Injective f)
  (hR : (R.subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) 1)).map f =
    (localFactor (binaryParameters m hm) a).map MulAut.conj)

omit [Finite G] in
include d hf hR in
/-- The actual triality extension marking supplies the original right-core equality. -/
theorem Preparation.triality_extension_right_core :
    (R ⊔ sourceS L H).pCoreIn 2 = R.pCoreIn 2 := by
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  have hRP : R ≤ P := le_sup_left.trans le_sup_left
  have hSP : sourceS L H ≤ P := le_sup_right.trans le_sup_left
  have hn : (sourceS L H).subgroupOf P ≤ normalizer (R.subgroupOf P : Set P) := by
    rw [← subgroupOf_normalizer_eq hRP]
    exact comap_mono d.S_normalizes_right
  have hc := OriginalTriality.core_eq m hm (R.subgroupOf P)
    ((sourceS L H).subgroupOf P)
    (pCore_isPGroup.map _ : IsPGroup 2 (sourceS L H)).comap_subtype hn f hf a hR
  have hh := congrArg (Subgroup.map P.subtype) hc
  rw [map_pCoreIn_of_injective 2 _ _ P.subtype_injective,
    map_pCoreIn_of_injective 2 _ _ P.subtype_injective, Subgroup.map_sup,
    map_subgroupOf_eq_of_le hRP, map_subgroupOf_eq_of_le hSP] at hh
  exact hh

include d h hTH hf hR in
/-- The normalized original Borel forces S into the same selected R,
for either node of the genuine triality extension. -/
theorem Preparation.sourceS_le_right_of_triality_extension : sourceS L H ≤ R := by
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  have hRP : R ≤ P := le_sup_left.trans le_sup_left
  let e : R ≃* R.subgroupOf P := (subgroupOfEquivOfLe hRP).symm
  let q := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (OriginalTriality.quotientEquiv m hm (R.subgroupOf P) f hf a hR)
  have hs : sourceS L H = (R ⊔ sourceS L H).pCoreIn 2 ⊔ (sourceS L H ⊓ R) := by
    cases a
    · exact (d.hypothesisF11 h hTH).linear_local_sylow_factorization 1
        (ExtensionField (binaryParameters m hm))
        (q.trans (localFactorArmsQuotientEquivPSL2 (binaryParameters m hm) rfl))
        d.right_borel_normalizes_sourceS
    · exact (d.hypothesisF11 h hTH).linear_local_sylow_factorization 1
        (GaloisField 2 m)
        (q.trans (localFactorCentralQuotientEquivPSL2 (binaryParameters m hm) rfl))
        d.right_borel_normalizes_sourceS
  rw [d.triality_extension_right_core m hm a f hf hR] at hs
  exact hs.le.trans (sup_le (map_subtype_le _) inf_le_right)
end SourceRestriction
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
