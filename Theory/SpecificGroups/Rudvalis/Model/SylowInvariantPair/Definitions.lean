module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.POrder
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.TwoPartBound
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers.Words

/-!
# Marking the Rudvalis local pair for ambient two-extensions

The fixed four-word subgroup has order 2¹⁴ and therefore is an ambient
 Sylow subgroup by the checked two-part bound. The first local is max4;
 the second is max6 conjugated by the inverse of the recorded GAP word.
 Actual subgroup equivalences retain the precise ATLAS quotient models.
 Invariance under Sylow-preserving automorphisms and generation remain
 separate mathematical obligations; neither is asserted by these definitions.

Source: GLS3 Table 5.3r, printed p.279; the extension application is
 Aschbacher–Smith E.1.14(5), printed p.214. Word attribution and the inverse
 conjugation convention are retained in the imported certificate modules.
-/

public section
open Subgroup
namespace Rudvalis.SylowInvariantPair
open SylowOvergroups
open RadicalCoverage.LocalCover

/-- The literal local word subgroup has odd index in the ambient model. -/
theorem localP_index_odd : ¬ 2 ∣ localP.index := by
  intro h
  apply RadicalCoverage.SylowCertificate.not_two_pow_fifteen_dvd_card_model
  rw [← localP.card_mul_index, IntrinsicSylow.localP_card]
  exact Nat.mul_dvd_mul_left 16384 h

/-- The Sylow marking to be aligned with the ambient normal intersection. -/
@[expose] noncomputable def sylow : Sylow 2 Model :=
  IntrinsicSylow.localP_isPGroup.toSylow localP_index_odd

/-- The two locals with the certified inverse-GAP conjugation convention. -/
@[expose] def locals : Fin 2 → Subgroup Model :=
  ![max4, max6.map (MulAut.conj Max6Certificate.conjugator).toMonoidHom]

/-- The first local has exactly the original max4 carrier. -/
def firstEquiv : locals 0 ≃* max4 := MulEquiv.refl _

/-- The second local is a conjugate of the original max6 carrier. -/
noncomputable def secondEquiv : locals 1 ≃* max6 :=
  ((MulAut.conj Max6Certificate.conjugator).subgroupMap max6).symm

end Rudvalis.SylowInvariantPair
