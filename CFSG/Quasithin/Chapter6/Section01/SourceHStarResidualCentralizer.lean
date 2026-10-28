module
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarResidualExtraction
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarJoinCentralizer
public import Theory.GroupTheory.NormalClosureCentralizerCore
public import Theory.GroupTheory.PResidual.CommutatorImage

/-!
# The canonical residual in the H-star orbit centralizer

Let C = C_H(⟨Ω₁(Z(T))ᴴ⟩) and X = O²(C), embedded in H. Normality of
the orbit makes X normal in H. Thus the two-perfect elimination theorem
applies to X as soon as X = [X,J(T)]. It follows that C is a normal
two-group; reducedness of the orbit gives C = O₂(H).

The quotient version asks only for the commutator identity on the actual
image of X in H/O₂(H). Two-perfectness lifts that identity through the
two-core. The final application supplies the exact centralizer equality
used for the left Cartan join on the next source page.

The commutator identity remains an explicit source input. In particular,
normality of X alone is not asserted to imply it, and this module does not
claim the extraspecial extraction in the preceding source paragraph.

Source: Aschbacher--Smith 6.1.5, printed pp.666--667, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise

namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H A : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- The canonical residual needs only its actual Thompson commutator identity;
its perfectness and normality are derived on the original carriers. -/
theorem hstar_omega_orbit_centralizer_eq_core_of_residual_commutator
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hcomm :
      let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
      let C := centralizer (U : Set H)
      let X := (pResidual 2 C).map C.subtype
      X = ⁅X, elementaryAbelianMaxJ (T.subtype hH.1.1.2 : Subgroup H)⁆) :
    centralizer
      (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) :
        Set H) = pCore 2 H := by
  by_contra hne
  let U₀ := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
  let U := U₀.subgroupOf H
  let C := centralizer (U : Set H)
  let X := (pResidual 2 C).map C.subtype
  let Y := X.map H.subtype
  obtain ⟨hYne,hYX,hTY,hKY,hYC,_,_⟩ :=
    h.hstar_omega_orbit_residual_extraction hout hH hZH hne
  have hJmap : (elementaryAbelianMaxJ
      (T.subtype hH.1.1.2 : Subgroup H)).map H.subtype =
        elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    exact congrArg elementaryAbelianMaxJ (map_subgroupOf_eq_of_le hH.1.1.2)
  have hYcomm : Y = ⁅Y, elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
    have he := congrArg (map H.subtype) hcomm
    simpa only [map_commutator, hJmap] using he
  exact hYne (h.hstar_twoPerfect_orbit_centralizer_eq_bot_of_residual_normalized
    hout hH hm hZH hYX hTY hKY hYC hYcomm)

/-- Only commutator generation in the literal two-core quotient is needed:
the normal two-perfect residual lifts it to the full original subgroup. -/
theorem hstar_omega_orbit_centralizer_eq_core_of_residual_quotient_commutator
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hcomm :
      let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
      let C := centralizer (U : Set H)
      let X := (pResidual 2 C).map C.subtype
      let q := QuotientGroup.mk' (pCore 2 H)
      X.map q = ⁅X.map q,
        (elementaryAbelianMaxJ (T.subtype hH.1.1.2 : Subgroup H)).map q⁆) :
    centralizer
      (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) :
        Set H) = pCore 2 H := by
  apply h.hstar_omega_orbit_centralizer_eq_core_of_residual_commutator hout hH hm hZH
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := (h.rankOneInput hout).hstar_omega_orbit_reduced
    (h.maximal_eq_normalizer_L ▸ hH)
  let := hU.normal
  let C := centralizer (U : Set H)
  let X := (pResidual 2 C).map C.subtype
  exact eq_commutator_of_isPPerfect_of_map_eq X _
    (isPPerfect_embedded_pResidual 2 C) le_normalizer_of_normal
    (QuotientGroup.mk' (pCore 2 H))
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) hcomm

/-- The canonical residual identity discharges the preceding centralizer
premise of the actual Cartan-join core computation on source p.667. -/
theorem hstar_join_core_eq_sylow_centralizer_of_residual_commutator
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hcomm :
      let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
      let C := centralizer (U : Set H)
      let X := (pResidual 2 C).map C.subtype
      X = ⁅X, elementaryAbelianMaxJ (T.subtype hH.1.1.2 : Subgroup H)⁆)
    (hX : A ⊔ H ∈ Chapter1.HOver G (T : Set G))
    (hperm : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G))
    (hfaith : A ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥) :
    (A ⊔ H).pCoreIn 2 = (T : Subgroup G) ⊓ centralizer
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ H) : Set G) :=
  h.hstar_join_core_eq_sylow_centralizer hH hX hperm hfaith
    (h.hstar_omega_orbit_centralizer_eq_core_of_residual_commutator hout hH hm hZH hcomm)

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
