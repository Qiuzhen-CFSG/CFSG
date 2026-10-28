module

public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Stellmacher.OmegaOneCenterMap

/-!
# The initial reductions in the noncentrality argument

These are local group calculations used in Lemma 13.3.14. Under the contrary
centrality assumption, characteristic two already places V₂ in Z(Q₁).
Its conjugate span lies in the first omega subgroup of that center; the
parabolic generation identity identifies it with the span of V₃. Thus this
particular application does not need the stronger conclusion of G.2.2.

The centralizing residual is the embedded O²(C_G(U)), not O₂(C_G(U)).
All normality assertions are relative to the specified local subgroup.
The source hypotheses and the remaining reductions are assembled separately.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 13.3.14(a) and the start of (b), printed p.891, PDF p.908.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Subgroup Stellmacher
variable {G : Type*} [Group G]

/-- The actual centralizing two-residual occurring in reduction (b). -/
def centralizingResidual (U : Subgroup G) : Subgroup G :=
  (pResidual 2 (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype

private theorem normalizes_centralizer (A : Subgroup G) :
    normalizer (A : Set G) ≤ normalizer (centralizer (A : Set G) : Set G) :=
  (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp inferInstance

private theorem normalizes_core (H : Subgroup G) :
    H ≤ normalizer (H.pCoreIn 2 : Set G) :=
  H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))

private theorem normalizes_omegaCenter (Q : Subgroup G) :
    normalizer (Q : Set G) ≤ normalizer (omegaOneCenterAmbient Q : Set G) := by
  intro g hg
  apply (mem_normalizer_iff_map_conj_eq).mpr
  rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective,
    (mem_normalizer_iff_map_conj_eq).mp hg]

/-- A parabolic conjugate span followed by a larger local span gives the
original local span. This retains the actual acting subgroups. -/
theorem conjugateSpan_absorb (A B H : Subgroup G) (hBH : B ≤ H) :
    conjugateSpanBy (conjugateSpanBy A B) H = conjugateSpanBy A H := by
  apply le_antisymm
  · exact conjugateSpanBy_le (conjugateSpanBy_mono le_rfl hBH)
      (le_normalizer_conjugateSpanBy A H)
  · exact conjugateSpanBy_mono (le_conjugateSpanBy A B) le_rfl

/-- A centralizing elementary seed has its entire local span in Ω₁(Z(O₂(H))).
Characteristic two is imposed on H, not on the ambient group. -/
theorem span_le_omegaCenter (A H : Subgroup G) [IsElementaryAbelian 2 A]
    (hAH : A ≤ H) (hH : H ∈ Chapter1.He G)
    (hc : A ≤ centralizer (H.pCoreIn 2 : Set G)) :
    conjugateSpanBy A H ≤ omegaOneCenterAmbient (H.pCoreIn 2) := by
  apply conjugateSpanBy_le
  · intro a ha
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hH ⟨hAH ha, hc ha⟩, elemPow_eq_one_of_isElementaryAbelian a ha, hc ha⟩
  · exact (normalizes_core H).trans (normalizes_omegaCenter _)

/-- Reduction (a), including both descriptions of U. The parabolic generation
identity is earlier flag geometry; neither containment conclusion is assumed. -/
theorem reduction_a (V₂ V₃ Lplus H : Subgroup G) [IsElementaryAbelian 2 V₂]
    (hV₂ : V₂ ≤ H) (hLplus : Lplus ≤ H)
    (hgen : V₃ = conjugateSpanBy V₂ Lplus) (hH : H ∈ Chapter1.He G)
    (hc : ⁅V₂, H.pCoreIn 2⁆ = ⊥) :
    conjugateSpanBy V₃ H = conjugateSpanBy V₂ H ∧
      conjugateSpanBy V₃ H ≤ omegaOneCenterAmbient (H.pCoreIn 2) := by
  have he : conjugateSpanBy V₃ H = conjugateSpanBy V₂ H := by
    rw [hgen, conjugateSpan_absorb V₂ Lplus H hLplus]
  exact ⟨he, he ▸ span_le_omegaCenter V₂ H hV₂ hH
    (commutator_eq_bot_iff_le_centralizer.mp hc)⟩

/-- The residual centralizes the original seed of any local conjugate span. -/
theorem centralizingResidual_le_seed_centralizer (V H : Subgroup G) :
    centralizingResidual (conjugateSpanBy V H) ≤ centralizer (V : Set G) :=
  (map_subtype_le _).trans (centralizer_le (le_conjugateSpanBy V H))

/-- The local group normalizes its centralizing residual. -/
theorem normalizes_centralizingResidual (V H : Subgroup G) :
    H ≤ normalizer (centralizingResidual (conjugateSpanBy V H) : Set G) :=
  ((le_normalizer_conjugateSpanBy V H).trans (normalizes_centralizer _)).trans
    (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))

/-- The flag's point centralizer contains the residual in the source argument. -/
theorem centralizingResidual_le_point_group (V₁ V₃ : Subgroup G)
    (hflag : V₁ ≤ V₃) :
    centralizingResidual (conjugateSpanBy V₃ (normalizer (V₁ : Set G))) ≤
      normalizer (V₁ : Set G) :=
  (centralizingResidual_le_seed_centralizer _ _).trans
    ((centralizer_le hflag).trans (Subgroup.centralizer_le_normalizer _))

/-- Y is two-perfect, as required by the normalizer-uniqueness argument. -/
theorem centralizingResidual_isPPerfect [Finite G] (U : Subgroup G) :
    IsPPerfect 2 (centralizingResidual U) := by
  let C := centralizer (U : Set G)
  let e := (pResidual 2 C).equivMapOfInjective C.subtype C.subtype_injective
  exact (isPPerfect_pResidual 2).of_surjective e.toMonoidHom e.surjective

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
