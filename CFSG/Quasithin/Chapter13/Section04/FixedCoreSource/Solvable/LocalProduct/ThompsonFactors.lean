module
public import CFSG.Quasithin.ChapterB.Section02.RelativeThompsonFactors
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CentralizerModule

/-!
# The Thompson-span factors in the original involution centralizer

Take the literal H=C_G(z), its reduced module V_H=⟨Ω₁(Z(T))^H⟩, and
its centralizer quotient H/C_H(V_H). For a subgroup R of the original T
containing O₂(H), nontrivial action by J(R) gives a faithful image of
⟨J(R)^H⟩ isomorphic to S₃ or S₃×S₃. The proof transports J(R) and its
normal span through the original subgroup inclusions. The quasithin
hypothesis bounds the three-rank of H itself; it does not assert rank
monotonicity across the centralizer quotient.

This applies the B.2.10/B.1.8 stable-family step to the actual group and
module used in 13.4.8–9. The source subgroup R₁ must still be shown to
contain O₂(H) and to act nontrivially. Choosing one factor, identifying
the two-core kernel, and constructing the C₃ chamber remain obligations
of qt-d-1341-solvable-source. Earlier source inputs retain final discharge
with qt-d-1341-fixed-core-source.

Source: Aschbacher–Smith, 13.4.8–9, printed pp. 904–906.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual centralizer quotient of the original Thompson span has one or two factors. -/
theorem centralizer_thompson_span_models
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (hQR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ R)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z} : Set G))) :
    let H := centralizer ({z} : Set G)
    let U := (centralizerOmegaOrbit T z).subgroupOf H
    letI := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
    let q := QuotientGroup.mk' (centralizer (U : Set H))
    Nonempty ((((conjugateSpanBy (elementaryAbelianMaxJ R) H).subgroupOf H).map q) ≃*
      Equiv.Perm (Fin 3)) ∨
    Nonempty ((((conjugateSpanBy (elementaryAbelianMaxJ R) H).subgroupOf H).map q) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let H := centralizer ({z} : Set G)
  let U := (centralizerOmegaOrbit T z).subgroupOf H
  have hU := centralizerOmegaOrbit_reduced h₀ hz hz1
  let := hU.normal
  let := hU.elementary
  let q := QuotientGroup.mk' (centralizer (U : Set H))
  have hq := QuotientGroup.mk'_surjective (centralizer (U : Set H))
  have hker : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' _
  have hRH : R ≤ H := hRT.trans (original_sylow_le_centralizer hz)
  have hUR : U ≤ R.subgroupOf H :=
    fun _ hx => hQR (centralizerOmegaOrbit_le_core h₀ hz hz1 hx)
  have hmapJ : (elementaryAbelianMaxJ (R.subgroupOf H)).map H.subtype =
      elementaryAbelianMaxJ R := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hRH]
  have hJi : ¬ elementaryAbelianMaxJ (R.subgroupOf H) ≤ q.ker := by
    rw [hker]
    intro hc
    apply hJ
    rw [← hmapJ]
    rintro x ⟨a, ha, rfl⟩ v hv
    exact congrArg Subtype.val
      ((hc ha) ⟨v, centralizerOmegaOrbit_le hz hv⟩ hv)
  have hspan : conjugateSpanBy (elementaryAbelianMaxJ (R.subgroupOf H)) ⊤ =
      (conjugateSpanBy (elementaryAbelianMaxJ R) H).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_conjugateSpanBy, hmapJ, ← MonoidHom.range_eq_map, H.range_subtype,
      map_subgroupOf_eq_of_le]
    exact conjugateSpanBy_le_self
      ((sSup_le fun _ hA => hA.1).trans hRH)
  have hrank : primeRank 3 H ≤ 2 :=
    (isQuasithin_iff_twoLocal.mp h₀.qtke.quasithin) H
      (isTwoLocal_involution_centralizer
        (orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.1 hz1))
      3 (by decide) (by decide)
  have hm := ChapterB.relative_thompson_span_models U (R.subgroupOf H) hUR
    q hq hker hJi hsolv hU.quotient_pCore_eq_bot hrank
  rwa [hspan] at hm

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
