module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner.Marks

/-!
# Literal quotient transport for the marked partner

Subgroups containing Z are recovered from their images in U/Z. Thus the
relative normalizer of V₀ is exactly the stabilizer of its quotient image
under the actual conjugation action. The full marked action also identifies
its parameter kernel with the actual actor kernel; it is not merely an
abstract four-group label.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.48(3), 15.3.56(3–5), and 15.3.59, printed pp.1144, 1147–1150.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian

variable {G : Type*} [Group G]
variable (Z ZS : Subgroup G) [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- Quotient membership detects membership in any subgroup containing Z. -/
theorem vectorImage_mk_iff (A : Subgroup G) (hZA : Z ≤ A) (u : closureU Z ZS) :
    QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) u ∈ vectorImage Z ZS A ↔
      (u : G) ∈ A := by
  constructor
  · rintro ⟨a, ha, he⟩
    have hd : u / a ∈ Z.subgroupOf (closureU Z ZS) :=
      QuotientGroup.eq_iff_div_mem.mp he.symm
    have hh := A.mul_mem (hZA hd) ha
    change ((u : G) / (a : G)) * (a : G) ∈ A at hh
    simpa only [div_mul_cancel] using hh
  · intro hu
    exact ⟨u, hu, rfl⟩

/-- The normalizer acts on the actual quotient line, and conversely.
Containment V₀ ≤ U and Z ≤ V₀ are retained in the converse. -/
theorem mem_markedNormalizer_iff (V₀ : Subgroup G)
    (hZV : Z ≤ V₀) (hVU : V₀ ≤ closureU Z ZS) (h : centralizerH Z) :
    (h : G) ∈ markedNormalizer Z V₀ ↔
      ∀ w : VectorQuotient Z ZS,
        quotientAction Z ZS h w ∈ vectorImage Z ZS V₀ ↔
          w ∈ vectorImage Z ZS V₀ := by
  have hu := mem_normalizer_iff.mp (H_normalizes_closureU Z ZS h.property)
  constructor
  · intro hn w
    induction w using QuotientGroup.induction_on with
    | H u =>
      change quotientAction Z ZS h (QuotientGroup.mk' _ u) ∈ vectorImage Z ZS V₀ ↔
        QuotientGroup.mk' _ u ∈ vectorImage Z ZS V₀
      rw [quotientAction_mk, vectorImage_mk_iff Z ZS V₀ hZV,
        vectorImage_mk_iff Z ZS V₀ hZV]
      exact (mem_normalizer_iff.mp hn.2 u).symm
  · intro hw
    refine ⟨h.property, mem_normalizer_iff.mpr ?_⟩
    intro x
    constructor
    · intro hx
      have he := hw (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) ⟨x, hVU hx⟩)
      rw [quotientAction_mk, vectorImage_mk_iff Z ZS V₀ hZV,
        vectorImage_mk_iff Z ZS V₀ hZV] at he
      exact he.mpr hx
    · intro hx
      have hxU : x ∈ closureU Z ZS := (hu x).mpr (hVU hx)
      have he := hw (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) ⟨x, hxU⟩)
      rw [quotientAction_mk, vectorImage_mk_iff Z ZS V₀ hZV,
        vectorImage_mk_iff Z ZS V₀ hZV] at he
      exact he.mp hx

namespace MarkedAction
variable {Z ZS}
variable {V₀ : Subgroup G} {y t : G} {hXH : partnerX Z ZS y ≤ centralizerH Z}

/-- Faithfulness of the natural matrix action makes the transvection parameter
kernel exactly the kernel of the actual conjugation action on U/Z. -/
theorem parameter_eq_one_iff (m : MarkedAction Z ZS V₀ y t hXH)
    (x : partnerX Z ZS y) :
    m.parameter x = 1 ↔ quotientAction Z ZS ⟨x, hXH x.property⟩ = 1 := by
  constructor
  · intro hx
    apply MulEquiv.ext
    intro w
    apply m.coordinates.injective
    apply Multiplicative.toAdd.injective
    have hh := m.equivariant x w
    simpa only [hx, Subgroup.coe_one, map_one, Module.End.one_apply, MulAut.one_apply,
      Prod.mk.eta] using hh
  · intro hx
    apply Subtype.ext
    apply Subtype.ext
    apply Matrix.mulVec_injective
    funext v
    have hh := congrArg Prod.fst
      (m.equivariant x (m.coordinates.symm (Multiplicative.ofAdd (v, 0))))
    simp only [hx, MulAut.one_apply, MulEquiv.apply_symm_apply] at hh
    change v = BinaryLinearThree.W (m.parameter x).val v at hh
    change (m.parameter x).val.val.mulVec v =
      (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v
    rw [Matrix.one_mulVec]
    exact hh.symm

/-- In the actual faithful actor quotient the parameter kills exactly X ∩ Q_H. -/
theorem parameter_eq_one_iff_mem_core (m : MarkedAction Z ZS V₀ y t hXH)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (x : partnerX Z ZS y) : m.parameter x = 1 ↔ (x : G) ∈ coreQ Z := by
  rw [m.parameter_eq_one_iff]
  change (⟨x, hXH x.property⟩ : centralizerH Z) ∈ (quotientAction Z ZS).ker ↔ _
  rw [hkernel]
  exact ((QuotientGroup.eq_one_iff _).symm).trans
    (actorProjection_eq_one_iff Z ⟨x, hXH x.property⟩)

/-- Retaining the source X ∩ Q_H = E identifies the literal parameter kernel. -/
theorem parameter_ker (m : MarkedAction Z ZS V₀ y t hXH)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hXQ : partnerX Z ZS y ⊓ coreQ Z = intersectionE Z ZS y) :
    m.parameter.ker = (intersectionE Z ZS y).subgroupOf (partnerX Z ZS y) := by
  ext x
  change m.parameter x = 1 ↔ (x : G) ∈ intersectionE Z ZS y
  rw [m.parameter_eq_one_iff_mem_core hkernel, ← hXQ]
  exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩

/-- The literal actor projection restricted to X. -/
def projection (hXH : partnerX Z ZS y ≤ centralizerH Z) :
    partnerX Z ZS y →* ActorQuotient Z :=
  (actorProjection Z).comp (inclusion hXH)

omit [(Z.subgroupOf (closureU Z ZS)).Normal] in
/-- Restricting the ambient projection to X gives exactly the published actor image. -/
theorem projection_range : (projection hXH).range = actorImage Z (partnerX Z ZS y) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨inclusion hXH x, x.property, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The marked representation and the ambient actor projection have the same kernel. -/
theorem projection_ker (m : MarkedAction Z ZS V₀ y t hXH)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) :
    (projection hXH).ker = m.parameter.ker := by
  ext x
  exact (actorProjection_eq_one_iff Z (inclusion hXH x)).trans
    (m.parameter_eq_one_iff_mem_core hkernel x).symm

/-- An actual four-group equivalence, induced by the two literal maps from X. -/
noncomputable def actorEquiv (m : MarkedAction Z ZS V₀ y t hXH)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) :
    actorImage Z (partnerX Z ZS y) ≃* Matrix.PSL3Two.MarkedAutomorphisms.pointV :=
  (MulEquiv.subgroupCongr (projection_range (hXH := hXH))).symm.trans
    ((QuotientGroup.quotientKerEquivRange (projection hXH)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (m.projection_ker hkernel)).trans
        (QuotientGroup.quotientKerEquivOfSurjective m.parameter m.full)))

/-- The equivalence is compatible with the parameter of every element of X. -/
theorem actorEquiv_projection (m : MarkedAction Z ZS V₀ y t hXH)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (x : partnerX Z ZS y) :
    m.actorEquiv hkernel
      ⟨projection hXH x,
        projection_range (hXH := hXH) ▸ (MonoidHom.mem_range.mpr ⟨x, rfl⟩)⟩ =
        m.parameter x := by
  change (QuotientGroup.quotientKerEquivOfSurjective m.parameter m.full)
    (QuotientGroup.quotientMulEquivOfEq (m.projection_ker hkernel)
      ((QuotientGroup.quotientKerEquivRange (projection hXH)).symm
        ((QuotientGroup.quotientKerEquivRange (projection hXH))
          (QuotientGroup.mk x)))) = m.parameter x
  rw [MulEquiv.symm_apply_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- The full marked action, rather than an abstract tag, forces actor order four. -/
theorem actor_card (m : MarkedAction Z ZS V₀ y t hXH)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) :
    Nat.card (actorImage Z (partnerX Z ZS y)) = 4 :=
  (Nat.card_congr (m.actorEquiv hkernel).toEquiv).trans
    Matrix.PSL3Two.MarkedAutomorphisms.card_pointV

end MarkedAction
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner
