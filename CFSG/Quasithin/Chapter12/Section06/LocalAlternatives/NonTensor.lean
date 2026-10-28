module
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Consequences
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.CubicMovement
public import Theory.GroupTheory.Commutator.TwoPerfectLayers

/-!
# Excluding the non-tensor wreath filtration

The two local components act on the original abelian point span U_H.
Their mixed commutator vanishes on both layers of the stated filtration
modulo the central point V₁. Two-perfectness removes these central errors.
A literal cubic in the marked A₄ × A₄ action then moves a nonsingular
vector in V₅. The opposite component centralizes it, contradicting the
nonsingular-centralizer bound and its conjugacy to an escaping component.

This proves the exclusion of case (a) in 12.6.33 from its explicit local
filtration and action marking. The F.9 hypothesis, abelian-span conclusion
12.6.26, component placement and filtration alternative still need their
source constructions. The original chosen-module application is in
`NaturalSource/NonTensor`.

Source: Aschbacher--Smith, proof of Lemma 12.6.33, printed pp.837--838
(PDF pp.854--855), using Theorem 12.6.2.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup
open BinaryPermutation
open BinaryPermutation.TerminalOrthogonal
variable {G : Type*} [Group G] (D : Setup G)

/-- A cubic of the literal four-block action moves a nonsingular vector
inside the original hyperplane. -/
theorem exists_nonsingular_cubic_commutator
    (r : Equiv.Perm (Fin 8))
    (hz : (D.coordinates D.z).toAdd = naturalRepresentation (Fin 8) r CubicMovement.point)
    (x : G) (hx : x ∈ normalizer (D.V : Set G))
    (a : FourBlockResidual.Product) (ha : a ^ 3 = 1) (hne : a ≠ 1)
    (he : ∀ v : D.V,
      (D.coordinates (D.V.normalizerMonoidHom ⟨x,hx⟩ v)).toAdd =
        naturalRepresentation (Fin 8) (r * FourBlockResidual.blockHom a * r⁻¹) (D.coordinates v).toAdd) :
    ∃ u : D.V, (u : G) ∈ ⁅D.V₅,zpowers x⁆ ∧
      Eight.form (D.coordinates u).toAdd = 1 := by
  obtain ⟨v,hv,hq⟩ := CubicMovement.conjugate_cubic_moved_nonsingular r a ha hne
  let w : D.V := D.coordinates.symm (Multiplicative.ofAdd v)
  have hw : (D.coordinates w).toAdd = v := by simp [w]
  have hw5 : (w : G) ∈ D.V₅ := by
    apply (D.mem_V₅_iff w).mpr
    rw [hz,hw]
    exact hv
  let u : D.V := D.V.normalizerMonoidHom ⟨x,hx⟩ w * w⁻¹
  have heq : (D.coordinates u).toAdd =
      naturalRepresentation (Fin 8) (r * FourBlockResidual.blockHom a * r⁻¹) v - v := by
    change (D.coordinates (D.V.normalizerMonoidHom ⟨x,hx⟩ w * w⁻¹)).toAdd = _
    rw [map_mul,map_inv]
    rw [toAdd_mul,toAdd_inv,←sub_eq_add_neg]
    rw [he,hw]
  refine ⟨u,?_,heq ▸ hq⟩
  rw [commutator_comm]
  exact commutator_mem_commutator (mem_zpowers x) hw5

variable [Finite G]

/-- The non-tensor filtration in 12.6.33 cannot occur for two escaping
components with their actual cubic marking. The lower mixed commutator
need only vanish modulo V₁; two-perfectness removes that central error. -/
theorem nonTensor_wreath_impossible
    {H : Subgroup G} (h : (D.f9 H).Hypothesis)
    (habelian : IsMulCommutative (D.UH H))
    (r : Equiv.Perm (Fin 8))
    (hz : (D.coordinates D.z).toAdd = naturalRepresentation (Fin 8) r CubicMovement.point)
    (hpoint : ∀ u : D.V, Eight.form (D.coordinates u).toAdd ≠ 0 →
      centralizer ({(u : G)} : Set G) ≤ D.M)
    (K₁ K₂ I : Subgroup H)
    (hp₁ : IsPPerfect 2 K₁) (hp₂ : IsPPerfect 2 K₂)
    (hn₁ : K₁ ≤ normalizer (K₂ : Set H))
    (hn₂ : K₂ ≤ normalizer (K₁ : Set H))
    (hcomm : ⁅K₁,K₂⁆ ≤ pCore 2 H)
    (hupper : ⁅⁅(D.UH H).subgroupOf H,K₁⁆,K₂⁆ ≤ I)
    (hlower : ⁅⁅I,K₁⁆,K₂⁆ ≤ D.V₁.subgroupOf H)
    (hM : D.M = normalizer (D.L : Set G))
    (hout : ¬ K₁.map H.subtype ≤ D.M)
    (t : G) (ht : t ∈ (D.T : Subgroup G))
    (hswap : (K₁.map H.subtype).map (MulAut.conj t).toMonoidHom = K₂.map H.subtype)
    (x : H) (hx₁ : x ∈ K₁) (hxV : (x : G) ∈ normalizer (D.V : Set G))
    (a : FourBlockResidual.Product) (ha : a ^ 3 = 1) (hne : a ≠ 1)
    (he : ∀ v : D.V,
      (D.coordinates (D.V.normalizerMonoidHom ⟨(x : G),hxV⟩ v)).toAdd =
        naturalRepresentation (Fin 8) (r * FourBlockResidual.blockHom a * r⁻¹) (D.coordinates v).toAdd) :
    False := by
  let U : Subgroup H := (D.UH H).subgroupOf H
  let Z : Subgroup H := D.V₁.subgroupOf H
  let : IsMulCommutative (D.UH H) := habelian
  let : IsMulCommutative U := inferInstance
  let : U.Normal := h.UH_normal
  let : Z.Normal := h.point_normal
  have hU : IsPGroup 2 U :=
    ((isPGroup_pCoreIn 2 H).to_le h.UH_le_QH).comap_subtype
  have hZ : Z ≤ center H := by
    intro z hz'
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    exact ((h.H_centralizes y.property) z hz').symm
  have hcross : ⁅⁅K₁,K₂⁆,U⁆ ≤ Z := by
    apply commutator_le.mpr
    intro k hk u hu
    have hc := h.commutator_UH_QH_le_point
      (commutator_mem_commutator hu (mem_map_of_mem H.subtype (hcomm hk)))
    change ⁅(u : G),(k : G)⁆ ∈ D.V₁ at hc
    change ⁅(k : G),(u : G)⁆ ∈ D.V₁
    simpa only [commutatorElement_inv] using D.V₁.inv_mem hc
  have hzero : ⁅⁅U,K₁⁆,K₂⁆ = ⊥ :=
    Subgroup.twoPerfect_mixed_commutator_eq_bot_modulo U I K₁ K₂ Z
      hU hp₁ hp₂ le_normalizer_of_normal le_normalizer_of_normal
      hn₁ hn₂ hZ hcross hupper hlower
  obtain ⟨u,hu,hq⟩ := D.exists_nonsingular_cubic_commutator r hz (x : G) hxV a ha hne he
  have hHU : (⁅U,K₁⁆).map H.subtype = ⁅D.UH H,K₁.map H.subtype⁆ := by
    rw [map_commutator]
    change ⁅((D.UH H).subgroupOf H).map H.subtype,K₁.map H.subtype⁆ = _
    rw [map_subgroupOf_eq_of_le (show D.UH H ≤ H from h.UH_le_H)]
  have hu' : (u : G) ∈ (⁅U,K₁⁆).map H.subtype := by
    rw [hHU]
    exact (commutator_mono (le_conjugateSpanBy D.V₅ H)
      (zpowers_le.mpr (mem_map_of_mem H.subtype hx₁))) hu
  obtain ⟨uH,huH,heu⟩ := hu'
  have hout₂ : ¬ K₂.map H.subtype ≤ D.M := by
    intro hK₂
    apply hout
    intro k hk
    have htM : t ∈ D.M := hM.symm ▸ h.normalizes_L ht
    have hkM : t * k * t⁻¹ ∈ D.M :=
      hK₂ (hswap ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom hk)
    have hh := D.M.mul_mem (D.M.mul_mem (D.M.inv_mem htM) hkM) htM
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh
  apply hout₂
  rintro k ⟨k,hk,rfl⟩
  apply hpoint u (by rw [hq]; exact one_ne_zero)
  rw [mem_centralizer_singleton_iff]
  have hc := (commutator_eq_bot_iff_le_centralizer.mp hzero) huH k hk
  have heG := congrArg Subtype.val hc
  change (k : G) * (uH : G) = (uH : G) * (k : G) at heG
  change (uH : G) = (u : G) at heu
  rw [heu] at heG
  exact heG
end CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup
