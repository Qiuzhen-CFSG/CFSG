module

public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.Mathieu.M22.Basic

/-!
# The intrinsic type-J₄ hypotheses

For a finite group and an involution z, put C = C_G(z) and Q = F*(C).
The source requires Q extraspecial of order 2¹³, a normal subgroup of order
three in C/Q with quotient Aut(M₂₂), and a conjugate of z in Q other than z.
The order-three kernel is retained by an actual surjective homomorphism;
neither a bare Aut(M₂₂) quotient nor a group-family label expresses this data.

We use the source's set inequality in `IsTypeJ4` and prove its equivalence
with an explicit ambient conjugator. We also identify Q with O₂(C). These
are interface lemmas, not a uniqueness or recognition theorem.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*, Invent.
Math. 105 (1991), 589–607, DOI 10.1007/BF01232280; the authors' exposition,
*The study of J₄ via the theory of uniqueness systems*, in *Groups,
Combinatorics and Geometry* (1992), p.12. The consumer is Aschbacher–Smith
8.2.14, printed p.723 (combined manuscript PDF p.740).
-/

@[expose] public section

namespace Theory.GroupTheory.Recognition.JankoFour

open Subgroup
open scoped IsMulCommutative

/-- An extension of a group of order three by the actual automorphism group
of the native Mathieu group. The middle group and its quotient map are fixed. -/
structure CubicAutomorphismQuotient (H : Type*) [Group H] where
  projection : H →* MulAut Sporadic.Mathieu.M22
  surjective : Function.Surjective projection
  kernel_card : Nat.card projection.ker = 3

/-- The quotient by the retained normal cubic kernel is Aut(M₂₂). -/
noncomputable def CubicAutomorphismQuotient.quotientEquiv
    {H : Type*} [Group H] (e : CubicAutomorphismQuotient H) :
    (H ⧸ e.projection.ker) ≃* MulAut Sporadic.Mathieu.M22 :=
  QuotientGroup.quotientKerEquivOfSurjective e.projection e.surjective

@[simp] theorem CubicAutomorphismQuotient.quotientEquiv_mk
    {H : Type*} [Group H] (e : CubicAutomorphismQuotient H) (h : H) :
    e.quotientEquiv (QuotientGroup.mk' e.projection.ker h) = e.projection h := rfl

/-- A literal normal cubic subgroup and an isomorphism of the quotient
supply exactly the retained extension map. -/
noncomputable def CubicAutomorphismQuotient.ofNormalSubgroup
    {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    (hN : Nat.card N = 3) (e : (H ⧸ N) ≃* MulAut Sporadic.Mathieu.M22) :
    CubicAutomorphismQuotient H where
  projection := e.toMonoidHom.comp (QuotientGroup.mk' N)
  surjective := e.surjective.comp (QuotientGroup.mk'_surjective N)
  kernel_card := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
    exact hN

/-- The homomorphism formulation is equivalent to the source's normal
subgroup and quotient formulation, including relative normality. -/
theorem nonempty_cubic_iff_normal_subgroup {H : Type*} [Group H] :
    Nonempty (CubicAutomorphismQuotient H) ↔
      ∃ (N : Subgroup H) (hN : N.Normal),
        letI := hN
        Nat.card N = 3 ∧ Nonempty ((H ⧸ N) ≃* MulAut Sporadic.Mathieu.M22) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.projection.ker, inferInstance, e.kernel_card, ⟨e.quotientEquiv⟩⟩
  · rintro ⟨N, hN, hc, ⟨e⟩⟩
    exact ⟨CubicAutomorphismQuotient.ofNormalSubgroup N hc e⟩

variable {G : Type*} [Group G] [Finite G]

/-- The literal ambient centralizer of the marked element. -/
abbrev centralizer (z : G) : Subgroup G := Subgroup.centralizer ({z} : Set G)

/-- The intrinsic generalized Fitting subgroup, inside the centralizer. -/
abbrev core (z : G) : Subgroup (centralizer z) := generalizedFitting (centralizer z)

/-- Its image in the original ambient group, used for ambient fusion. -/
def ambientCore (z : G) : Subgroup G := (core z).map (centralizer z).subtype

/-- Source type-J₄, without an assumed recognition implication, simplicity,
plus type, or any global group-order hypothesis. -/
structure IsTypeJ4 (z : G) : Prop where
  involution : orderOf z = 2
  extraspecial : IsExtraspecial 2 (core z)
  core_card : Nat.card (core z) = 2 ^ 13
  cubic_quotient : Nonempty (CubicAutomorphismQuotient ((centralizer z) ⧸ core z))
  fusion : {x : G | IsConj z x ∧ x ∈ ambientCore z} ≠ {z}

omit [Finite G] in
/-- A central element of its own centralizer belongs to its generalized
Fitting subgroup. This also makes the source fusion condition nonvacuous. -/
theorem marker_mem_ambientCore (z : G) : z ∈ ambientCore z := by
  have hzC : z ∈ centralizer z := mem_centralizer_singleton_iff.mpr rfl
  have hzZ : (⟨z, hzC⟩ : centralizer z) ∈ center (centralizer z) := by
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (mem_centralizer_singleton_iff.mp c.property)
  have hZ : center (centralizer z) ≤ fittingSubgroup (centralizer z) :=
    le_sSup ⟨inferInstance, inferInstance⟩
  exact mem_map.mpr ⟨⟨z, hzC⟩,
    fitting_le_generalizedFitting _ (hZ hzZ), rfl⟩

omit [Finite G] in
/-- The set inequality used by Aschbacher–Segev is exactly a nontrivial
returning ambient conjugate. Conjugation is on the left throughout. -/
theorem fusion_iff_exists_conjugator (z : G) :
    {x : G | IsConj z x ∧ x ∈ ambientCore z} ≠ {z} ↔
      ∃ g : G, g * z * g⁻¹ ∈ ambientCore z ∧ g * z * g⁻¹ ≠ z := by
  constructor
  · intro h
    by_contra hn
    apply h
    ext x
    constructor
    · rintro ⟨hx, hxQ⟩
      obtain ⟨g, rfl⟩ := isConj_iff.mp hx
      exact Set.mem_singleton_iff.mpr (by
        by_contra hne
        exact hn ⟨g, hxQ, hne⟩)
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact ⟨IsConj.refl z, marker_mem_ambientCore z⟩
  · rintro ⟨g, hg, hne⟩ he
    have hm : g * z * g⁻¹ ∈ ({z} : Set G) := by
      rw [← he]
      exact ⟨isConj_iff.mpr ⟨g, rfl⟩, hg⟩
    exact hne (Set.mem_singleton_iff.mp hm)

/-- Extraspeciality identifies the intrinsic generalized Fitting subgroup
with the intrinsic two-core; no extra characteristic-two assumption is needed. -/
theorem IsTypeJ4.core_eq_twoCore {z : G} (h : IsTypeJ4 z) :
    core z = pCore 2 (centralizer z) := by
  let := h.extraspecial
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, IsExtraspecial.isPGroup 2 (core z)⟩
  · exact (pCore_le_fitting _ 2).trans (fitting_le_generalizedFitting _)

/-- The returning element and conjugator are both in the original ambient
group, whereas the core membership is retained inside its actual centralizer. -/
theorem IsTypeJ4.exists_returning_conjugate {z : G} (h : IsTypeJ4 z) :
    ∃ g : G, ∃ q : core z, ((q : centralizer z) : G) = g * z * g⁻¹ ∧
      ((q : centralizer z) : G) ≠ z := by
  obtain ⟨g, hg, hne⟩ := (fusion_iff_exists_conjugator z).mp h.fusion
  obtain ⟨q, hq, he⟩ := mem_map.mp hg
  exact ⟨g, ⟨q, hq⟩, he, fun hz => hne (he.symm.trans hz)⟩

end Theory.GroupTheory.Recognition.JankoFour
