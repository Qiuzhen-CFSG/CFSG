module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.SourceBounds
public import Theory.SpecificGroups.PSL3Three.Basic
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.Representation.BinaryIrreducibleCentralizer
public import Theory.GroupTheory.AutomorphismTowerSimple

public import Theory.SpecificGroups.PSL3Three.GraphWitnesses.Thirteen

/-!
# Transporting the PSL₃(3) graph witnesses to the original source action

A marked isomorphism from the actual generalized Fitting subgroup transports
conjugation to the native PSL₃(3) model. Binary irreducibility makes this action
faithful on each elementary two-subgroup, so its order and rank are preserved.
When the component center is trivial, an ambient involution acting inner lies
in that component: its inner representative differs from it by a centralizing
involution, which binary Schur's lemma kills.

The native inverter and fixed-centralizer witnesses therefore lift to elements
of the original G, preserving every order, conjugation and commutator equation.
The final theorem has exactly the two witness conclusions consumed by
`TwelveFixedSpaces.source_bounds_of_local_calculations`.

This is conditional assembly. The centerless-cover premise must be discharged
by the existing SL₃ projection-universality owner; it is not an assumption of
the source theorem. Outer-involution conjugacy and the elementary-eight
centralizer calculation also remain explicit. In the latter, the outer
involution may be reselected, as required for the normal eight-subgroup of
C₂ × S₄. No faithfulness of conjugation on all of G is assumed.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.2,
manuscript p.10, the PSL₃(3) case.
-/

public section

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.TwelveFixedSpaces.GraphWitnesses
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative

variable {G V S : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [Group S]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)

private abbrev L := generalizedFitting G

private def modelAction (e : L (G := G) ≃* S) : G →* MulAut S :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

private theorem modelAction_apply (e : L (G := G) ≃* S) (g : G) (l : L (G := G)) :
    modelAction e g (e l) = e (MulAut.conjNormal g l) := by
  change e (MulAut.conjNormal g (e.symm (e l))) = _
  rw [e.symm_apply_apply]

private theorem modelAction_on_L (e : L (G := G) ≃* S) (l : L (G := G)) :
    modelAction e (l : G) = MulAut.conj (e l) := by
  change MulAut.congr e (MulAut.conjNormal (l : G)) = _
  rw [MulAut.conjNormal_val, MulAut.congr_conj]

include h in
private theorem modelAction_elementary_injective (e : L (G := G) ≃* S)
    (A : Subgroup G) (hA : IsElementaryTwo A) :
    Function.Injective ((modelAction e).comp A.subtype) := by
  let : IsIrreducible (ρ.comp (L (G := G)).subtype) := h.irreducible
  let : IsElementaryAbelian 2 A := hA.2
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro a ha
  apply Subtype.ext
  apply BinaryIrreducibleCentralizer.centralizing_square_one_eq_one ρ (L (G := G)) h.faithful
  · exact elemPow_eq_one_of_isElementaryAbelian (a : G) a.property
  · have he : MulAut.conjNormal (a : G) = (1 : MulAut (L (G := G))) := by
      apply (MulAut.congr e).injective
      exact ha.trans (map_one (MulAut.congr e)).symm
    rw [← MulAut.conjNormal_ker_eq_centralizer]
    exact he

include h in
private theorem mem_L_of_inner (e : L (G := G) ≃* S)
    (hcenter : center (L (G := G)) = ⊥) (t : G) (ht : t ^ 2 = 1)
    (hi : modelAction e t ∈ MulAut.innerSubgroup S) : t ∈ L (G := G) := by
  let : IsIrreducible (ρ.comp (L (G := G)).subtype) := h.irreducible
  obtain ⟨s, hs⟩ := hi
  let l := e.symm s
  have he : MulAut.conjNormal t = MulAut.conj l := by
    apply (MulAut.congr e).injective
    rw [MulAut.congr_conj, e.apply_symm_apply]
    exact hs.symm
  have hl2 : l ^ 2 = 1 := by
    apply MulAut.conj_injective_of_center_eq_bot hcenter
    rw [map_pow, ← he, ← map_pow, ht, map_one, map_one]
  have htl : Commute t (l : G) := by
    have hx := congrArg (fun a : MulAut (L (G := G)) => (a l : G)) he
    change t * (l : G) * t⁻¹ = (l : G) * l * (l : G)⁻¹ at hx
    simp only [mul_inv_cancel_right] at hx
    exact mul_inv_eq_iff_eq_mul.mp hx
  have hk2 : ((l : G)⁻¹ * t) ^ 2 = 1 := by
    rw [htl.symm.inv_left.mul_pow, inv_pow, ht]
    have hl2' : (l : G) ^ 2 = 1 := congrArg Subtype.val hl2
    rw [hl2', inv_one, one_mul]
  have hkc : (l : G)⁻¹ * t ∈ centralizer (L (G := G) : Set G) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer]
    change MulAut.conjNormal ((l : G)⁻¹ * t) = (1 : MulAut (L (G := G)))
    rw [map_mul, map_inv, MulAut.conjNormal_val, he, inv_mul_cancel]
  have hk := BinaryIrreducibleCentralizer.centralizing_square_one_eq_one
    ρ (L (G := G)) h.faithful hk2 hkc
  have hte : t = (l : G) := (inv_mul_eq_one.mp hk).symm
  exact hte ▸ l.property

omit [Finite G] in
private theorem exists_sourceModelEquiv
    (hm : ClassicalGroup.IsPSL ((L (G := G)) ⧸ center (L (G := G))) 3 3)
    (hcenter : center (L (G := G)) = ⊥) :
    Nonempty (L (G := G) ≃* Matrix.PSL3Three.PSL) := by
  obtain ⟨F, hF, hfin, hc, ⟨f⟩⟩ := hm
  let := Fintype.ofFinite F
  let eF : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hc)
  let q := QuotientGroup.mk' (center (L (G := G)))
  have hq : Function.Bijective q := by
    refine ⟨?_, QuotientGroup.mk'_surjective _⟩
    rw [← MonoidHom.ker_eq_bot_iff]
    simpa only [q, QuotientGroup.ker_mk'] using hcenter
  exact ⟨(MulEquiv.ofBijective q hq).trans (f.trans (Atlas.fieldEquivPSL 3 eF))⟩

include h in
/-- Conditional ambient transport of outer inversion. The covering premise and
native inversion calculation are separate mathematical inputs. -/
theorem outer_witness_of_centerless_model_calculation
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 3)
    (hcenter : center (generalizedFitting G) = ⊥)
    (hinv : ∀ b : MulAut Matrix.PSL3Three.PSL, orderOf b = 2 →
      b ∉ MulAut.innerSubgroup Matrix.PSL3Three.PSL →
      ∃ x : Matrix.PSL3Three.PSL, orderOf x = 13 ∧ b x = x⁻¹)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hout : ¬ A ≤ generalizedFitting G) :
    ∃ t ∈ A, ∃ x : G, orderOf x = 13 ∧ t * x * t⁻¹ = x⁻¹ := by
  classical
  let e := Classical.choice (exists_sourceModelEquiv hm hcenter)
  let f := modelAction e
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨t, htA, htL⟩ := SetLike.not_le_iff_exists.mp hout
  have ht2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) t htA
  have houter : f t ∉ MulAut.innerSubgroup Matrix.PSL3Three.PSL :=
    fun hi => htL (mem_L_of_inner ρ h e hcenter t ht2 hi)
  have hb2 : orderOf (f t) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ht2, map_one]
    · intro he
      exact houter (he ▸ (MulAut.innerSubgroup _).one_mem)
  obtain ⟨x, hx, htx⟩ := hinv (f t) hb2 houter
  let y := e.symm x
  have hxy : orderOf (y : G) = 13 := by
    rw [Subgroup.orderOf_coe, ← e.orderOf_eq y, e.apply_symm_apply]
    exact hx
  have he : MulAut.conjNormal t y = y⁻¹ := by
    apply e.injective
    rw [← modelAction_apply, map_inv, e.apply_symm_apply]
    exact htx
  exact ⟨t, htA, y, hxy, congrArg Subtype.val he⟩

include h in
/-- Conditional ambient transport of the reselected rank-three graph witness.
The order-three commutator is formed in the original G, with its second entry
lifted into the actual generalized Fitting subgroup. -/
theorem three_witness_of_centerless_model_calculations
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 3)
    (hcenter : center (generalizedFitting G) = ⊥)
    (hinv : ∀ b : MulAut Matrix.PSL3Three.PSL, orderOf b = 2 →
      b ∉ MulAut.innerSubgroup Matrix.PSL3Three.PSL →
      ∃ x : Matrix.PSL3Three.PSL, orderOf x = 13 ∧ b x = x⁻¹)
    (height : ∀ B : Subgroup (MulAut Matrix.PSL3Three.PSL),
      IsElementaryAbelian 2 B → Nat.card B = 8 →
      ∃ b ∈ B, b ∉ MulAut.innerSubgroup Matrix.PSL3Three.PSL ∧
        ∃ a ∈ B, ∃ c : Matrix.PSL3Three.PSL,
          b c = c ∧ orderOf (a c * c⁻¹) = 3)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hr : rank A = 3) :
    ∃ t ∈ A, orderOf t = 2 ∧ ∃ x a c : G, a ∈ A ∧ orderOf x = 13 ∧
      t * x * t⁻¹ = x⁻¹ ∧ Commute t a ∧ Commute t c ∧
        orderOf (a * c * a⁻¹ * c⁻¹) = 3 := by
  classical
  let e := Classical.choice (exists_sourceModelEquiv hm hcenter)
  let f := (modelAction e).comp A.subtype
  have hf : Function.Injective f := modelAction_elementary_injective ρ h e A hA
  let B := f.range
  let : IsElementaryAbelian 2 A := hA.2
  have hB : IsElementaryAbelian 2 B :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hcard : Nat.card B = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
      hA.card_eq_two_pow_rank, hr]
    rfl
  obtain ⟨b, hb, hbout, a, ha, c, hbc, hac⟩ := height B hB hcard
  obtain ⟨t, rfl⟩ := hb
  obtain ⟨a, rfl⟩ := ha
  have ht2 : (t : G) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (t : G) t.property
  have ht1 : (t : G) ≠ 1 := by
    intro he
    apply hbout
    change modelAction e (t : G) ∈ MulAut.innerSubgroup _
    rw [he, map_one]
    exact one_mem _
  have ht : orderOf (t : G) = 2 := orderOf_eq_prime ht2 ht1
  have hft : orderOf (f t) = 2 := by
    rw [orderOf_injective f hf, ← Subgroup.orderOf_coe]
    exact ht
  obtain ⟨x, hx, htx⟩ := hinv (f t) hft hbout
  let y := e.symm x
  let z := e.symm c
  have hy : orderOf (y : G) = 13 := by
    rw [Subgroup.orderOf_coe, ← e.orderOf_eq y, e.apply_symm_apply]
    exact hx
  have hty : (t : G) * (y : G) * (t : G)⁻¹ = (y : G)⁻¹ := by
    have he : MulAut.conjNormal (t : G) y = y⁻¹ := by
      apply e.injective
      rw [← modelAction_apply, map_inv, e.apply_symm_apply]
      exact htx
    exact congrArg Subtype.val he
  have htz : Commute (t : G) (z : G) := by
    have he : MulAut.conjNormal (t : G) z = z := by
      apply e.injective
      rw [← modelAction_apply, e.apply_symm_apply]
      exact hbc
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)
  have hta : Commute (t : G) (a : G) :=
    congrArg Subtype.val (mul_comm t a)
  let w : L (G := G) := MulAut.conjNormal (a : G) z * z⁻¹
  have hw : e w = f a c * c⁻¹ := by
    rw [map_mul, map_inv, ← modelAction_apply, e.apply_symm_apply]
    rfl
  have hw3 : orderOf (w : G) = 3 := by
    rw [Subgroup.orderOf_coe, ← e.orderOf_eq w, hw]
    exact hac
  exact ⟨t, t.property, ht, y, a, z, a.property, hy, hty, hta, htz, hw3⟩

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.TwelveFixedSpaces.GraphWitnesses

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.TwelveFixedSpaces.GraphWitnesses
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

/-- Both literal ambient witness premises of the degree-twelve fixed-space
argument, conditional on the central-cover and two native graph calculations.
The rank-three calculation may select a different outer involution for each A. -/
theorem source_witnesses_of_centerless_graph_calculations
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 3)
    (hcenter : center (generalizedFitting G) = ⊥)
    (hconj : ∀ b : MulAut Matrix.PSL3Three.PSL, orderOf b = 2 →
      b ∉ MulAut.innerSubgroup Matrix.PSL3Three.PSL →
      ∃ u : MulAut Matrix.PSL3Three.PSL,
        b = u * Matrix.PSL3.OuterSolvable.graph (ZMod 3) * u⁻¹)
    (height : ∀ B : Subgroup (MulAut Matrix.PSL3Three.PSL),
      IsElementaryAbelian 2 B → Nat.card B = 8 →
      ∃ b ∈ B, b ∉ MulAut.innerSubgroup Matrix.PSL3Three.PSL ∧
        ∃ a ∈ B, ∃ c : Matrix.PSL3Three.PSL,
          b c = c ∧ orderOf (a c * c⁻¹) = 3) :
    (∀ A : Subgroup G, IsElementaryTwo A → ¬ A ≤ generalizedFitting G →
      rank A = 2 → ∃ t ∈ A, ∃ x : G, orderOf x = 13 ∧ t * x * t⁻¹ = x⁻¹) ∧
    (∀ A : Subgroup G, IsElementaryTwo A → rank A = 3 →
      ∃ t ∈ A, orderOf t = 2 ∧ ∃ x a c : G, a ∈ A ∧ orderOf x = 13 ∧
        t * x * t⁻¹ = x⁻¹ ∧ Commute t a ∧ Commute t c ∧
          orderOf (a * c * a⁻¹ * c⁻¹) = 3) := by
  have hinv (b : MulAut Matrix.PSL3Three.PSL) (hb : orderOf b = 2)
      (hout : b ∉ MulAut.innerSubgroup Matrix.PSL3Three.PSL) :=
    Matrix.PSL3Three.GraphWitnesses.inverts_thirteen_of_graph_conjugate b
      (hconj b hb hout)
  constructor
  · intro A hA hout _
    exact outer_witness_of_centerless_model_calculation ρ h hm hcenter hinv A hA hout
  · exact three_witness_of_centerless_model_calculations ρ h hm hcenter hinv height

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.TwelveFixedSpaces.GraphWitnesses
