module

public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.SylowChoice.Centers
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Transvections
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The Ru2 center lies in the Ru1 natural subgroup

The center-order calculation from Ru1 makes U elementary abelian before
any compatible Sylow choice. The nontrivial Q-action has fixed subgroup Z;
central binary commutator duality therefore realizes every shear U → Z.
A nonzero character of U/Z killing the image of V is realized by q ∈ C_Q(V).
Thus q ∈ S, and U ≤ S implies its commutator image Z lies in [S,S] = V.

This supplies the containment needed to choose the Sylow subgroup inside
C_G(Z), preserving the literal Ru2 groups and maps.

Source: Aschbacher–Smith, J.1–J.2, pp.431–432; the duality is F.9.7, p.321.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ
open Subgroup Representation
open scoped commutatorElement IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem conjugate_mem_centralizer {A : Subgroup G} {h c : G}
    (hn : h ∈ normalizer A) (hc : c ∈ centralizer (A : Set G)) :
    h * c * h⁻¹ ∈ centralizer (A : Set G) := by
  intro a ha
  have hb : h⁻¹ * a * h ∈ A := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp ((normalizer (A : Set G)).inv_mem hn) a).mp ha
  simpa [mul_assoc] using congrArg (fun x : G => h * x * h⁻¹) (hc _ hb)

/-- The two special cores cannot coincide: their center would then be H-invariant. -/
theorem TypeRuSetup.Q_ne_S (d : TypeRuSetup G) : d.Q ≠ d.S := by
  intro he
  have hn : d.H ≤ normalizer d.V := by
    apply le_normalizer_iff.mpr
    intro h hh v hv
    rw [← d.ru1.centralizer_S] at hv ⊢
    apply conjugate_mem_centralizer _ hv
    change h ∈ normalizer (d.S : Set G)
    rw [← he]
    exact d.ru2.six.normalized hh
  have hUV : d.U ≤ d.V := by
    apply iSup_le
    intro h
    apply map_le_iff_le_comap.mpr
    intro v hv
    exact (mem_normalizer_iff.mp (hn h.property) v).mp hv
  have hc := card_le_of_le hUV
  rw [d.ru2.card_U d.card_Z, d.ru1.card_V] at hc
  omega

/-- Q acts nontrivially on U. -/
theorem TypeRuSetup.not_U_le_centralizer_Q (d : TypeRuSetup G) :
    ¬ d.U ≤ centralizer (d.Q : Set G) := by
  intro hc
  have hQS : d.Q ≤ d.S := by
    change d.Q ≤ d.L.pCoreIn 2
    rw [← d.ru1.centralizer_V]
    exact (le_centralizer_iff.mp hc).trans (centralizer_le (le_conjugateSpan _ _))
  apply d.Q_ne_S
  apply Subgroup.eq_of_le_of_card_ge hQS
  rw [d.ru2.card_Q d.card_Z, d.ru1.card_S]

/-- Irreducibility on U/Z and the nontrivial Q-action determine its fixed subgroup. -/
theorem TypeRuSetup.centralizer_Q_inf_U (d : TypeRuSetup G) :
    d.U ⊓ centralizer (d.Q : Set G) = d.Z := by
  have hZQ : d.Z ≤ centralizer (d.Q : Set G) :=
    le_centralizer_iff.mpr (pCoreIn_le 2 d.H)
  apply le_antisymm
  · intro u hu
    by_contra hun
    have hcoord : (d.ru2.natural.coordinates ⟨u, hu.1⟩).toAdd ≠ 0 := by
      exact fun he => hun ((d.ru2.natural.coordinates_eq_one_iff _).mp he)
    apply d.not_U_le_centralizer_Q
    intro v hv
    by_cases hvZ : v ∈ d.Z
    · exact hZQ hvZ
    have hvcoord : (d.ru2.natural.coordinates ⟨v, hv⟩).toAdd ≠ 0 := by
      exact fun he => hvZ ((d.ru2.natural.coordinates_eq_one_iff _).mp he)
    obtain ⟨h, hh⟩ := d.ru2.transitive_natural _ _ hcoord hvcoord
    let a : d.U := ⟨h * u * (h : G)⁻¹,
      (mem_normalizer_iff.mp (d.ru2.natural.normalized h.property) u).mp hu.1⟩
    have ha : (a : G) ∈ centralizer (d.Q : Set G) :=
      conjugate_mem_centralizer (d.ru2.six.normalized h.property) hu.2
    have he : d.ru2.natural.coordinates a = d.ru2.natural.coordinates ⟨v, hv⟩ :=
      Multiplicative.toAdd.injective ((d.ru2.natural.equivariant h ⟨u, hu.1⟩).trans hh)
    have hc : ((a⁻¹ * (⟨v, hv⟩ : d.U) : d.U) : G) ∈
        d.Z := by
      apply (d.ru2.natural.coordinates_eq_one_iff _).mp
      rw [map_mul, map_inv, he, inv_mul_cancel]
    have hp := (centralizer (d.Q : Set G)).mul_mem ha (hZQ hc)
    simpa only [coe_mul, coe_inv, mul_inv_cancel_left] using hp
  · exact le_inf d.ru2.natural.kernel_le hZQ


/-- J.2.2(4): every binary shear with center Z is induced by an element of Q.
A homomorphism U → Z that kills Z specifies exactly such a shear by
u ↦ f(u)u. The reverse containment follows from `commutator_Q_U_le_Z`.
The proof applies F.9.7 to the actual subgroups inside H. -/
theorem TypeRuSetup.full_transvection_action (d : TypeRuSetup G)
    (f : d.U →* d.Z)
    (hf : ∀ z : d.Z,
      f ⟨z, d.ru2.natural.kernel_le z.property⟩ = 1) :
    ∃ q : d.Q, ∀ u : d.U,
      (q : G) * u * (q : G)⁻¹ = (f u : G) * u := by
  let QH := d.Q.subgroupOf d.H
  let UH := d.U.subgroupOf d.H
  let ZH := d.Z.subgroupOf d.H
  have hUH := d.ru2.natural.section_le
  have hQH := pCoreIn_le 2 d.H
  have hZH := d.ru2.natural.kernel_le.trans hUH
  let : QH.Normal :=
    (normal_subgroupOf_iff_le_normalizer hQH).mpr d.ru2.six.normalized
  let : UH.Normal :=
    (normal_subgroupOf_iff_le_normalizer hUH).mpr d.ru2.natural.normalized
  let : IsElementaryAbelian 2 d.U := d.elementary_U
  let : IsElementaryAbelian 2 UH := IsElementaryAbelian.subgroupOf hUH
  have hZQ : ZH ≤ QH := fun z hz => d.ru2.six.kernel_le (d.ru2.natural.kernel_le hz)
  have hZcentral : ZH ≤ center d.H := by
    intro z hz
    apply mem_center_iff.mpr
    intro h
    exact Subtype.ext ((h.property z hz).symm)
  have hcomm : ⁅QH, UH⁆ ≤ ZH := by
    apply commutator_le.mpr
    intro q hq u hu
    exact d.commutator_Q_U_le_Z (commutator_mem_commutator hq hu)
  have hcard : Nat.card ZH = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZH).toEquiv]
    exact d.card_Z
  obtain ⟨eZ, e, he, _⟩ := ChapterF.lemma_F_9_7 QH UH ZH hZQ hZcentral hcomm hcard
  let eU : UH ≃* d.U := subgroupOfEquivOfLe hUH
  let eQ : QH ≃* d.Q := subgroupOfEquivOfLe hQH
  let eZ₀ : ZH ≃* d.Z := subgroupOfEquivOfLe hZH
  let fH : UH →* Multiplicative (ZMod 2) :=
    eZ.toMonoidHom.comp (eZ₀.symm.toMonoidHom.comp (f.comp eU.toMonoidHom))
  let N := (centralizer (QH : Set d.H)).subgroupOf UH
  have hN : N ≤ fH.ker := by
    intro u hu
    have huZ : ((u : d.H) : G) ∈ d.Z := by
      rw [← d.centralizer_Q_inf_U]
      refine ⟨u.property, ?_⟩
      intro q hq
      exact congrArg Subtype.val (hu ⟨q, hQH hq⟩ hq)
    have hh := hf ⟨_, huZ⟩
    change fH u = 1
    change eZ (eZ₀.symm (f (eU u))) = 1
    rw [show f (eU u) = 1 from hh, map_one, map_one]
  let k := QuotientGroup.lift N fH hN
  obtain ⟨qbar, hqbar⟩ := e.surjective (MonoidHom.binaryCharacterEquivLinearDual k)
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective _ qbar
  refine ⟨eQ q, ?_⟩
  intro u
  let uH := eU.symm u
  have hpair := he q uH
  rw [hqbar] at hpair
  have heq : fH uH = eZ ⟨⁅(q : d.H), (uH : d.H)⁆,
      hcomm (commutator_mem_commutator q.property uH.property)⟩ :=
    Multiplicative.toAdd.injective hpair
  have hh := congrArg (fun z : ZH => ((z : d.H) : G)) (eZ.injective heq)
  change (f u : G) = ⁅(eQ q : G), (u : G)⁆ at hh
  rw [hh, commutatorElement_def]
  group


/-- U lies in the centralizer S of its subgroup V, before making the Sylow choice. -/
theorem TypeRuSetup.U_le_S (d : TypeRuSetup G) : d.U ≤ d.S := by
  let : IsElementaryAbelian 2 d.U := d.elementary_U
  change d.U ≤ d.L.pCoreIn 2
  rw [← d.ru1.centralizer_V]
  intro u hu v hv
  exact congrArg Subtype.val
    (mul_comm (⟨v, le_conjugateSpan d.H d.V hv⟩ : d.U) ⟨u, hu⟩)


/-- The center of the original Ru2 Sylow already lies in V. -/
theorem TypeRuSetup.Z_le_V (d : TypeRuSetup G) : d.Z ≤ d.V := by
  let hVU := le_conjugateSpan d.H d.V
  let k : d.V →* Multiplicative FourSpace :=
    d.ru2.natural.coordinates.comp (Subgroup.inclusion hVU)
  let A : Submodule (ZMod 2) FourSpace :=
    AddSubgroup.toZModSubmodule 2 k.toAdditiveLeft.range
  have hA : A < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro ht
    have hs : Function.Surjective k := by
      intro x
      have hx : x.toAdd ∈ A := by rw [ht]; trivial
      exact hx
    have hc := Nat.card_le_card_of_surjective k hs
    have hfour : Nat.card (Multiplicative FourSpace) = 16 := by
      change Nat.card FourSpace = 16
      rw [Nat.card_eq_fintype_card]
      exact SL2FourNatural.card_vector
    rw [hfour, d.ru1.card_V] at hc
    omega
  obtain ⟨f₀, hf₀, hAf₀⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hA inferInstance
  let eZ : d.Z ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq d.card_Z (by simp)
  let f : d.U →* d.Z := eZ.symm.toMonoidHom.comp
    (f₀.toAddMonoidHom.toMultiplicative.comp d.ru2.natural.coordinates)
  have hfZ (z : d.Z) : f ⟨z, d.ru2.natural.kernel_le z.property⟩ = 1 := by
    have hz := (d.ru2.natural.coordinates_eq_one_iff
      ⟨z, d.ru2.natural.kernel_le z.property⟩).mpr z.property
    change eZ.symm (Multiplicative.ofAdd (f₀ _)) = 1
    rw [hz]
    simp
  have hfV (v : d.V) : f ⟨v, hVU v.property⟩ = 1 := by
    have hx : (k v).toAdd ∈ A := ⟨Additive.ofMul v, rfl⟩
    have hy : f₀ (k v).toAdd ∈ A.map f₀ := ⟨_, hx, rfl⟩
    rw [hAf₀, Submodule.mem_bot] at hy
    change eZ.symm (Multiplicative.ofAdd (f₀ (k v).toAdd)) = 1
    rw [hy]
    exact eZ.symm.map_one
  have hfs : Function.Surjective f := by
    intro z
    obtain ⟨x, hx⟩ := (LinearMap.surjective_iff_ne_zero.mpr hf₀) (eZ z).toAdd
    obtain ⟨u, hu⟩ := d.ru2.natural.onto (Multiplicative.ofAdd x)
    refine ⟨u, ?_⟩
    change eZ.symm (Multiplicative.ofAdd (f₀ (d.ru2.natural.coordinates u).toAdd)) = z
    rw [hu]
    change eZ.symm (Multiplicative.ofAdd (f₀ x)) = z
    rw [hx]
    exact eZ.symm_apply_apply z
  obtain ⟨q, hq⟩ := d.full_transvection_action f hfZ
  have hqS : (q : G) ∈ d.S := by
    change (q : G) ∈ d.L.pCoreIn 2
    rw [← d.ru1.centralizer_V]
    intro v hv
    have he := hq ⟨v, hVU hv⟩
    rw [hfV ⟨v, hv⟩] at he
    simp only [coe_one, one_mul] at he
    have hh := congrArg (fun x : G => x * q) he
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh.symm
  intro z hz
  obtain ⟨u, hu⟩ := hfs ⟨z, hz⟩
  have hcomm : ⁅(q : G), (u : G)⁆ ∈ d.V := by
    rw [← d.ru1.derived_eq]
    exact mem_map.mpr ⟨⁅(⟨q, hqS⟩ : d.S), (⟨u, d.U_le_S u.property⟩ : d.S)⁆,
      commutator_mem_commutator (mem_top _) (mem_top _), rfl⟩
  have he : ⁅(q : G), (u : G)⁆ = z := by
    rw [commutatorElement_def, hq, hu]
    simp
  rwa [he] at hcomm

end CFSG.Quasithin.ChapterJ
