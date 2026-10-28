module

public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Center
public import CFSG.Quasithin.ChapterF.Section09
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The full transvection action and parabolic overlap in J.2.2

The Ru2 coordinate action gives [Q,U] ≤ Z. If Q centralized U, its
order and C_G(V) = S would give Q = S; normality of Q would then make
V = Z(S) invariant under H, contradicting |U| = 32 and |V| = 8.
Transitivity on the nonzero vectors of U/Z therefore gives C_U(Q) = Z.
Applying F.9.7 inside H, with the actual relative normal subgroups and
quotient maps, realizes every homomorphism U → Z vanishing on Z by
conjugation in Q. Conversely every Q-action has this form. This proves
exact equality with the full group of transvections of center Z.

Faithfulness of the given S₅ action gives HC ≤ Q, and elementary
abelianness gives U ≤ HC. The Sylow supplement to the two-residual
identifies the overlap H ∩ L both as a join and as the product L₁T.
The two cores Q and S lie in that overlap and in its two-core. The
reverse core inclusion and the natural Q/HC identification are separate
obligations; no J.2.2 conclusion is added to the Ru hypotheses here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(1,4), printed p.432 (PDF p.443), using F.9.7 on printed p.321.
The printed U/HC in the J.2.2 proof is Q/HC.
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

/-- The literal U/Z action factors through H/Q, so its Q-commutators lie in Z. -/
theorem TypeRuSetup.commutator_Q_U_le_Z (d : TypeRuSetup G) : ⁅d.Q, d.U⁆ ≤ d.Z := by
  apply commutator_le.mpr
  intro q hq u hu
  have hqH := pCoreIn_le 2 d.H hq
  have hqker : d.ru2.quotientMap ⟨q, hqH⟩ = 1 := by
    change (⟨q, hqH⟩ : d.H) ∈ d.ru2.quotientMap.ker
    rw [d.ru2.quotient_kernel]
    exact hq
  let a : d.U := ⟨q * u * q⁻¹,
    (mem_normalizer_iff.mp (d.ru2.natural.normalized hqH) u).mp hu⟩
  have he : d.ru2.natural.coordinates a = d.ru2.natural.coordinates ⟨u, hu⟩ := by
    apply Multiplicative.toAdd.injective
    have hh := d.ru2.natural.equivariant ⟨q, hqH⟩ ⟨u, hu⟩
    simpa only [MonoidHom.comp_apply, hqker, map_one, Module.End.one_apply] using hh
  have hk : (a * (⟨u, hu⟩ : d.U)⁻¹ : d.U) ∈ d.ru2.natural.coordinates.ker := by
    change d.ru2.natural.coordinates (a * (⟨u, hu⟩ : d.U)⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  rw [d.ru2.natural.kernel_eq] at hk
  exact hk

/-- The two special cores cannot coincide: their center would then be H-invariant. -/
theorem LocalSetup.Q_ne_S (d : LocalSetup G) : d.toTypeRuSetup.Q ≠ d.toTypeRuSetup.S := by
  intro he
  have hn : d.toTypeRuSetup.H ≤ normalizer d.V := by
    apply le_normalizer_iff.mpr
    intro h hh v hv
    rw [← d.ru1.centralizer_S] at hv ⊢
    apply conjugate_mem_centralizer _ hv
    change h ∈ normalizer (d.toTypeRuSetup.S : Set G)
    rw [← he]
    exact d.ru2.six.normalized hh
  have hUV : d.toTypeRuSetup.U ≤ d.V := by
    apply iSup_le
    intro h
    apply map_le_iff_le_comap.mpr
    intro v hv
    exact (mem_normalizer_iff.mp (hn h.property) v).mp hv
  have hc := card_le_of_le hUV
  rw [d.ru2.card_U d.card_Z, d.ru1.card_V] at hc
  omega

/-- Q acts nontrivially on U. -/
theorem LocalSetup.not_U_le_centralizer_Q (d : LocalSetup G) :
    ¬ d.toTypeRuSetup.U ≤ centralizer (d.toTypeRuSetup.Q : Set G) := by
  intro hc
  have hQS : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.S := by
    change d.toTypeRuSetup.Q ≤ d.L.pCoreIn 2
    rw [← d.ru1.centralizer_V]
    exact (le_centralizer_iff.mp hc).trans (centralizer_le (le_conjugateSpan _ _))
  apply d.Q_ne_S
  apply Subgroup.eq_of_le_of_card_ge hQS
  rw [d.ru2.card_Q d.card_Z, d.ru1.card_S]

/-- Irreducibility on U/Z and the nontrivial Q-action determine its fixed subgroup. -/
theorem LocalSetup.centralizer_Q_inf_U (d : LocalSetup G) :
    d.toTypeRuSetup.U ⊓ centralizer (d.toTypeRuSetup.Q : Set G) = d.toTypeRuSetup.Z := by
  have hZQ : d.toTypeRuSetup.Z ≤ centralizer (d.toTypeRuSetup.Q : Set G) :=
    le_centralizer_iff.mpr (pCoreIn_le 2 d.toTypeRuSetup.H)
  apply le_antisymm
  · intro u hu
    by_contra hun
    have hcoord : (d.ru2.natural.coordinates ⟨u, hu.1⟩).toAdd ≠ 0 := by
      exact fun he => hun ((d.ru2.natural.coordinates_eq_one_iff _).mp he)
    apply d.not_U_le_centralizer_Q
    intro v hv
    by_cases hvZ : v ∈ d.toTypeRuSetup.Z
    · exact hZQ hvZ
    have hvcoord : (d.ru2.natural.coordinates ⟨v, hv⟩).toAdd ≠ 0 := by
      exact fun he => hvZ ((d.ru2.natural.coordinates_eq_one_iff _).mp he)
    obtain ⟨h, hh⟩ := d.ru2.transitive_natural _ _ hcoord hvcoord
    let a : d.toTypeRuSetup.U := ⟨h * u * (h : G)⁻¹,
      (mem_normalizer_iff.mp (d.ru2.natural.normalized h.property) u).mp hu.1⟩
    have ha : (a : G) ∈ centralizer (d.toTypeRuSetup.Q : Set G) :=
      conjugate_mem_centralizer (d.ru2.six.normalized h.property) hu.2
    have he : d.ru2.natural.coordinates a = d.ru2.natural.coordinates ⟨v, hv⟩ :=
      Multiplicative.toAdd.injective ((d.ru2.natural.equivariant h ⟨u, hu.1⟩).trans hh)
    have hc : ((a⁻¹ * (⟨v, hv⟩ : d.toTypeRuSetup.U) : d.toTypeRuSetup.U) : G) ∈
        d.toTypeRuSetup.Z := by
      apply (d.ru2.natural.coordinates_eq_one_iff _).mp
      rw [map_mul, map_inv, he, inv_mul_cancel]
    have hp := (centralizer (d.toTypeRuSetup.Q : Set G)).mul_mem ha (hZQ hc)
    simpa only [coe_mul, coe_inv, mul_inv_cancel_left] using hp
  · exact le_inf d.ru2.natural.kernel_le hZQ


/-- J.2.2(4): every binary shear with center Z is induced by an element of Q.
A homomorphism U → Z that kills Z specifies exactly such a shear by
u ↦ f(u)u. The reverse containment follows from `commutator_Q_U_le_Z`.
The proof applies F.9.7 to the actual subgroups inside H. -/
theorem LocalSetup.full_transvection_action (d : LocalSetup G)
    (f : d.toTypeRuSetup.U →* d.toTypeRuSetup.Z)
    (hf : ∀ z : d.toTypeRuSetup.Z,
      f ⟨z, d.ru2.natural.kernel_le z.property⟩ = 1) :
    ∃ q : d.toTypeRuSetup.Q, ∀ u : d.toTypeRuSetup.U,
      (q : G) * u * (q : G)⁻¹ = (f u : G) * u := by
  let QH := d.toTypeRuSetup.Q.subgroupOf d.toTypeRuSetup.H
  let UH := d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.H
  let ZH := d.toTypeRuSetup.Z.subgroupOf d.toTypeRuSetup.H
  have hUH := d.ru2.natural.section_le
  have hQH := pCoreIn_le 2 d.toTypeRuSetup.H
  have hZH := d.ru2.natural.kernel_le.trans hUH
  let : QH.Normal :=
    (normal_subgroupOf_iff_le_normalizer hQH).mpr d.ru2.six.normalized
  let : UH.Normal :=
    (normal_subgroupOf_iff_le_normalizer hUH).mpr d.ru2.natural.normalized
  let : IsElementaryAbelian 2 d.toTypeRuSetup.U := d.elementary_U
  let : IsElementaryAbelian 2 UH := IsElementaryAbelian.subgroupOf hUH
  have hZQ : ZH ≤ QH := fun z hz => d.ru2.six.kernel_le (d.ru2.natural.kernel_le hz)
  have hZcentral : ZH ≤ center d.toTypeRuSetup.H := by
    intro z hz
    apply mem_center_iff.mpr
    intro h
    exact Subtype.ext ((h.property z hz).symm)
  have hcomm : ⁅QH, UH⁆ ≤ ZH := by
    apply commutator_le.mpr
    intro q hq u hu
    exact d.toTypeRuSetup.commutator_Q_U_le_Z (commutator_mem_commutator hq hu)
  have hcard : Nat.card ZH = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZH).toEquiv]
    exact d.card_Z
  obtain ⟨eZ, e, he, _⟩ := ChapterF.lemma_F_9_7 QH UH ZH hZQ hZcentral hcomm hcard
  let eU : UH ≃* d.toTypeRuSetup.U := subgroupOfEquivOfLe hUH
  let eQ : QH ≃* d.toTypeRuSetup.Q := subgroupOfEquivOfLe hQH
  let eZ₀ : ZH ≃* d.toTypeRuSetup.Z := subgroupOfEquivOfLe hZH
  let fH : UH →* Multiplicative (ZMod 2) :=
    eZ.toMonoidHom.comp (eZ₀.symm.toMonoidHom.comp (f.comp eU.toMonoidHom))
  let N := (centralizer (QH : Set d.toTypeRuSetup.H)).subgroupOf UH
  have hN : N ≤ fH.ker := by
    intro u hu
    have huZ : ((u : d.toTypeRuSetup.H) : G) ∈ d.toTypeRuSetup.Z := by
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
  have heq : fH uH = eZ ⟨⁅(q : d.toTypeRuSetup.H), (uH : d.toTypeRuSetup.H)⁆,
      hcomm (commutator_mem_commutator q.property uH.property)⟩ :=
    Multiplicative.toAdd.injective hpair
  have hh := congrArg (fun z : ZH => ((z : d.toTypeRuSetup.H) : G)) (eZ.injective heq)
  change (f u : G) = ⁅(eQ q : G), (u : G)⁆ at hh
  rw [hh, commutatorElement_def]
  group


/-- An S₅ action extending the faithful natural SL₂(4) action is faithful. -/
theorem L2FourAction.injective (r : L2FourAction) : Function.Injective r.action := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  by_contra hn
  have hA := Equiv.Perm.alternatingGroup_le_of_normal
    (by simp : 5 ≤ Nat.card (Fin 5)) ((nontrivial_iff_ne_bot _).mpr hn)
  have ht (g : SL2FourNatural.SL) : g = 1 := by
    apply SL2FourNatural.action_faithful
    apply LinearEquiv.ext
    intro v
    have hh := r.restriction g v
    rw [MonoidHom.mem_ker.mp (hA (r.marking g).property)] at hh
    rw [map_one]
    change SL2FourNatural.action g v = v
    simpa only [Module.End.one_apply] using hh.symm
  have hh := congrArg (fun g : SL2FourNatural.SL => g.val 0 1) (ht (SL2FourNatural.upper 1))
  norm_num [SL2FourNatural.upper] at hh

/-- The full H-centralizer of U lies in Q, so Q/HC is the literal quotient. -/
theorem TypeRuSetup.HC_le_Q (d : TypeRuSetup G) : d.HC ≤ d.Q := by
  intro h hh
  have hr : d.ru2.naturalAction.action (d.ru2.quotientMap ⟨h, hh.1⟩) = 1 := by
    apply LinearMap.ext
    intro v
    obtain ⟨u, hu⟩ := d.ru2.natural.onto (Multiplicative.ofAdd v)
    have he := d.ru2.natural.equivariant ⟨h, hh.1⟩ u
    have hc : h * (u : G) * h⁻¹ = u := by
      rw [← hh.2 u u.property, mul_inv_cancel_right]
    have heq : (⟨h * (u : G) * h⁻¹,
        by rw [hc]; exact u.property⟩ : d.U) = u := Subtype.ext hc
    rw [heq, hu] at he
    exact he.symm
  have hk : (⟨h, hh.1⟩ : d.H) ∈ d.ru2.quotientMap.ker := by
    apply d.ru2.naturalAction.injective
    simpa only [map_one] using hr
  rw [d.ru2.quotient_kernel] at hk
  exact hk

/-- Elementary abelianness puts U in its full H-centralizer. -/
theorem LocalSetup.U_le_HC (d : LocalSetup G) : d.toTypeRuSetup.U ≤ d.toTypeRuSetup.HC := by
  let : IsElementaryAbelian 2 d.toTypeRuSetup.U := d.elementary_U
  refine le_inf d.ru2.natural.section_le ?_
  intro u hu v hv
  exact congrArg Subtype.val (mul_comm (⟨v, hv⟩ : d.toTypeRuSetup.U) ⟨u, hu⟩)

/-- Relative normality of the actual centralizer kernel. -/
theorem TypeRuSetup.HC_normal (d : TypeRuSetup G) : (d.HC.subgroupOf d.H).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
  apply le_normalizer_iff.mpr
  intro h hh c hc
  refine ⟨d.H.mul_mem (d.H.mul_mem hh hc.1) (d.H.inv_mem hh), ?_⟩
  exact conjugate_mem_centralizer (d.ru2.natural.normalized hh) hc.2

/-- The source parabolic overlap is the product of its two-residual and T. -/
theorem LocalSetup.H_inf_L (d : LocalSetup G) :
    d.toTypeRuSetup.H ⊓ d.L = d.toTypeRuSetup.L₁ ⊔ (d.T : Subgroup G) := by
  have hT := le_inf d.T_le_L d.toTypeRuSetup.T_le_H
  have hh := congrArg (fun A : Subgroup ↥(d.L ⊓ d.toTypeRuSetup.H) =>
    A.map (d.L ⊓ d.toTypeRuSetup.H).subtype)
    (pResidual_sup_sylow_eq_top (d.T.subtype hT))
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hh
  change d.toTypeRuSetup.L₁ ⊔ ((d.T : Subgroup G).subgroupOf
    (d.L ⊓ d.toTypeRuSetup.H)).map (d.L ⊓ d.toTypeRuSetup.H).subtype = _ at hh
  rw [map_subgroupOf_eq_of_le hT] at hh
  exact (inf_comm _ _).trans hh.symm


/-- U is abelian and contains V, so it lies in C_G(V) = S. -/
theorem LocalSetup.U_le_S (d : LocalSetup G) : d.toTypeRuSetup.U ≤ d.toTypeRuSetup.S := by
  have hUC : d.toTypeRuSetup.U ≤ centralizer (d.toTypeRuSetup.U : Set G) :=
    d.U_le_HC.trans inf_le_right
  have hv := hUC.trans (centralizer_le (le_conjugateSpan d.toTypeRuSetup.H d.V))
  rwa [d.ru1.centralizer_V] at hv

/-- Q preserves V because its displacement on U lies in Z ≤ V. -/
theorem LocalSetup.Q_le_L (d : LocalSetup G) : d.toTypeRuSetup.Q ≤ d.L := by
  rw [d.ru1.normalizer_eq]
  apply le_normalizer_iff.mpr
  intro q hq v hv
  have hc := d.toTypeRuSetup.commutator_Q_U_le_Z
    (commutator_mem_commutator hq (le_conjugateSpan d.toTypeRuSetup.H d.V hv))
  have hZV := d.center_eq.le.trans inf_le_left
  have hm := d.V.mul_mem (hZV hc) hv
  simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hm

/-- S centralizes Z, which is contained in its center V. -/
theorem LocalSetup.S_le_H (d : LocalSetup G) : d.toTypeRuSetup.S ≤ d.toTypeRuSetup.H := by
  change d.L.pCoreIn 2 ≤ centralizer (d.toTypeRuSetup.Z : Set G)
  rw [← d.ru1.centralizer_V]
  exact centralizer_le (d.center_eq.le.trans inf_le_left)

/-- The product QS is a normal two-subgroup of the parabolic overlap. -/
theorem LocalSetup.Q_sup_S_le_parabolic_core (d : LocalSetup G) :
    d.toTypeRuSetup.Q ⊔ d.toTypeRuSetup.S ≤
      (d.toTypeRuSetup.H ⊓ d.L).pCoreIn 2 := by
  apply sup_le
  · apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 d.toTypeRuSetup.H)
      (le_inf (pCoreIn_le 2 _) d.Q_le_L)
    exact inf_le_left.trans d.ru2.six.normalized
  · apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 d.L)
      (le_inf d.S_le_H (pCoreIn_le 2 _))
    exact inf_le_right.trans d.ru1.steinberg.normalized

/-- The Q-commutator is exactly the distinguished order-two center. -/
theorem LocalSetup.commutator_Q_U (d : LocalSetup G) :
    ⁅d.toTypeRuSetup.Q, d.toTypeRuSetup.U⁆ = d.toTypeRuSetup.Z := by
  have hn : ⁅d.toTypeRuSetup.Q, d.toTypeRuSetup.U⁆ ≠ ⊥ := by
    intro he
    apply d.not_U_le_centralizer_Q
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
  have hl := (one_lt_card_iff_ne_bot _).mpr hn
  apply Subgroup.eq_of_le_of_card_ge d.toTypeRuSetup.commutator_Q_U_le_Z
  rw [d.card_Z]
  omega


/-- The join describing the parabolic overlap is literally the product L₁T. -/
theorem LocalSetup.mem_H_inf_L (d : LocalSetup G) (x : G) :
    x ∈ d.toTypeRuSetup.H ⊓ d.L ↔
      ∃ a ∈ d.toTypeRuSetup.L₁, ∃ t ∈ (d.T : Subgroup G), a * t = x := by
  constructor
  · intro hx
    have hT := le_inf d.T_le_L d.toTypeRuSetup.T_le_H
    have hp := pResidual_sup_sylow_eq_top (d.T.subtype hT)
    have hm : (⟨x, hx.2, hx.1⟩ : ↥(d.L ⊓ d.toTypeRuSetup.H)) ∈
        pResidual 2 ↥(d.L ⊓ d.toTypeRuSetup.H) ⊔ (d.T.subtype hT : Subgroup _) := by
      rw [hp]
      trivial
    obtain ⟨a, ha, t, ht, he⟩ := mem_sup_of_normal_left.mp hm
    exact ⟨a, mem_map.mpr ⟨a, ha, rfl⟩, t, ht, congrArg Subtype.val he⟩
  · rintro ⟨a, ha, t, ht, rfl⟩
    rw [d.H_inf_L]
    exact mul_mem_sup ha ht

/-- Every Q-action is a shear into Z that fixes Z pointwise. -/
theorem LocalSetup.transvection_of_Q (d : LocalSetup G) (q : d.toTypeRuSetup.Q) :
    ∃ f : d.toTypeRuSetup.U →* d.toTypeRuSetup.Z,
      (∀ z : d.toTypeRuSetup.Z, f ⟨z, d.ru2.natural.kernel_le z.property⟩ = 1) ∧
      ∀ u : d.toTypeRuSetup.U, (q : G) * u * (q : G)⁻¹ = (f u : G) * u := by
  let f : d.toTypeRuSetup.U →* d.toTypeRuSetup.Z := {
    toFun u := ⟨⁅(q : G), (u : G)⁆, d.toTypeRuSetup.commutator_Q_U_le_Z
      (commutator_mem_commutator q.property u.property)⟩
    map_one' := Subtype.ext (commutatorElement_one_right _)
    map_mul' u v := by
      apply Subtype.ext
      change ⁅(q : G), (u : G) * v⁆ = ⁅(q : G), (u : G)⁆ * ⁅(q : G), (v : G)⁆
      have hc := (d.ru2.natural.section_le u.property) _
        (d.toTypeRuSetup.commutator_Q_U_le_Z (commutator_mem_commutator q.property v.property))
      calc
        _ = ⁅(q : G), (u : G)⁆ * ((u : G) * ⁅(q : G), (v : G)⁆ * (u : G)⁻¹) := by
          rw [commutatorElement_mul_right_eq_mul_conj]
          group
        _ = _ := by rw [← hc, mul_inv_cancel_right] }
  refine ⟨f, ?_, ?_⟩
  · intro z
    apply Subtype.ext
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact ((pCoreIn_le 2 d.toTypeRuSetup.H q.property) z z.property).symm
  · intro u
    change _ = ⁅(q : G), (u : G)⁆ * u
    rw [commutatorElement_def]
    group

/-- Exact equality of the induced action image with all shears of center Z. -/
theorem LocalSetup.transvection_image (d : LocalSetup G)
    (σ : d.toTypeRuSetup.U → G) :
    (∃ q : d.toTypeRuSetup.Q, ∀ u : d.toTypeRuSetup.U,
      (q : G) * u * (q : G)⁻¹ = σ u) ↔
    ∃ f : d.toTypeRuSetup.U →* d.toTypeRuSetup.Z,
      (∀ z : d.toTypeRuSetup.Z, f ⟨z, d.ru2.natural.kernel_le z.property⟩ = 1) ∧
      ∀ u : d.toTypeRuSetup.U, σ u = (f u : G) * u := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨f, hf, he⟩ := d.transvection_of_Q q
    exact ⟨f, hf, fun u => (hq u).symm.trans (he u)⟩
  · rintro ⟨f, hf, he⟩
    obtain ⟨q, hq⟩ := d.full_transvection_action f hf
    exact ⟨q, fun u => (hq u).trans (he u).symm⟩

end CFSG.Quasithin.ChapterJ
