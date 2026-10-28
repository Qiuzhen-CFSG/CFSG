module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Reduction
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models.Coordinates
public import Theory.GroupTheory.PCoreImage

/-!
# The s = 1 layer calculations in 15.3.59

`LayerActions` specifies the actual tensor action on V and direct sum action
on P/V through one common map I → SL₂(2) × SL₂(2). Its earlier-source
inputs are enumerated explicitly:

* I normalizes P and V, and V is normal inside P;
* the common actor is surjective, with kernel P restricted to I;
* the actual image of Y is the product of the two cubic rotation subgroups;
* both multiplicative coordinate equivalences intertwine literal conjugation.

The kernel input means C_I(V) = P when P ≤ I, by faithfulness of the tensor
action. It is an earlier local action-kernel obligation, not a conclusion
of this module. The surrounding source supplies Y ≤ I, normality of Y
inside I (from Y normal in M), P = O₂(I), V ≤ P, and V = Z(P).
The source equality I = YU is used in obtaining those actor inputs;
none of the calculations needs an additional supplement assumption.

Cubic displacement on the two layers gives [P,Y] = P. Relative normality
then places P in Y and identifies it with O₂(Y). The abelian upper layer
puts [P,P] inside V. Tensor irreducibility and the proper center force
[P,P] = V. The coordinates and actor kernel give all the required orders.
Finally, conjugation restriction transports the same two images from I
to M; both have order nine. `Models.Normalizers` applies the general
automorphism-normalizer residual theorem to these actual images.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.53(1), 15.3.54(4), 15.3.55, and proof of 15.3.59,
printed pp.1146–1147 and 1150. The source owner must construct these
earlier action witnesses before applying the calculations.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
open Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G]

/-- The s = 1 action descriptions from 15.3.53(1) and 15.3.54(4).
The single actor map, both intertwining equations, the actual Y-image,
and the earlier local kernel equality are all retained. -/
structure LayerActions (I Y P V : Subgroup G)
    (hIP : I ≤ normalizer (P : Set G)) (hIV : I ≤ normalizer (V : Set G))
    [(V.subgroupOf P).Normal] where
  actor : I →* Actor
  onto : Function.Surjective actor
  kernel : actor.ker = P.subgroupOf I
  image_Y : (Y.subgroupOf I).map actor = nine
  lowerCoordinates : V ≃* TensorVector
  upperCoordinates : (P ⧸ V.subgroupOf P) ≃* SumVector
  lower_compatible : ∀ (i : I) (v : V),
    lowerCoordinates (lowerAction I V hIV i v) = tensorAction (actor i) (lowerCoordinates v)
  upper_compatible : ∀ (i : I) (v : P ⧸ V.subgroupOf P),
    upperCoordinates (upperAction I P V hIP hIV i v) = sumAction (actor i) (upperCoordinates v)

namespace LayerActions
variable {I Y P V : Subgroup G}
variable {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (V : Set G)}
variable [(V.subgroupOf P).Normal] (d : LayerActions I Y P V hIP hIV)
include d

theorem card_lower : Nat.card V = 16 := by
  rw [Nat.card_congr d.lowerCoordinates.toEquiv]
  norm_num [TensorVector, Matrix, Nat.card_eq_fintype_card]

theorem card_upper : Nat.card (P ⧸ V.subgroupOf P) = 16 := by
  rw [Nat.card_congr d.upperCoordinates.toEquiv]
  norm_num [SumVector, Plane, Nat.card_eq_fintype_card]

theorem card_core (hVP : V ≤ P) : Nat.card P = 256 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf P), d.card_upper,
    Nat.card_congr (subgroupOfEquivOfLe hVP).toEquiv, d.card_lower]

theorem card_actor_domain (hPI : P ≤ I) (hVP : V ≤ P) : Nat.card I = 9216 := by
  have hc := d.actor.ker.card_mul_index
  rw [d.kernel, Nat.card_congr (subgroupOfEquivOfLe hPI).toEquiv, d.card_core hVP] at hc
  have hi : d.actor.ker.index = 36 := by
    rw [Subgroup.index_ker, d.actor.range_eq_top.mpr d.onto, Nat.card_congr Subgroup.topEquiv.toEquiv]
    exact card_actor
  rw [← d.kernel, hi] at hc
  exact hc.symm

theorem twoPart_actor_domain (hPI : P ≤ I) (hVP : V ≤ P) :
    2 ^ (Nat.card I).factorization 2 = 1024 := by
  rw [d.card_actor_domain hPI hVP]
  change 2 ^ ((2 ^ 10 * 3 ^ 2).factorization 2) = 1024
  rw [Nat.factorization_mul (by norm_num : 2 ^ 10 ≠ 0) (by norm_num : 3 ^ 2 ≠ 0)]
  rw [Nat.prime_two.factorization_pow, Nat.prime_three.factorization_pow]
  norm_num

theorem lower_hom_transport :
    (MulAut.congr d.lowerCoordinates).toMonoidHom.comp (lowerAction I V hIV) =
      tensorAction.comp d.actor := by
  apply MonoidHom.ext
  intro i
  apply MulEquiv.ext
  intro v
  change d.lowerCoordinates (lowerAction I V hIV i (d.lowerCoordinates.symm v)) = _
  rw [d.lower_compatible, d.lowerCoordinates.apply_symm_apply]
  rfl

theorem upper_hom_transport :
    (MulAut.congr d.upperCoordinates).toMonoidHom.comp (upperAction I P V hIP hIV) =
      sumAction.comp d.actor := by
  apply MonoidHom.ext
  intro i
  apply MulEquiv.ext
  intro v
  change d.upperCoordinates (upperAction I P V hIP hIV i (d.upperCoordinates.symm v)) = _
  rw [d.upper_compatible, d.upperCoordinates.apply_symm_apply]
  rfl

theorem lower_image_transport :
    (lowerImage I Y V hIV).map (MulAut.congr d.lowerCoordinates).toMonoidHom =
      nine.map tensorAction := by
  rw [lowerImage, map_map, d.lower_hom_transport, ← map_map, d.image_Y]

theorem upper_image_transport :
    (upperImage I Y P V hIP hIV).map (MulAut.congr d.upperCoordinates).toMonoidHom =
      nine.map sumAction := by
  rw [upperImage, map_map, d.upper_hom_transport, ← map_map, d.image_Y]

theorem card_lower_image : Nat.card (lowerImage I Y V hIV) = 9 := by
  rw [Nat.card_congr ((lowerImage I Y V hIV).equivMapOfInjective
    (MulAut.congr d.lowerCoordinates).toMonoidHom (MulAut.congr d.lowerCoordinates).injective).toEquiv,
    d.lower_image_transport,
    ← Nat.card_congr (nine.equivMapOfInjective tensorAction tensorAction_injective).toEquiv,
    card_nine]

theorem card_upper_image : Nat.card (upperImage I Y P V hIP hIV) = 9 := by
  rw [Nat.card_congr ((upperImage I Y P V hIP hIV).equivMapOfInjective
    (MulAut.congr d.upperCoordinates).toMonoidHom (MulAut.congr d.upperCoordinates).injective).toEquiv,
    d.upper_image_transport,
    ← Nat.card_congr (nine.equivMapOfInjective sumAction sumAction_injective).toEquiv,
    card_nine]

/-- The lower layer is generated by actual commutators with Y. -/
theorem commutator_lower (hYI : Y ≤ I) : ⁅V, Y⁆ = V := by
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp (hYI.trans hIV))
  intro v hv
  have ha : (rotation, 1) ∈ (Y.subgroupOf I).map d.actor := by
    rw [d.image_Y]
    exact ⟨mem_zpowers rotation, cubic.one_mem⟩
  obtain ⟨y, hy, he⟩ := ha
  obtain ⟨w, hw⟩ := tensor_displacement (d.lowerCoordinates ⟨v, hv⟩)
  let u := d.lowerCoordinates.symm w
  have heq : ((lowerAction I V hIV y u) * u⁻¹ : V) = ⟨v, hv⟩ := by
    apply d.lowerCoordinates.injective
    rw [map_mul, map_inv, d.lower_compatible, he, d.lowerCoordinates.apply_symm_apply]
    exact hw
  have hmem : ⁅(y : G), (u : G)⁆ ∈ ⁅Y, V⁆ := commutator_mem_commutator hy u.property
  rw [commutator_comm Y V] at hmem
  have hg := congrArg V.subtype heq
  change ⁅(y : G), (u : G)⁆ = v at hg
  rwa [← hg]

/-- Displacement on both genuine layers generates the entire group P. -/
theorem commutator_core (hYI : Y ≤ I) (hVP : V ≤ P) : ⁅P, Y⁆ = P := by
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp (hYI.trans hIP))
  intro p hp
  have hvD : V ≤ ⁅P, Y⁆ := by
    rw [← d.commutator_lower hYI]
    exact commutator_mono hVP le_rfl
  have ha : (rotation, rotation) ∈ (Y.subgroupOf I).map d.actor := by
    rw [d.image_Y]
    exact ⟨mem_zpowers rotation, mem_zpowers rotation⟩
  obtain ⟨y, hy, he⟩ := ha
  let q := QuotientGroup.mk' (V.subgroupOf P)
  let pP : P := ⟨p, hp⟩
  obtain ⟨w, hw⟩ := sum_displacement (d.upperCoordinates (q pP))
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (V.subgroupOf P) (d.upperCoordinates.symm w)
  let t : P := ⟨(y : G) * (u : G) * (y : G)⁻¹ * (u : G)⁻¹,
    P.mul_mem ((mem_normalizer_iff.mp (hIP y.property) u).mp u.property)
      (P.inv_mem u.property)⟩
  have htD : (t : G) ∈ ⁅P, Y⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator hy u.property
  have ht : q t = q pP := by
    apply d.upperCoordinates.injective
    have htc : q t = upperAction I P V hIP hIV y (q u) * (q u)⁻¹ := by
      rw [upperAction_mk]
      change q ((⟨(y : G) * (u : G) * (y : G)⁻¹,
        (mem_normalizer_iff.mp (hIP y.property) u).mp u.property⟩ : P) * u⁻¹) = _
      rw [map_mul, map_inv]
    rw [htc, map_mul, map_inv, d.upper_compatible, he, hu,
      d.upperCoordinates.apply_symm_apply]
    exact hw
  have hvt : (t⁻¹ * pP : P) ∈ V.subgroupOf P := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (t⁻¹ * pP) = 1
    rw [map_mul, map_inv, ht, inv_mul_cancel]
  have hm := (⁅P, Y⁆).mul_mem htD (hvD hvt)
  change (t : G) * ((t : G)⁻¹ * p) ∈ ⁅P, Y⁆ at hm
  simpa only [mul_inv_cancel_left] using hm

/-- Normality of Y is relative to I, not to the ambient group. -/
theorem core_le_Y (hYI : Y ≤ I) (hPI : P ≤ I)
    (hIY : I ≤ normalizer (Y : Set G)) (hVP : V ≤ P) : P ≤ Y := by
  rw [← d.commutator_core hYI hVP]
  exact le_normalizer_iff_commutator_le_right.mp (hPI.trans hIY)

/-- The computed commutator identifies the same group as the two-core of Y. -/
theorem core_eq_twoCore_Y (hYI : Y ≤ I) (hIY : I ≤ normalizer (Y : Set G))
    (hVP : V ≤ P) (hP : P = Stellmacher.twoCoreAmbient I) :
    P = Stellmacher.twoCoreAmbient Y := by
  have hPI : P ≤ I := hP ▸ map_subtype_le _
  have hPY := d.core_le_Y hYI hPI hIY hVP
  apply le_antisymm
  · exact le_pCoreIn_of_normalizes (hP.symm ▸ pCore_isPGroup.map I.subtype)
      hPY (hYI.trans hIP)
  · exact hP.symm ▸ pCoreIn_mono_of_normalizes hYI hIY

/-- The elementary upper layer places every P-commutator in V. -/
theorem derived_le_lower : ⁅P, P⁆ ≤ V := by
  apply commutator_le.mpr
  intro a ha b hb
  have h : ⁅(⟨a, ha⟩ : P), (⟨b, hb⟩ : P)⁆ ∈ V.subgroupOf P := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply d.upperCoordinates.injective
    change d.upperCoordinates (QuotientGroup.mk' (V.subgroupOf P) _) = _
    rw [map_commutatorElement, map_commutatorElement, map_one]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  exact h

/-- The tensor module has no proper nontrivial I-invariant subgroup. -/
theorem lower_irreducible (D : Subgroup G) (hDV : D ≤ V)
    (hID : I ≤ normalizer (D : Set G)) : D = ⊥ ∨ D = V := by
  let D₀ := (D.subgroupOf V).map d.lowerCoordinates.toMonoidHom
  have hn : ∀ (a : Actor) (x : TensorVector), x ∈ D₀ → tensorAction a x ∈ D₀ := by
    intro a x hx
    obtain ⟨i, rfl⟩ := d.onto a
    obtain ⟨v, hv, rfl⟩ := hx
    refine ⟨lowerAction I V hIV i v, ?_, d.lower_compatible i v⟩
    exact (mem_normalizer_iff.mp (hID i.property) v).mp hv
  rcases tensor_irreducible D₀ hn with hbot | htop
  · left
    apply bot_unique
    intro v hv
    have hmem : d.lowerCoordinates ⟨v, hDV hv⟩ ∈ D₀ := mem_map_of_mem _ hv
    rw [hbot, mem_bot] at hmem
    have he := (map_eq_one_iff d.lowerCoordinates d.lowerCoordinates.injective).mp hmem
    exact congrArg V.subtype he
  · right
    apply le_antisymm hDV
    intro v hv
    have hmem : d.lowerCoordinates ⟨v, hv⟩ ∈ D₀ := htop ▸ mem_top _
    obtain ⟨u, hu, he⟩ := hmem
    have heq := d.lowerCoordinates.injective he
    have heqG : (u : G) = v := congrArg V.subtype heq
    change (u : G) ∈ D at hu
    rwa [← heqG]

/-- A proper center rules out the zero derived submodule, so V = [P,P]. -/
theorem lower_eq_derived [Finite G] (hVP : V ≤ P)
    (hcenter : V = (center P).map P.subtype) : V = ⁅P, P⁆ := by
  have hID : I ≤ normalizer ((⁅P, P⁆ : Subgroup G) : Set G) := by
    intro i hi
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hIP hi)]
  rcases d.lower_irreducible ⁅P, P⁆ d.derived_le_lower hID with hbot | heq
  · have hPC : P ≤ centralizer (P : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp hbot
    have hPV : P ≤ V := by
      intro p hp
      rw [hcenter]
      refine ⟨⟨p, hp⟩, ?_, rfl⟩
      apply mem_center_iff.mpr
      intro q
      exact Subtype.ext (hPC hp q q.property)
    have hc := Subgroup.card_le_of_le hPV
    rw [d.card_core hVP, d.card_lower] at hc
    omega
  · exact heq.symm

omit d [(V.subgroupOf P).Normal] in
/-- The same center description supplies the lower-central hypothesis of
`residual_eq_of_local_core_and_automizers`. -/
theorem lower_central (hcenter : V = (center P).map P.subtype) :
    V ≤ centralizer (P : Set G) := by
  rw [hcenter]
  rintro _ ⟨v, hv, rfl⟩ p hp
  exact congrArg P.subtype ((mem_center_iff.mp hv) ⟨p, hp⟩)

/-- The actual quotient of Y by its two-core has order nine. -/
theorem card_Y_quotient (hYI : Y ≤ I) (hIY : I ≤ normalizer (Y : Set G))
    (hVP : V ≤ P) (hP : P = Stellmacher.twoCoreAmbient I) :
    Nat.card (Y ⧸ pCore 2 Y) = 9 := by
  let f := d.actor.comp (inclusion hYI)
  have hk : f.ker = pCore 2 Y := by
    ext y
    change d.actor (inclusion hYI y) = 1 ↔ y ∈ pCore 2 Y
    rw [← MonoidHom.mem_ker, d.kernel]
    change (y : G) ∈ P ↔ _
    rw [d.core_eq_twoCore_Y hYI hIY hVP hP]
    constructor
    · rintro ⟨z, hz, he⟩
      exact Subtype.ext he ▸ hz
    · intro hy
      exact mem_map_of_mem Y.subtype hy
  have hr : f.range = nine := by
    rw [← d.image_Y]
    ext a
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨inclusion hYI y, y.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [← hk, Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hr, card_nine]

/-- The lower coordinates make V an elementary binary group. -/
theorem elementary_lower : IsElementaryAbelian 2 V where
  toIsMulCommutative := IsMulCommutative.of_comm fun a b => d.lowerCoordinates.injective
    (by simp only [map_mul, mul_comm])
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun v => by
    apply d.lowerCoordinates.injective
    rw [map_pow, map_one]
    have h : ∀ x : TensorVector, x ^ 2 = 1 := by decide +kernel
    exact h _

/-- The upper coordinates make the literal quotient P/V elementary binary. -/
theorem elementary_upper : IsElementaryAbelian 2 (P ⧸ V.subgroupOf P) where
  toIsMulCommutative := IsMulCommutative.of_comm fun a b => d.upperCoordinates.injective
    (by simp only [map_mul, mul_comm])
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun v => by
    apply d.upperCoordinates.injective
    rw [map_pow, map_one]
    have h : ∀ x : SumVector, x ^ 2 = 1 := by decide +kernel
    exact h _

omit d [(V.subgroupOf P).Normal] in
/-- Restricting ambient conjugation to Y does not change its lower image. -/
theorem lowerImage_overgroup (M : Subgroup G) (hYI : Y ≤ I) (hIM : I ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) :
    lowerImage M Y V hMV = lowerImage I Y V hIV := by
  ext a
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, hYI hm⟩, hm, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hIM i.property⟩, hi, rfl⟩

omit d in
/-- The same restriction identity on the actual quotient; it follows from
`upperAction_mk`, independently of the chosen quotient-action witness. -/
theorem upperImage_overgroup (M : Subgroup G) (hYI : Y ≤ I) (hIM : I ≤ M)
    (hMP : M ≤ normalizer (P : Set G)) (hMV : M ≤ normalizer (V : Set G)) :
    upperImage M Y P V hMP hMV = upperImage I Y P V hIP hIV := by
  have he (i : I) : upperAction I P V hIP hIV i =
      upperAction M P V hMP hMV ⟨i, hIM i.property⟩ := by
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H q =>
      change upperAction I P V hIP hIV i (QuotientGroup.mk' _ q) =
        upperAction M P V hMP hMV ⟨i, hIM i.property⟩ (QuotientGroup.mk' _ q)
      rw [upperAction_mk, upperAction_mk]
  ext a
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, hYI hm⟩, hm, he ⟨m, hYI hm⟩⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hIM i.property⟩, hi, (he i).symm⟩

/-- The tensor model identifies the literal Y-image defined using M. -/
theorem lower_image_overgroup_transport (M : Subgroup G) (hYI : Y ≤ I) (hIM : I ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) :
    (lowerImage M Y V hMV).map (MulAut.congr d.lowerCoordinates).toMonoidHom =
      nine.map tensorAction := by
  rw [lowerImage_overgroup (hIV := hIV) M hYI hIM hMV]
  exact d.lower_image_transport

/-- The direct sum model identifies the literal Y-image on P/V defined using M. -/
theorem upper_image_overgroup_transport (M : Subgroup G) (hYI : Y ≤ I) (hIM : I ≤ M)
    (hMP : M ≤ normalizer (P : Set G)) (hMV : M ≤ normalizer (V : Set G)) :
    (upperImage M Y P V hMP hMV).map (MulAut.congr d.upperCoordinates).toMonoidHom =
      nine.map sumAction := by
  rw [upperImage_overgroup (hIP := hIP) (hIV := hIV) M hYI hIM hMP hMV]
  exact d.upper_image_transport

theorem card_lower_image_overgroup (M : Subgroup G) (hYI : Y ≤ I) (hIM : I ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) : Nat.card (lowerImage M Y V hMV) = 9 := by
  rw [lowerImage_overgroup (hIV := hIV) M hYI hIM hMV]
  exact d.card_lower_image

theorem card_upper_image_overgroup (M : Subgroup G) (hYI : Y ≤ I) (hIM : I ≤ M)
    (hMP : M ≤ normalizer (P : Set G)) (hMV : M ≤ normalizer (V : Set G)) :
    Nat.card (upperImage M Y P V hMP hMV) = 9 := by
  rw [upperImage_overgroup (hIP := hIP) (hIV := hIV) M hYI hIM hMP hMV]
  exact d.card_upper_image

end LayerActions
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
