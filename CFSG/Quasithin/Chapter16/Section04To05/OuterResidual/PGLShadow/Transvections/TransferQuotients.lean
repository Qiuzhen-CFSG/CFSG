module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.Transvections.Configuration
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.Transvections.Geometry
public import Theory.Frattini.BinarySquares
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The two transfer quotients in the transvection endgame

For the actual subgroup D = T_L⟨u⟩, the PGL₂ product T = T_C T_L R and
T_C = ⟨z⟩ give T = D⟨z⟩ and index two. In the Aut(A₆) branch, the retained
isomorphism T_E ≃ E₄ × C₄ makes Φ(T_E) a characteristic subgroup of order two.
The actual s,t action fixes its nonidentity element, so the common fixed-point
calculation identifies the embedded Frattini subgroup with ⟨vz⟩.

The product T = T_E T_L proves D normal in T: T_E normalizes T_L and centralizes
u. The quotient is an image of T_E killing ⟨u,v⟩, hence has order at most four.
A square root of vz survives with order four, yielding the actual cyclic-four
equivalence. Both normality and quotient formation are relative to T.

These are conditional helpers for the final assembly of Lemma 16.4.6.
The source owner must supply the configuration, the exclusion of all conjugates
of z from D, and the intrinsic branch product identities. PGLBranch and
AutSixBranch retain actual model equivalences for L and H* = N_G(L)/C_G(L),
with their compatible conjugation actions. No index or normality of D,
Frattini identity or isomorphism for T/D is assumed. The source owner must construct
these branch data; this module does not assert the whole book lemma.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 16.4.6, printed pp.1185–1186, especially the two endings on p.1186.
-/

public section

open Subgroup GorensteinWalter
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.Transvections.TransferQuotients
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L R : Subgroup G} {g r z v u s t : G}
variable (h : Configuration T L R g r z v u s t)

private theorem mem_two {a x : G} (ha : orderOf a = 2) :
    x ∈ zpowers a ↔ x = 1 ∨ x = a := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, ha]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, hn'⟩
    interval_cases n <;> simp_all
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, by simp⟩
    · exact ⟨1, by decide, by simp⟩

omit [Finite G] in
private theorem comm_in {A : Subgroup G} [IsMulCommutative A]
    {x y : G} (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x :=
  congrArg Subtype.val (mul_comm (⟨x, hx⟩ : A) ⟨y, hy⟩)

include h

private theorem v_inner : v ∈ innerSylow T L := by
  have hv : v ∈ omegaOneAmbient (pairCentralizer T r z) ⊓ L := by
    rw [h.inner_intersection]
    exact mem_zpowers v
  exact ⟨(omegaOneAmbient_le _ hv.1).1, hv.2⟩

private theorem u_pair : u ∈ pairCentralizer T r z :=
  omegaOneAmbient_le _ h.eight.u_mem

private theorem transfer_le : transferSubgroup T L u ≤ (T : Subgroup G) :=
  sup_le inf_le_left (zpowers_le.mpr (u_pair h).1)

private theorem v_transfer : v ∈ transferSubgroup T L u :=
  mem_sup_left (v_inner h)

private theorem inner_normalized : (T : Subgroup G) ≤ normalizer (innerSylow T L : Set G) := by
  apply le_normalizer_iff.mpr
  intro a ha x hx
  exact ⟨(T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ha hx.1)
      ((T : Subgroup G).inv_mem ha),
    (mem_normalizer_iff.mp (h.source.sylow_normalizes ha) x).mp hx.2⟩

/-- The missing Frattini involution is outside D because v is in T_L and z is not fused into D. -/
theorem fixed_product_not_mem
    (havoid : ∀ x ∈ transferSubgroup T L u, ¬ IsConj z x) :
    v * z ∉ transferSubgroup T L u := by
  intro hw
  have hz : z ∈ transferSubgroup T L u := by
    simpa only [inv_mul_cancel_left] using
      (transferSubgroup T L u).mul_mem
        ((transferSubgroup T L u).inv_mem (v_transfer h)) hw
  exact havoid z hz (IsConj.refl z)

/-- Normality is in T. The abelian factor T_E centralizes u and normalizes T_L. -/
theorem transfer_normal
    (hT : (T : Subgroup G) = pairCentralizer T r z ⊔ innerSylow T L) :
    ((transferSubgroup T L u).subgroupOf (T : Subgroup G)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer (transfer_le h)).mpr
  rw [hT]
  refine sup_le ?_ (le_sup_left.trans (transferSubgroup T L u).le_normalizer)
  intro a ha
  apply normalizer_inf_normalizer_le_normalizer_sup (innerSylow T L) (zpowers u)
  refine ⟨inner_normalized h ha.1, ?_⟩
  apply Subgroup.centralizer_le_normalizer
  rw [zpowers_eq_closure, centralizer_closure]
  apply mem_centralizer_singleton_iff.mpr
  let := h.centralizer_abelian
  exact comm_in ha (u_pair h)

private theorem sylow_eq_transfer_sup
    (hTC : centralizingSylow T L = zpowers z)
    (hT : (T : Subgroup G) = (centralizingSylow T L ⊔ innerSylow T L) ⊔ R) :
    (T : Subgroup G) = transferSubgroup T L u ⊔ zpowers z := by
  apply le_antisymm
  · rw [hT, hTC, h.R_eq]
    refine sup_le (sup_le le_sup_right (le_sup_left.trans le_sup_left)) (zpowers_le.mpr ?_)
    have hu2 : u * u = 1 := by simpa only [pow_two, h.eight.u_order] using pow_orderOf_eq_one u
    have hr : r = u * (v * z) := by
      rw [h.eight.fixed_line_relation, ← mul_assoc, hu2, one_mul]
    rw [hr]
    exact (transferSubgroup T L u ⊔ zpowers z).mul_mem
      (mem_sup_left (mem_sup_right (mem_zpowers u)))
      (mul_mem_sup (v_transfer h) (mem_zpowers z))
  · exact sup_le (transfer_le h) (zpowers_le.mpr h.source.mem_sylow)

/-- The PGL product gives the precise index required by index_two_contradiction. -/
theorem index_two_of_product
    (hTC : centralizingSylow T L = zpowers z)
    (havoid : ∀ x ∈ transferSubgroup T L u, ¬ IsConj z x)
    (hT : (T : Subgroup G) = (centralizingSylow T L ⊔ innerSylow T L) ⊔ R) :
    ((transferSubgroup T L u).subgroupOf (T : Subgroup G)).index = 2 := by
  have hzout : z ∉ transferSubgroup T L u := fun hz => havoid z hz (IsConj.refl z)
  have hznorm : z ∈ normalizer (transferSubgroup T L u : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    apply mem_centralizer_iff.mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mp (h.source.sylow_centralizes (transfer_le h hx))
  have hc := card_sup_zpowers_of_normalizing_involution (transferSubgroup T L u) z
    (h.eight.z_order ▸ pow_orderOf_eq_one z) hzout hznorm
  rw [← sylow_eq_transfer_sup h hTC hT] at hc
  have hi := ((transferSubgroup T L u).subgroupOf (T : Subgroup G)).index_mul_card
  have he := Nat.card_congr (subgroupOfEquivOfLe (transfer_le h)).toEquiv
  rw [he, hc] at hi
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hi

private theorem plane_card : Nat.card (zpowers u ⊔ zpowers v : Subgroup G) = 4 := by
  let := h.eight.elementary
  have hvout : v ∉ zpowers u := by
    intro hv
    rcases (mem_two h.eight.u_order).mp hv with he | he
    · have ho := h.eight.v_order
      simp [he] at ho
    · exact h.eight.u_ne_v he.symm
  have hn : v ∈ normalizer (zpowers u : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    rw [zpowers_eq_closure, centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr (comm_in h.eight.v_mem h.eight.u_mem)
  rw [card_sup_zpowers_of_normalizing_involution _ _
    (h.eight.v_order ▸ pow_orderOf_eq_one v) hvout hn, Nat.card_zpowers, h.eight.u_order]


/-- The precise abelian centralizer in the Aut(A₆) branch. -/
abbrev FourModel :=
  (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × Multiplicative (ZMod 4)

private def modelRoot : FourModel := ((1, 1), Multiplicative.ofAdd 1)
private def modelSquare : FourModel := ((1, 1), Multiplicative.ofAdd 2)

omit h in
private theorem model_squares (x : FourModel) : x ^ 2 = 1 ∨ x ^ 2 = modelSquare := by
  revert x
  decide

omit h in
private theorem model_root_sq : modelRoot ^ 2 = modelSquare := by decide
omit h in
private theorem model_square_order : orderOf modelSquare = 2 :=
  orderOf_eq_prime (by decide) (by decide)
omit h in
private theorem model_card : Nat.card FourModel = 16 := by rw [Nat.card_eq_fintype_card]; decide

omit h in
private theorem frattini_preimage (e : pairCentralizer T r z ≃* FourModel) :
    frattini (pairCentralizer T r z) = zpowers (e.symm modelSquare) := by
  have hP : IsPGroup 2 (pairCentralizer T r z) :=
    T.isPGroup'.of_injective (inclusion inf_le_left) (inclusion_injective _)
  rw [hP.frattini_eq_closure_squares]
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨y, rfl⟩
    change y ^ 2 ∈ zpowers (e.symm modelSquare)
    rcases model_squares (e y) with he | he
    · have hy : y ^ 2 = 1 := e.injective (by simpa only [map_pow, map_one] using he)
      rw [hy]
      exact one_mem _
    · have hy : y ^ 2 = e.symm modelSquare := e.injective (by
        simpa only [map_pow, e.apply_symm_apply] using he)
      rw [hy]
      exact mem_zpowers _
  · apply zpowers_le.mpr
    apply Subgroup.subset_closure
    refine ⟨e.symm modelRoot, ?_⟩
    change (e.symm modelRoot) ^ 2 = e.symm modelSquare
    rw [← map_pow, model_root_sq]

/-- The characteristic order-two Frattini subgroup is fixed by s and t. Their
common fixed-point calculation therefore identifies its ambient image as ⟨vz⟩. -/
theorem frattini_eq_fixed_line (e : pairCentralizer T r z ≃* FourModel) :
    (frattini (pairCentralizer T r z)).map (pairCentralizer T r z).subtype =
      zpowers (v * z) := by
  let w : pairCentralizer T r z := e.symm modelSquare
  have hw2 : orderOf w = 2 := (e.symm.orderOf_eq _).trans model_square_order
  have hwne : w ≠ 1 := by intro he; simp [he] at hw2
  have hphi : frattini (pairCentralizer T r z) = zpowers w := frattini_preimage e
  have hfix (a : G) (ha : a ∈ normalizer (pairCentralizer T r z : Set G)) :
      MulAut.conj a (w : G) = w := by
    let α : MulAut (pairCentralizer T r z) :=
      (pairCentralizer T r z).normalizerMonoidHom ⟨a, ha⟩
    have hwphi : w ∈ frattini (pairCentralizer T r z) := by rw [hphi]; exact mem_zpowers w
    have haw : α w ∈ frattini (pairCentralizer T r z) :=
      (characteristic_iff_le_comap.mp (inferInstance :
        (frattini (pairCentralizer T r z)).Characteristic) α) hwphi
    rw [hphi] at haw
    rcases (mem_two hw2).mp haw with he | he
    · exact (hwne (α.injective (he.trans (map_one α).symm))).elim
    · exact congrArg Subtype.val he
  have hwV : (w : G) ∈ omegaOneAmbient (pairCentralizer T r z) :=
    (omegaOneAmbient_le_iff _ _).mp le_rfl (w : G) w.property
      (by exact congrArg Subtype.val (hw2 ▸ pow_orderOf_eq_one w))
  have hwline : (w : G) = v * z := by
    rcases (h.eight.common_fixed_iff w hwV).mp
      ⟨hfix t h.t_normalizes_centralizer, hfix s h.s_normalizes_centralizer⟩ with he | he
    · exact (hwne (Subtype.ext he)).elim
    · exact he
  rw [hphi, MonoidHom.map_zpowers]
  exact congrArg zpowers hwline

/-- A fourth root in the retained model squares to the actual fixed involution. -/
theorem exists_square_fixed_product (e : pairCentralizer T r z ≃* FourModel) :
    ∃ a : pairCentralizer T r z, (a : G) ^ 2 = v * z := by
  let a := e.symm modelRoot
  have hasq : a ^ 2 = e.symm modelSquare := by rw [← map_pow, model_root_sq]
  have haw : (a : G) ^ 2 ∈ zpowers (v * z) := by
    rw [← frattini_eq_fixed_line h e]
    refine ⟨a ^ 2, ?_, rfl⟩
    rw [frattini_preimage e, hasq]
    exact mem_zpowers _
  have hane : (a : G) ^ 2 ≠ 1 := by
    intro he
    have he' : a ^ 2 = 1 := Subtype.ext he
    rw [hasq] at he'
    have hn : orderOf (e.symm modelSquare) = 2 :=
      (e.symm.orderOf_eq _).trans model_square_order
    simp [he'] at hn
  have hvzorder : orderOf (v * z) = 2 := by
    apply orderOf_eq_prime
    · let := h.eight.elementary
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (v * z)
        ((omegaOneAmbient (pairCentralizer T r z)).mul_mem h.eight.v_mem h.eight.z_mem)
    · intro he
      have hvzV := h.eight.fixed_line_relation
      have hu2 : u * u = 1 := by simpa only [h.eight.u_order, pow_two] using pow_orderOf_eq_one u
      have hur : u = r := by
        calc
          u = u * (u * r) := by rw [← hvzV, he, mul_one]
          _ = r := by rw [← mul_assoc, hu2, one_mul]
      exact h.eight.u_ne_r hur
  exact ⟨a, ((mem_two hvzorder).mp haw).resolve_left hane⟩

private def pairQuotientMap
    [((transferSubgroup T L u).subgroupOf (T : Subgroup G)).Normal] :
    pairCentralizer T r z →* (T ⧸ (transferSubgroup T L u).subgroupOf (T : Subgroup G)) :=
  (QuotientGroup.mk' _).comp (inclusion inf_le_left)

private theorem pairQuotientMap_surjective
    [((transferSubgroup T L u).subgroupOf (T : Subgroup G)).Normal]
    (hT : (T : Subgroup G) = pairCentralizer T r z ⊔ innerSylow T L) :
    Function.Surjective (pairQuotientMap (T := T) (L := L) (u := u) (r := r) (z := z)) := by
  intro q
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective ((transferSubgroup T L u).subgroupOf (T : Subgroup G)) q
  have hb : (b : G) ∈ (innerSylow T L : Set G) * (pairCentralizer T r z : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (inf_le_left.trans (inner_normalized h)),
      sup_comm, ← hT]
    exact b.property
  obtain ⟨l, hl, a, ha, he⟩ := hb
  refine ⟨⟨a, ha⟩, ?_⟩
  have hb' : b = (⟨l, hl.1⟩ : T) * ⟨a, ha.1⟩ := Subtype.ext he.symm
  change QuotientGroup.mk' _ ⟨a, ha.1⟩ = QuotientGroup.mk' _ b
  have hlq : QuotientGroup.mk' ((transferSubgroup T L u).subgroupOf (T : Subgroup G))
      ⟨l, hl.1⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (mem_sup_left hl)
  rw [hb', map_mul, hlq, one_mul]

private theorem quotient_card_le_four
    [((transferSubgroup T L u).subgroupOf (T : Subgroup G)).Normal]
    (e : pairCentralizer T r z ≃* FourModel)
    (hT : (T : Subgroup G) = pairCentralizer T r z ⊔ innerSylow T L) :
    Nat.card (T ⧸ (transferSubgroup T L u).subgroupOf (T : Subgroup G)) ≤ 4 := by
  let f := pairQuotientMap (T := T) (L := L) (u := u) (r := r) (z := z)
  let A := (zpowers u ⊔ zpowers v).subgroupOf (pairCentralizer T r z)
  have hAV : zpowers u ⊔ zpowers v ≤ pairCentralizer T r z :=
    sup_le (zpowers_le.mpr (u_pair h))
      (zpowers_le.mpr (omegaOneAmbient_le _ h.eight.v_mem))
  have hAD : zpowers u ⊔ zpowers v ≤ transferSubgroup T L u :=
    sup_le le_sup_right (zpowers_le.mpr (v_transfer h))
  have hAK : A ≤ f.ker := by
    intro x hx
    change QuotientGroup.mk' _ (⟨(x : G), x.property.1⟩ : T) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (hAD hx)
  have hAc : Nat.card A = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAV).toEquiv).trans (plane_card h)
  have hKc : 4 ≤ Nat.card f.ker := by
    rw [← hAc]
    exact Nat.card_le_card_of_injective (inclusion hAK) (inclusion_injective _)
  have hc := f.ker.index_mul_card
  have hfc : f.ker.index =
      Nat.card (T ⧸ (transferSubgroup T L u).subgroupOf (T : Subgroup G)) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
      (pairQuotientMap_surjective h hT)).toEquiv
  have hec : Nat.card (pairCentralizer T r z) = 16 :=
    (Nat.card_congr e.toEquiv).trans model_card
  rw [hfc, hec] at hc
  nlinarith

/-- The model fourth root survives with order four in the actual relative quotient. -/
theorem quotient_order_four
    [((transferSubgroup T L u).subgroupOf (T : Subgroup G)).Normal]
    (e : pairCentralizer T r z ≃* FourModel)
    (havoid : ∀ x ∈ transferSubgroup T L u, ¬ IsConj z x) :
    ∃ x : T ⧸ (transferSubgroup T L u).subgroupOf (T : Subgroup G), orderOf x = 4 := by
  obtain ⟨a, ha⟩ := exists_square_fixed_product h e
  let f := pairQuotientMap (T := T) (L := L) (u := u) (r := r) (z := z)
  have hsquare : (f a) ^ 2 ≠ 1 := by
    rw [← map_pow]
    intro he
    have hm : (⟨(a : G), a.property.1⟩ : T) ^ 2 ∈
        (transferSubgroup T L u).subgroupOf (T : Subgroup G) :=
      (QuotientGroup.eq_one_iff _).mp he
    change (a : G) ^ 2 ∈ transferSubgroup T L u at hm
    rw [ha] at hm
    exact fixed_product_not_mem h havoid hm
  have hfour : (f a) ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, ← map_pow, ← map_pow]
    have he : (a ^ 2) ^ 2 = 1 := by
      apply Subtype.ext
      change ((a : G) ^ 2) ^ 2 = 1
      rw [ha]
      let := h.eight.elementary
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (v * z)
        ((omegaOneAmbient (pairCentralizer T r z)).mul_mem h.eight.v_mem h.eight.z_mem)
    rw [he, map_one]
  refine ⟨f a, ?_⟩
  have hd : orderOf (f a) ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hfour
  have hn : ¬ orderOf (f a) ∣ 2 := fun he => hsquare (orderOf_dvd_iff_pow_eq_one.mp he)
  obtain ⟨k, hk, ho⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show orderOf (f a) ∣ 2 ^ 2 from hd)
  interval_cases k
  · exact (hn (by simp [ho])).elim
  · exact (hn (by simp [ho])).elim
  · simpa using ho

/-- Construction of the cyclic-four equivalence, with relative normality proved
by transfer_normal. It has exactly the quotient type used by cyclic_four_contradiction. -/
noncomputable def cyclicFourEquiv
    (e : pairCentralizer T r z ≃* FourModel)
    (hT : (T : Subgroup G) = pairCentralizer T r z ⊔ innerSylow T L)
    (havoid : ∀ x ∈ transferSubgroup T L u, ¬ IsConj z x) :
    letI := transfer_normal h hT
    (T ⧸ (transferSubgroup T L u).subgroupOf (T : Subgroup G)) ≃*
      Multiplicative (ZMod 4) := by
  letI := transfer_normal h hT
  let x := (quotient_order_four h e havoid).choose
  have hx : orderOf x = 4 := (quotient_order_four h e havoid).choose_spec
  have hc : Nat.card (T ⧸ (transferSubgroup T L u).subgroupOf (T : Subgroup G)) = 4 :=
    Nat.le_antisymm (quotient_card_le_four h e hT) (hx ▸ orderOf_le_card (x := x))
  letI := isCyclic_of_orderOf_eq_card x (hx.trans hc.symm)
  exact mulEquivOfCyclicCardEq (hc.trans (by simp : Nat.card (Multiplicative (ZMod 4)) = 4).symm)

/-- Genuine PGL₂ branch data. The quotient is H* = N_G(L)/C_G(L), and the
compatibility equation identifies its action on the actual L with projective
matrix conjugation. The Sylow product is an explicit intrinsic model input;
constructing it and these model identifications remains the source owner's job. -/
structure PGLBranch (T : Sylow 2 G) (L R : Subgroup G)
    (F : Type*) [Field F] [Finite F] where
  odd : IsOddPrimePower (Nat.card F)
  card_gt : 3 < Nat.card F
  component : L ≃* PSL2 F
  action : componentActionQuotient L ≃* PGL2 F
  compatible : ∀ (n : normalizer (L : Set G)) (x : L),
    Matrix.ProjectiveSpecialLinearGroup.toPGL (component (L.normalizerMonoidHom n x)) =
      action (QuotientGroup.mk' _ n) * Matrix.ProjectiveSpecialLinearGroup.toPGL (component x) *
        (action (QuotientGroup.mk' _ n))⁻¹
  sylow_product : (T : Subgroup G) = (centralizingSylow T L ⊔ innerSylow T L) ⊔ R

/-- Genuine Aut(A₆) branch data. Both model equivalences retain the conjugation
action of N_G(L); T_E is the actual common centralizer, with its full E₄ × C₄
structure. The product T = T_E T_L remains an explicit intrinsic model input. -/
structure AutSixBranch (T : Sylow 2 G) (L : Subgroup G) (r z : G) where
  component : L ≃* alternatingGroup (Fin 6)
  action : componentActionQuotient L ≃* MulAut (alternatingGroup (Fin 6))
  compatible : ∀ n : normalizer (L : Set G),
    action (QuotientGroup.mk' _ n) = MulAut.congr component (L.normalizerMonoidHom n)
  centralizer : pairCentralizer T r z ≃* FourModel
  sylow_product : (T : Subgroup G) = pairCentralizer T r z ⊔ innerSylow T L

omit h [Finite G] in
/-- The ambient fusion premise, in the exact subtype form consumed by both
transfer contradiction theorems in PGLShadow. -/
theorem avoids_conjugates
    (havoid : ∀ x ∈ transferSubgroup T L u, ¬ IsConj z x) :
    ∀ x : T, x ∈ (transferSubgroup T L u).subgroupOf (T : Subgroup G) →
      ¬ IsConj z (x : G) := fun x hx => havoid x hx

/-- The PGL₂ transfer quotient has index two. All model input is marked by
actual equivalences and the compatible conjugation equation above. -/
theorem pgl_index_two {F : Type*} [Field F] [Finite F]
    (branch : PGLBranch T L R F)
    (hTC : centralizingSylow T L = zpowers z)
    (havoid : ∀ x ∈ transferSubgroup T L u, ¬ IsConj z x) :
    ((transferSubgroup T L u).subgroupOf (T : Subgroup G)).index = 2 :=
  index_two_of_product h hTC havoid branch.sylow_product

/-- The Aut(A₆) branch identifies the embedded Frattini subgroup using the
actual s,t action, proves relative normality, and omits the fixed involution. -/
theorem autSix_transfer_structure (branch : AutSixBranch T L r z)
    (havoid : ∀ x ∈ transferSubgroup T L u, ¬ IsConj z x) :
    (frattini (pairCentralizer T r z)).map (pairCentralizer T r z).subtype = zpowers (v * z) ∧
    ((transferSubgroup T L u).subgroupOf (T : Subgroup G)).Normal ∧
    v * z ∉ transferSubgroup T L u :=
  ⟨frattini_eq_fixed_line h branch.centralizer,
    transfer_normal h branch.sylow_product, fixed_product_not_mem h havoid⟩

/-- The actual cyclic-four quotient required by cyclic_four_contradiction.
The relative normality instance is supplied by the proof, not by the caller. -/
noncomputable def autSixCyclicFourEquiv (branch : AutSixBranch T L r z)
    (havoid : ∀ x ∈ transferSubgroup T L u, ¬ IsConj z x) :
    letI := transfer_normal h branch.sylow_product
    (T ⧸ (transferSubgroup T L u).subgroupOf (T : Subgroup G)) ≃*
      Multiplicative (ZMod 4) :=
  cyclicFourEquiv h branch.centralizer branch.sylow_product havoid

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.Transvections.TransferQuotients
