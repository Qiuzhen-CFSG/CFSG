module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.SixSylowFixer.Transport
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.GroupAction.AutomorphismFixedResidualTransport
public import Theory.GroupAction.PerfectCentralQuotient
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6.HS
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CentralCoreInvolutionSource
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary
public import Theory.GroupTheory.CentralBinaryKernelSquares
public import Theory.GroupAction.CentralKernelFixedComponents
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.FullA6.HSProductTwist

/-!
# Exact HS fusion through the original central cover

The marked HS involution is conjugate to its product with any involution
of its actual A₆ fixed component. One checked representative calculation
and the unique A₆ involution class establish this in the literal model.

The HS multiplier bounds reduce an arbitrary finite perfect central cover
to center order one or two. In the double cover, the three nonidentity
points of the certified product-class four-group have equal nontrivial
squares. This conjugates a lift of the marked involution to its inverse,
so either possible central discrepancy in lifting conjugacy can be removed.
Thus the required product fusion holds in the cover itself.

The final consumer descends the original centerless fixed component and
its marked involution faithfully, lifts the inner action by perfectness,
and transfers the exact conjugacy to the original ambient group. The
crossing equation then contradicts source 2.5.11(2). This eliminates the
HS row without a core-four identity or a Sylow-position premise.

Source: Aschbacher–Smith 2.5.19, printed pp.561–562; I.2.2(5b), printed
p.412; and the HS involution classes of 16.1.5(10), printed p.1172.
-/

public section
set_option maxRecDepth 20000
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.FullA6.HS
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
open ClassCoverage ClassCoverage.ProductEmbedding
open ClassCoverage.ProductEmbedding.SylowFixerCertificate
open Sporadic.LeechRelated.HS

private theorem seed_mem_D : Seed.generator 3 ∈ D :=
  subset_closure (by simp)

private theorem seed_square : Seed.generator 3 ^ 2 = 1 := by
  apply Sporadic.LeechRelated.HS.inclusion_injective
  apply Equiv.ext
  have h : ∀ p : Fin 100, inclusion (Seed.generator 3 ^ 2) p = p := by
    apply Certificate.allFin
    decide +kernel
  exact h

private theorem seed_twist_fixedPointFree :
    ∀ p : Fin 100, inclusion (t * Seed.generator 3) p ≠ p := by
  apply Certificate.allFin
  decide +kernel

private theorem seed_twist_isConj : IsConj t (t * Seed.generator 3) := by
  have hsq : (t * Seed.generator 3) ^ 2 = 1 := by
    rw [(show Commute t (Seed.generator 3) from
      (mem_centralizer_singleton_iff.mp (D_le_centralizer (seed_mem_D))).symm).mul_pow,
      (orderOf_eq_prime_iff.mp t_order).1, seed_square, one_mul]
  have hn : t * Seed.generator 3 ≠ 1 := by
    intro h
    exact seed_twist_fixedPointFree 0 (by rw [h, map_one]; rfl)
  rcases involution_classes _ (orderOf_eq_prime hsq hn) with h | h
  · obtain ⟨g, hg⟩ := isConj_iff.mp h
    have he : (t * Seed.generator 3) * g = g * EvenLocalCandidates.e0 := by
      rw [← hg]; group
    have h0 : inclusion EvenLocalCandidates.e0 0 = 0 := by decide +kernel
    have hh := congrArg (fun x : Carrier => inclusion x 0) he
    exact (seed_twist_fixedPointFree (inclusion g 0)
      (by simpa only [map_mul, Equiv.Perm.mul_apply, h0] using hh)).elim
  · exact h

/-- Multiplying the product-class involution by an involution of its actual
alternating component preserves its HS class. -/
theorem component_involution_twist_isConj (k : Carrier) (hk : k ∈ D)
    (ho : orderOf k = 2) : IsConj t (t * k) := by
  obtain ⟨e⟩ := D_equiv_A6
  let d : D := ⟨Seed.generator 3, seed_mem_D⟩
  let kD : D := ⟨k, hk⟩
  have hd : orderOf d = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      exact seed_square
    · intro he
      have hv := congrArg (fun x : D => inclusion (x : Carrier) 0) he
      change inclusion (Seed.generator 3) 0 = 0 at hv
      have hn : inclusion (Seed.generator 3) 0 ≠ 0 := by decide +kernel
      exact hn hv
  have hc : IsConj d kD := by
    simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using e.symm.toMonoidHom.map_isConj
      (AlternatingSix.ShadowLocal.involutions_isConj (e d) (e kD)
        ((e.orderOf_eq d).trans hd) ((e.orderOf_eq kD).trans ((orderOf_coe kD).symm.trans ho)))
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  apply seed_twist_isConj.trans
  apply isConj_iff.mpr
  refine ⟨(g : Carrier), ?_⟩
  have hgt : Commute (g : Carrier) t := mem_centralizer_singleton_iff.mp (D_le_centralizer g.property)
  have hg' := congrArg Subtype.val hg
  change (g : Carrier) * Seed.generator 3 * (g : Carrier)⁻¹ = k at hg'
  change (g : Carrier) * (t * Seed.generator 3) * (g : Carrier)⁻¹ = t * k
  calc
    (g : Carrier) * (t * Seed.generator 3) * (g : Carrier)⁻¹ =
        t * ((g : Carrier) * Seed.generator 3 * (g : Carrier)⁻¹) := by
      rw [← mul_assoc, hgt.eq]
      group
    _ = t * k := congrArg (t * ·) hg'

/-- Compatible transport retains the literal fixed component and involution. -/
theorem marked_component_twist_isConj {E : Type*} [Group E]
    (e : E ≃* Carrier) (a : MulAut E)
    (he : ∀ x, e (a x) = MulAut.conj t (e x))
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (k : B) (hk : orderOf k = 2) : IsConj t (t * e ((k : a.fixedSubgroup) : E)) := by
  let j := MulAut.fixedSubgroupEquivOfCompatible e a (MulAut.conj t) he
  let C := B.map j.toMonoidHom
  let C' := C.map (MulAut.conj t).fixedSubgroup.subtype
  have hC : IsComponent (MulAut.conj t).fixedSubgroup C := hB.map_equiv j
  have hC' : IsComponentIn C' (MulAut.conj t).fixedSubgroup := by
    refine ⟨map_subtype_le C, ?_⟩
    change IsComponent (MulAut.conj t).fixedSubgroup
      ((C.map (MulAut.conj t).fixedSubgroup.subtype).comap
        (MulAut.conj t).fixedSubgroup.subtype)
    rwa [comap_map_eq_self_of_injective (MulAut.conj t).fixedSubgroup.subtype_injective]
  rw [MulAut.fixedSubgroup_conj] at hC'
  have hCD := component_eq_D C' hC'
  have hkm : e ((k : a.fixedSubgroup) : E) ∈ D := by
    rw [← hCD]
    rw [← MulAut.fixedSubgroupEquivOfCompatible_apply e a (MulAut.conj t) he
      (k : a.fixedSubgroup)]
    exact mem_map_of_mem (MulAut.conj t).fixedSubgroup.subtype
      (mem_map_of_mem j.toMonoidHom k.property)
  apply component_involution_twist_isConj _ hkm
  rw [e.orderOf_eq, orderOf_coe, orderOf_coe, hk]

open CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers
open ClassCoverage Sporadic.LeechRelated.HS

/-- All lifts of the marked class are conjugate in a central double cover. -/
theorem product_class_lifts_isConj {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (e : (E ⧸ center E) ≃* Carrier) (hZ : Nat.card (center E) = 2)
    (r : Carrier) (hr : IsConj t r) (hrt : IsConj t (t * r))
    (u v : E) (hu : HSLocal.modelMap e u = t)
    (hv : IsConj t (HSLocal.modelMap e v)) : IsConj u v := by
  let f := HSLocal.modelMap e
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = center E := HSLocal.modelMap_ker e
  have hk2 : ∀ k ∈ f.ker, k ^ 2 = 1 := by
    intro k hk
    have h := pow_card_eq_one' (x := (⟨k, hker ▸ hk⟩ : center E))
    rw [hZ] at h
    exact congrArg Subtype.val h
  have hu2Z : u ^ 2 ∈ center E := by
    rw [← hker, MonoidHom.mem_ker, map_pow, hu]
    exact (orderOf_eq_prime_iff.mp t_order).1
  obtain ⟨w, hw⟩ := hf r
  have hw2 : w ^ 2 = u ^ 2 :=
    (f.square_eq_of_isConj_map_of_central_binary_kernel hf hker.le hk2 hu2Z
      (by rw [hu, hw]; exact hr)).symm
  have huw2 : (u * w) ^ 2 = u ^ 2 :=
    (f.square_eq_of_isConj_map_of_central_binary_kernel hf hker.le hk2 hu2Z
      (by rw [hu, map_mul, hu, hw]; exact hrt)).symm
  have hflip : IsConj u u⁻¹ := by
    refine isConj_iff.mpr ⟨w, ?_⟩
    calc
      w * u * w⁻¹ = u⁻¹ * (u * w) ^ 2 * (w ^ 2)⁻¹ := by simp only [pow_two]; group
      _ = u⁻¹ := by rw [huw2, hw2]; group
  have huo : orderOf u = 4 := HSLocal.order_four_of_nonTwoCentral_image
    CFSG.Quasithin.ChapterB.NaturalExtensions.earlierB48Two e hZ u
    (by rw [hu]; exact t_order) (by rw [hu]; exact HSLocal.t_not_twoCentral)
  have hu2ne : u ^ 2 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [huo] at hd
    norm_num at hd
  have hcases (k : E) (hk : k ∈ f.ker) : k = 1 ∨ k = u ^ 2 := by
    by_cases h : k = 1
    · exact Or.inl h
    · right
      exact congrArg Subtype.val (((Nat.card_eq_two_iff' (1 : center E)).mp hZ).unique
        (show (⟨k, hker ▸ hk⟩ : center E) ≠ 1 from fun he => h (congrArg Subtype.val he))
        (show (⟨u ^ 2, hu2Z⟩ : center E) ≠ 1 from fun he => hu2ne (congrArg Subtype.val he)))
  obtain ⟨g, hg⟩ := isConj_iff.mp hv
  obtain ⟨b, hb⟩ := hf g
  let x := b * u * b⁻¹
  have hx : f x = f v := by
    dsimp only [x]
    rw [map_mul, map_mul, map_inv, hb, hu]
    exact hg
  have hdiff : x⁻¹ * v ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hx, inv_mul_cancel]
  rcases hcases _ hdiff with hc | hc
  · have he : x = v := inv_mul_eq_one.mp hc
    exact he ▸ isConj_iff.mpr ⟨b, rfl⟩
  · have huv : u * u ^ 2 = u⁻¹ := by
      apply mul_right_cancel (b := u)
      have h4 : u ^ 4 = 1 := huo ▸ pow_orderOf_eq_one u
      calc
        u * u ^ 2 * u = u ^ 4 := by simp only [pow_succ, pow_zero]; group
        _ = 1 := h4
        _ = u⁻¹ * u := (inv_mul_cancel u).symm
    have he : v = b * u⁻¹ * b⁻¹ := by
      have hmul : v = x * u ^ 2 := inv_mul_eq_iff_eq_mul.mp hc
      calc
        v = (b * u * b⁻¹) * u ^ 2 := hmul
        _ = b * u * (b⁻¹ * u ^ 2) := by group
        _ = b * u * (u ^ 2 * b⁻¹) := by rw [mem_center_iff.mp hu2Z b⁻¹]
        _ = b * (u * u ^ 2) * b⁻¹ := by group
        _ = b * u⁻¹ * b⁻¹ := by rw [huv]
    exact hflip.trans (he.symm ▸ isConj_iff.mpr ⟨b, rfl⟩)

/-- The multiplier bounds remove any extra assumption on the center order. -/
theorem product_class_lifts_isConj_of_pair {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (e : (E ⧸ center E) ≃* Carrier)
    (r : Carrier) (hr : IsConj t r) (hrt : IsConj t (t * r))
    (u v : E) (hu : HSLocal.modelMap e u = t)
    (hv : IsConj t (HSLocal.modelMap e v)) : IsConj u v := by
  let f := HSLocal.modelMap e
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = center E := HSLocal.modelMap_ker e
  have hcard : Nat.card f.ker ≤ 2 :=
    Theory.SpecificGroups.J2HSMultipliers.HS.card_kernel_le_two_of_not_four_dvd f hf hker.le
      (Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.not_four_dvd_card_kernel f hf hker.le
        (Theory.SpecificGroups.J2HSMultipliers.HS.kernel_isPGroup f hf hker.le))
  by_cases h2 : Nat.card (center E) = 2
  · exact product_class_lifts_isConj e h2 r hr hrt u v hu hv
  · have hZ : center E = ⊥ := card_eq_one.mp (by
      rw [hker] at hcard
      have hp : 0 < Nat.card (center E) := Nat.card_pos
      omega)
    have hfI : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp (hker.trans hZ)
    obtain ⟨g, hg⟩ := isConj_iff.mp hv
    obtain ⟨b, hb⟩ := hf g
    exact isConj_iff.mpr ⟨b, hfI (by rw [map_mul, map_mul, map_inv, hb, hu]; exact hg)⟩

private theorem ambient_isConj_of_inner_lifts {E G : Type*} [Group E] [Group G]
    (a : MulAut E) (f : E →* G) (s : G)
    (hact : ∀ x, f (a x) = s * f x * s⁻¹)
    (u k : E) (ha : a = MulAut.conj u) (hconj : IsConj u (u * k)) :
    IsConj s (s * f k) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  let c := (f u)⁻¹ * s
  have hc (x : E) : Commute c (f x) := by
    have hh := hact x
    rw [ha, MulAut.conj_apply, map_mul, map_mul, map_inv] at hh
    have hh' : s * f x = f u * f x * (f u)⁻¹ * s := (mul_inv_eq_iff_eq_mul.mp hh.symm)
    change ((f u)⁻¹ * s) * f x = f x * ((f u)⁻¹ * s)
    calc
      ((f u)⁻¹ * s) * f x = (f u)⁻¹ * (s * f x) := by group
      _ = (f u)⁻¹ * (f u * f x * (f u)⁻¹ * s) := by rw [hh']
      _ = f x * ((f u)⁻¹ * s) := by group
  have hs : s = f u * c := by dsimp [c]; group
  have hg' := congrArg f hg
  simp only [map_mul, map_inv] at hg'
  refine isConj_iff.mpr ⟨f g, ?_⟩
  calc
    f g * s * (f g)⁻¹ = f g * (f u * c) * (f g)⁻¹ := by rw [hs]
    _ = f g * f u * (c * (f g)⁻¹) := by group
    _ = f g * f u * ((f g)⁻¹ * c) := by rw [(hc g).inv_right.eq]
    _ = (f u * f k) * c := by rw [← mul_assoc, hg']
    _ = (f u * c) * f k := by rw [mul_assoc, ← (hc k).eq, ← mul_assoc]
    _ = s * f k := by rw [← hs]

private theorem component_image_order {E : Type*} [Group E]
    (e : (E ⧸ center E) ≃* Carrier) (a : MulAut E)
    (hmark : MulAut.congr e (quotientAut (center E) a) = MulAut.conj t)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (hBZ : center B = ⊥) (k : B) (hk : orderOf k = 2) :
    ∃ (C : Subgroup (MulAut.conj t).fixedSubgroup),
      IsComponent (MulAut.conj t).fixedSubgroup C ∧
      ∃ v : C, orderOf v = 2 ∧
        ((v : (MulAut.conj t).fixedSubgroup) : Carrier) =
          HSLocal.modelMap e ((k : a.fixedSubgroup) : E) := by
  let f := HSLocal.modelMap e
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hc : f.ker ≤ center E := (HSLocal.modelMap_ker e).le
  have he (x : E) : f (a x) = (MulAut.conj t) (f x) := by
    change e (QuotientGroup.mk' (center E) (a x)) =
      (MulAut.conj t) (e (QuotientGroup.mk' (center E) x))
    rw [← hmark]
    exact (MulAut.centralQuotientAction_apply e a x).symm
  let j := MulAut.fixedSubgroupMap a (MulAut.conj t) f he
  have hC := (MulAut.fixedSubgroupMap_component_of_center_eq_bot a
    (MulAut.conj t) f hf hc he B hB hBZ).1
  have hi : Function.Injective (j.subgroupMap B) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hz : x ∈ center B := by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      apply Subtype.ext
      have hfx : f ((x : a.fixedSubgroup) : E) = 1 :=
        congrArg (fun z : B.map j => ((z : (MulAut.conj t).fixedSubgroup) : Carrier)) hx
      exact mem_center_iff.mp (hc hfx) ((y : a.fixedSubgroup) : E)
    simpa only [hBZ] using hz
  exact ⟨B.map j, hC, j.subgroupMap B k,
    (orderOf_injective (j.subgroupMap B) hi k).trans hk, rfl⟩

/-- Exact marked product fusion transfers from the perfect cover to its
original ambient actor, without requiring that actor to lie in the cover. -/
theorem ambient_cover_twist_isConj {E G : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] [Group G]
    (e : (E ⧸ center E) ≃* Carrier) (a : MulAut E)
    (hmark : MulAut.congr e (quotientAut (center E) a) = MulAut.conj t)
    (r : Carrier) (hr : IsConj t r) (hrt : IsConj t (t * r))
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (hBZ : center B = ⊥) (k : B) (hk : orderOf k = 2)
    (f : E →* G) (s : G) (hact : ∀ x, f (a x) = s * f x * s⁻¹) :
    IsConj s (s * f ((k : a.fixedSubgroup) : E)) := by
  obtain ⟨C, hC, v, hv, he⟩ := component_image_order e a hmark B hB hBZ k hk
  have hprod : IsConj t (t * HSLocal.modelMap e ((k : a.fixedSubgroup) : E)) := by
    rw [← he]
    exact marked_component_twist_isConj (MulEquiv.refl Carrier) (MulAut.conj t)
      (fun _ => rfl) C hC v hv
  obtain ⟨u, hu⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective _)) t
  have hu' : HSLocal.modelMap e u = t := hu
  have ha : a = MulAut.conj u := by
    apply MulAut.centralQuotientAction_injective e
    rw [MulAut.centralQuotientAction_conj]
    exact hmark.trans (congrArg MulAut.conj hu.symm)
  have hconj : IsConj u (u * ((k : a.fixedSubgroup) : E)) :=
    product_class_lifts_isConj_of_pair e r hr hrt u _ hu'
      (by rw [map_mul, hu']; exact hprod)
  exact ambient_isConj_of_inner_lifts a f s hact u _ ha hconj


open ComponentRefinement ComponentSelection
variable {G : Type*} [Group G] [Finite G]
variable {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The original crossing equation excludes the HS quotient row directly. -/
theorem source_hs_crossing_false
    (c : MathieuSourceSetup H K M S z)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (s i : G) (hs : orderOf s = 2) (hsC : s ∈ twoCore H)
    (hsZ : s ∈ centerIn ((S : Subgroup H).map H.subtype))
    (X : Subgroup (centralizer ({i} : Set G)))
    (hX : IsComponent (centralizer ({i} : Set G)) X)
    (e : (X ⧸ center X) ≃* Carrier) (a : MulAut X)
    (hact : ∀ x : X, ((a x : centralizer ({i} : Set G)) : G) =
      s * ((x : centralizer ({i} : Set G)) : G) * s⁻¹)
    (hmark : MulAut.congr e (quotientAut (center X) a) = MulAut.conj t)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eB : B ≃* AlternatingSix.ShadowLocal.A6)
    (k : B) (hk : orderOf k = 2)
    (hcross : z = s * ((((k : a.fixedSubgroup) : X) : centralizer ({i} : Set G)) : G)) :
    False := by
  let : IsQuasisimple X := hX.2
  have hBZ : center B = ⊥ := by
    apply bot_unique
    intro b hb
    have hez : eB b ∈ center AlternatingSix.ShadowLocal.A6 :=
      (centerCongr eB ⟨b, hb⟩).property
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hez
    exact mem_bot.mpr (eB.injective (hez.trans eB.map_one.symm))
  obtain ⟨r, _, _, _, hr, hrt⟩ := HSProductTwist.exists_commuting_product_class_pair
  have hf := ambient_cover_twist_isConj e a hmark r hr hrt B hB hBZ k hk
    ((centralizer ({i} : Set G)).subtype.comp X.subtype) s hact
  have hn := (MathieuSourceSetup.central_core_involution_centralizer c hgen s hs hsC hsZ).2.2.2.2
  exact hn (hcross.symm ▸ hf)

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.FullA6.HS