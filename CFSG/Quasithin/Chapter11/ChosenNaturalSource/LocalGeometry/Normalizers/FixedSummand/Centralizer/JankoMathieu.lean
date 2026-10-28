module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.OrdinaryLocal
public import Theory.Mathieu.M24.Properties.CubicElementary
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu

/-!
# Excluding the Mathieu local in the ordinary field-four J4 row

Native cubic fusion in M24 gives zero or six fixed points on the 24-point
set. In the first case every commuting involution is fixed-point-free,
so a two-subgroup of the centralizer acts freely and its order divides 24.
In the second case its action on the six fixed points is faithful: the
kernel cannot contain an involution. Thus 64 never divides a cubic
centralizer order.

A central cubic in a quotient through a two-group kernel lifts to a cubic
whose centralizer still covers the quotient, by coprime fixed-fiber counting.
This excludes the full SL3(4) quotient in every M24 subgroup. The literal
quotient map of J4's Mathieu local has elementary two-kernel, so the same
obstruction excludes every conjugate of that local for the actual projected
C.2.8 residual. The application keeps the full W and requires no ambient
Sylow containment or replacement of the natural action.

The remaining ordinary J4 placement and the degree-two 11.1.5 assembly
remain with qt-d-1222-natural-point-fixed-summand. Source applies this
exclusion to B=L; the shared covering statement is also available to
qt-d-1222-natural-odd-kernel-normalizer. Earlier-source discharge remains
with qt-d-1222-natural-normalizer-source.

Source: Aschbacher--Smith, C.3.5 and the local inspections on printed
pp.611--612,622. The native cubic/involution fusion and the J4 max1 words
retain their ATLAS attribution in the imported model modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M24ChapterHStabilizers
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
open scoped BigOperators

private theorem involution_fixed_card (t : M24) (ht : orderOf t = 2) :
    (fixedPoints t).card = 0 ∨ (fixedPoints t).card = 8 := by
  rcases M24InvolutionCentralizers.involution_classes t ht with h | h
  · exact Or.inr (m24Blocks_card _ (class2A_fixed_octad h))
  · exact Or.inl (by rw [class2B_fixed_empty h, Finset.card_empty])

private theorem cubic_fixed_card (x : M24) (hx : orderOf x = 3) :
    (fixedPoints x).card = 0 ∨ (fixedPoints x).card = 6 := by
  obtain ⟨i, hi⟩ := M24OddClasses.order_three_coverage x hx
  rw [fixedPoints_card_eq_of_isConj hi]
  have h : ∀ i : Fin 2,
      (fixedPoints (M24OddClasses.cubicRepresentative i)).card = 0 ∨
        (fixedPoints (M24OddClasses.cubicRepresentative i)).card = 6 := by
    decide +kernel
  exact h i

private theorem fixed_stable (x t : M24) (h : Commute x t) (a : Fin 24) :
    x.val a ∈ fixedPoints t ↔ a ∈ fixedPoints t := by
  rw [mem_fixedPoints, mem_fixedPoints]
  change t.val (x.val a) = x.val a ↔ t.val a = a
  have he : t.val (x.val a) = x.val (t.val a) :=
    congrArg (fun z : M24 => z.val a) h.eq.symm
  rw [he]
  exact x.val.injective.eq_iff

private def restricted (x t : M24) (h : Commute x t) : Equiv.Perm (fixedPoints t) :=
  x.val.subtypePerm (fixed_stable x t h)

private theorem fixed_intersection_mod_three (x t : M24) (hx : orderOf x = 3)
    (h : Commute x t) :
    (fixedPoints t).card % 3 = (fixedPoints t ∩ fixedPoints x).card % 3 := by
  classical
  let σ := restricted x t h
  have hp : σ ^ 3 ^ 1 = 1 := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    change x.val (x.val (x.val a.val)) = a.val
    have he := congrArg (fun z : M24 => z.val a.val) (pow_orderOf_eq_one x)
    rw [hx] at he
    simpa only [pow_succ, pow_zero, Subgroup.coe_mul, Equiv.Perm.mul_apply,
      Subgroup.coe_one, Equiv.Perm.one_apply] using he
  have hm (a : fixedPoints t) : a ∈ σ.supportᶜ ↔ a.val ∈ fixedPoints x := by
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, mem_fixedPoints]
    change (⟨x.val a.val, _⟩ : fixedPoints t) = a ↔ x.val a.val = a.val
    exact Subtype.ext_iff
  let e : ↥(σ.supportᶜ) ≃ ↥(fixedPoints t ∩ fixedPoints x) := {
    toFun a := ⟨a.val.val, Finset.mem_inter.mpr ⟨a.val.property, (hm a.val).mp a.property⟩⟩
    invFun a := ⟨⟨a.val, (Finset.mem_inter.mp a.property).1⟩,
      (hm _).mpr (Finset.mem_inter.mp a.property).2⟩
    left_inv a := by cases a; rfl
    right_inv a := by cases a; rfl }
  have hc : σ.supportᶜ.card = (fixedPoints t ∩ fixedPoints x).card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr e
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 3) (n := 1) hp
  rw [hc, Fintype.card_coe] at hmod
  exact hmod.symm

private theorem fixed_free_involution (x : M24) (hx : orderOf x = 3)
    (hfree : (fixedPoints x).card = 0) (t : M24) (ht : orderOf t = 2)
    (h : Commute x t) : fixedPoints t = ∅ := by
  have hm := fixed_intersection_mod_three x t hx h
  rw [Finset.card_eq_zero.mp hfree, Finset.inter_empty, Finset.card_empty] at hm
  rcases involution_fixed_card t ht with ht | ht
  · exact Finset.card_eq_zero.mp ht
  · rw [ht] at hm
    norm_num at hm

private theorem six_fixed_faithful_involution (x : M24) (hx : orderOf x = 3)
    (hfix : (fixedPoints x).card = 6) (t : M24) (ht : orderOf t = 2)
    (h : Commute x t) (hsub : fixedPoints x ⊆ fixedPoints t) : False := by
  have hm := fixed_intersection_mod_three x t hx h
  rw [Finset.inter_eq_right.mpr hsub, hfix] at hm
  have hle := Finset.card_le_card hsub
  rcases involution_fixed_card t ht with ht | ht <;> omega

private theorem free_card_dvd {U X : Type*} [Group U] [Finite U] [Finite X]
    [MulAction U X] [IsCancelSMul U X] : Nat.card U ∣ Nat.card X := by
  classical
  let : Fintype U := Fintype.ofFinite U
  let : Fintype X := Fintype.ofFinite X
  let : ∀ u : U, Fintype (MulAction.fixedBy X u) := fun _ => Fintype.ofFinite _
  have hsum : (∑ u : U, Nat.card (MulAction.fixedBy X u)) = Nat.card X := by
    rw [Finset.sum_eq_single 1]
    · simp [MulAction.fixedBy_one_eq_univ]
    · intro u _ hu
      have he : MulAction.fixedBy X u = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro a ha
        exact hu (IsCancelSMul.eq_one_of_smul ((MulAction.mem_fixedBy).mp ha))
      simp [he]
    · simp
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group U X
  have he : Nat.card X = Nat.card (Quotient (MulAction.orbitRel U X)) * Nat.card U := by
    rw [← hsum]
    simpa only [Nat.card_eq_fintype_card] using hb
  rw [he]
  exact dvd_mul_left _ _


private theorem two_group_free_of_involutions
    {P X : Type*} [Group P] [Finite P] [MulAction P X]
    (hp : IsPGroup 2 P)
    (hi : ∀ u : P, orderOf u = 2 → ∀ x : X, u • x ≠ x) :
    IsCancelSMul P X := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro u x hx
  by_contra hu
  let A := MulAction.stabilizer P x
  have ha : IsPGroup 2 A := hp.to_subgroup A
  have : Nontrivial A := ⟨⟨⟨u,hx⟩,1,fun he => hu (congrArg Subtype.val he)⟩⟩
  have hd : 2 ∣ Nat.card A := by
    rcases ha.card_eq_or_dvd with he | hd
    · exact (ne_of_gt Finite.one_lt_card he).elim
    · exact hd
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 hd
  exact hi t ((orderOf_coe t).trans ht) x t.property

/-- A cubic centralizer in the native Mathieu group has two-part below 64. -/
theorem mathieu_cubic_centralizer_not_sixtyFour (x : M24) (hx : orderOf x = 3) :
    ¬ 64 ∣ Nat.card (centralizer ({x} : Set M24)) := by
  classical
  let C := centralizer ({x} : Set M24)
  let P : Sylow 2 C := Classical.choice inferInstance
  have hc (u : P) : Commute x u.val.val :=
    (mem_centralizer_singleton_iff.mp u.val.property).symm
  have ho (u : P) (hu : orderOf u = 2) : orderOf u.val.val = 2 :=
    (orderOf_coe u.val).trans ((orderOf_coe u).trans hu)
  intro hd
  have h64 : 64 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card (n := 6) hd
  rcases cubic_fixed_card x hx with hfree | hfix
  · let : IsCancelSMul P (Fin 24) := two_group_free_of_involutions P.isPGroup' (by
      intro u hu a ha
      have he := fixed_free_involution x hx hfree u.val.val (ho u hu) (hc u)
      have hm : a ∈ fixedPoints u.val.val := (mem_fixedPoints _ _).mpr ha
      rw [he] at hm
      exact Finset.notMem_empty _ hm)
    have hb := h64.trans (free_card_dvd (U := P) (X := Fin 24))
    norm_num at hb
  · let f : P →* Equiv.Perm (fixedPoints x) := {
      toFun u := restricted u.val.val x (hc u).symm
      map_one' := by ext a; rfl
      map_mul' u v := by ext a; rfl }
    have hf : Function.Injective f := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      by_contra hne
      have : Nontrivial f.ker := (nontrivial_iff_ne_bot _).mpr hne
      have hk : IsPGroup 2 f.ker := P.isPGroup'.to_subgroup f.ker
      have h2 : 2 ∣ Nat.card f.ker := by
        rcases hk.card_eq_or_dvd with he | hd
        · exact (ne_of_gt Finite.one_lt_card he).elim
        · exact hd
      obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 2 h2
      apply six_fixed_faithful_involution x hx hfix u.val.val.val
        (ho u.val ((orderOf_coe u).trans hu)) (hc u.val)
      intro a ha
      have he := Equiv.congr_fun (MonoidHom.mem_ker.mp u.property) ⟨a,ha⟩
      exact (mem_fixedPoints _ _).mpr (congrArg Subtype.val he)
    have hb := h64.trans (card_dvd_of_injective f hf)
    rw [Nat.card_perm,show Nat.card (fixedPoints x) = 6 by
      simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hfix] at hb
    norm_num at hb

private theorem cubic_centralizer_surjective
    {A Q : Type*} [Group A] [Finite A] [Group Q]
    (f : A →* Q) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (c : A) (hc : orderOf c = 3) (hfc : f c ∈ center Q) :
    Function.Surjective (f.comp (centralizer ({c} : Set A)).subtype) := by
  intro y
  obtain ⟨a,ha⟩ := hf y
  let F := {b : A // f b = y}
  let e : f.ker ≃ F := {
    toFun k := ⟨a*k,by rw [map_mul,MonoidHom.mem_ker.mp k.property,mul_one,ha]⟩
    invFun b := ⟨a⁻¹*b,by rw [MonoidHom.mem_ker,map_mul,map_inv,b.property,ha,inv_mul_cancel]⟩
    left_inv k := Subtype.ext (by simp)
    right_inv b := Subtype.ext (by simp) }
  let C := zpowers c
  have hcp : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hc]; rfl)
  have hcc : C.map f ≤ center Q := by
    exact (map_le_iff_le_comap).mpr (zpowers_le.mpr hfc)
  let : MulAction C F := {
    smul t b := ⟨(t : A)*b*(t : A)⁻¹, by
      rw [map_mul,map_mul,map_inv,
        (mem_center_iff.mp (hcc (mem_map_of_mem f t.property)) (f b)).symm]
      simpa only [mul_assoc,mul_inv_cancel,mul_one] using b.property⟩
    one_smul b := Subtype.ext (by
      change (1 : A) * b.val * (1 : A)⁻¹ = b.val
      simp)
    mul_smul t u b := Subtype.ext (by
      change ((t : A) * (u : A)) * b.val * ((t : A) * (u : A))⁻¹ =
        (t : A) * ((u : A) * b.val * (u : A)⁻¹) * (t : A)⁻¹
      simp only [mul_inv_rev,mul_assoc]) }
  have hnot : ¬ 3 ∣ Nat.card F := by
    rw [←Nat.card_congr e]
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (by decide : ¬ 3 ∣ 2).imp (Nat.prime_three.dvd_of_dvd_pow)
  obtain ⟨b,hb⟩ := hcp.nonempty_fixed_point_of_prime_not_dvd_card F hnot
  refine ⟨⟨b,mem_centralizer_singleton_iff.mpr ?_⟩,b.property⟩
  have hh := congrArg Subtype.val (hb (⟨c,mem_zpowers c⟩ : C))
  change c * b.val * c⁻¹ = b.val at hh
  exact ((mul_inv_eq_iff_eq_mul).mp hh).symm


/-- A Mathieu subgroup has no two-kernel quotient with a central cubic
and two-part divisible by 64. -/
theorem mathieu_no_cubic_center_quotient
    (A : Subgroup M24) {Q : Type*} [Group Q] [Finite Q]
    (f : A →* Q) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hz : 3 ∣ Nat.card (center Q)) (h64 : 64 ∣ Nat.card Q) : False := by
  let Z := (center Q).comap f
  have hdiv : 3 ∣ Nat.card Z := hz.trans
    (card_dvd_of_surjective (f.subgroupComap (center Q))
      (f.subgroupComap_surjective_of_surjective (center Q) hf))
  obtain ⟨c,hc⟩ := exists_prime_orderOf_dvd_card' (G := Z) 3 hdiv
  have hcA : orderOf (c : A) = 3 := (Subgroup.orderOf_coe c).trans hc
  have hsur := cubic_centralizer_surjective f hf hk (c : A) hcA c.property
  have hd : 64 ∣ Nat.card (centralizer ({(c : A)} : Set A)) :=
    h64.trans (card_dvd_of_surjective _ hsur)
  let j : centralizer ({(c : A)} : Set A) →*
      centralizer ({((c : A) : M24)} : Set M24) := {
    toFun b := ⟨b.val.val,mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp b.property))⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro b d he
    exact Subtype.ext (Subtype.ext (congrArg
      (fun v : centralizer ({((c : A) : M24)} : Set M24) => (v : M24)) he))
  exact mathieu_cubic_centralizer_not_sixtyFour c.val.val
    ((Subgroup.orderOf_coe c.val).trans hcA) (hd.trans (card_dvd_of_injective j hj))

open Representation CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open WeakClosure.Generation

/-- The full SL3(4) quotient cannot occur inside the native Mathieu group. -/
theorem mathieu_no_full_linear_three_quotient
    (F : BinaryField) (hF : F.degree = 2) (A : Subgroup M24)
    (e : (A ⧸ pCore 2 A) ≃* SL(3,F.Carrier)) : False := by
  apply mathieu_no_cubic_center_quotient A (QuotientGroup.mk' (pCore 2 A))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  · rw [Nat.card_congr (centerCongr e).toEquiv,Atlas.ExceptionalSupport.card_sl_center]
    norm_num [F.card_eq,hF]
  · rw [Nat.card_congr e.toEquiv,OddNormalizer.linear_three_order]
    norm_num [F.card_eq,hF]

open Janko4 Janko4.Cardinality Janko4.LocalStructure
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
local notation "J" => max1Subgroup matrixA_mul_self matrixB_pow_four

/-- The same obstruction survives the actual elementary kernel of J4 max1. -/
theorem janko_mathieu_local_no_full_linear_three_quotient
    (F : BinaryField) (hF : F.degree = 2) (A : Subgroup J)
    (e : (A ⧸ pCore 2 A) ≃* SL(3,F.Carrier)) : False := by
  let q := (localQuotientEquivM24 matrixA_mul_self matrixB_pow_four).toMonoidHom.comp
    (QuotientGroup.mk' (localKernel matrixA_mul_self matrixB_pow_four))
  let f := q.comp A.subtype
  have hq : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _
      (localQuotientEquivM24 matrixA_mul_self matrixB_pow_four).injective,
      QuotientGroup.ker_mk']
    exact (localKernel_elementary matrixA_mul_self matrixB_pow_four).isPGroup
  have hk : IsPGroup 2 f.ker := hq.comap_of_injective A.subtype A.subtype_injective
  let a := f.rangeRestrict.quotientPCoreEquivOfSurjective f.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hk)
  exact mathieu_no_full_linear_three_quotient F hF f.range (a.symm.trans e)

/-- No conjugate of the actual Mathieu local contains a field-four residual
with its full original quotient. No Sylow-containment premise is needed. -/
theorem janko_cover_not_le_mathieu_conjugate
    (F : BinaryField) (hF : F.degree = 2) (X : Subgroup Janko4.Model)
    (e : (X ⧸ pCore 2 X) ≃* SL(3,F.Carrier)) (g : Janko4.Model) :
    ¬ X ≤ (J : Subgroup Janko4.Model).map (MulAut.conj g).toMonoidHom := by
  intro hX
  let t := MulAut.conj g⁻¹
  let Y := X.map t.toMonoidHom
  have hY : Y ≤ J := by
    have hh := map_mono (f := t.toMonoidHom) hX
    have ht : t.toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id _ := by
      ext z
      change g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z
      group
    rwa [map_map,ht,map_id] at hh
  let A := Y.subgroupOf J
  let a : A ≃* X := (subgroupOfEquivOfLe hY).trans (t.subgroupMap X).symm
  let b := a.toMonoidHom.quotientPCoreEquivOfSurjective a.surjective
    (by rw [a.toMonoidHom.ker_eq_bot a.injective]; exact IsPGroup.of_subsingleton 2 _)
  exact janko_mathieu_local_no_full_linear_three_quotient F hF A (b.trans e)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- In the shared C.2.8 configuration the literal residual image avoids
every conjugate of the actual Mathieu local of J4, with W unchanged. -/
theorem c28_covering_jankoFour_avoids_mathieu
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : IsComponent H K)
    (ek : K ⧸ center K ≃* Janko4.Model) (g : Janko4.Model) :
    ¬ (ordinaryCoverProjection h K hK).range.map ek.toMonoidHom ≤
      (J : Subgroup Janko4.Model).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨_,hf,⟨a⟩,_⟩ := c28_covering_ordinary_jankoFour D S h hBL hc hVB e K hK
  let t := ek.subgroupMap (ordinaryCoverProjection h K hK).range
  let q := t.toMonoidHom.quotientPCoreEquivOfSurjective t.surjective
    (by rw [t.toMonoidHom.ker_eq_bot t.injective]; exact IsPGroup.of_subsingleton 2 _)
  exact janko_cover_not_le_mathieu_conjugate S.field hf _
    (q.symm.trans ((ordinaryCoverQuotient h K hK).symm.trans (e.trans a))) g

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
