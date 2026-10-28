module
public import Theory.SpecificGroups.Rudvalis.Model.CubicElementary.Centralizers
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.Quotient
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.OrdinaryProjection

/-!
# The ordinary Rudvalis row cannot have the full natural quotient

In the native Rudvalis action, a cubic commuting with an involution fixes
ten points, and every such involution fixes two of those ten points.
For a two-group acting with this pattern, a central involution has a
fixed pair. The kernel on that pair acts freely on the other eight
points, so the two-group has order at most sixteen. Thus the centralizer
of a cubic has order not divisible by 64.

A surjection with two-group kernel onto a group with a central cubic
lifts a cubic in the central preimage. The coprime fixed-fiber argument
makes its centralizer cover the whole quotient. Full SL3(4) has order
divisible by 64 and center of order three, giving the contradiction.
The source application uses the literal covering residual projection;
W remains arbitrary. J₄ and the final 11.1.5 assembly remain with
qt-d-1222-natural-point-fixed-summand.

Source: Aschbacher--Smith C.3.5, p.150, and local inspection on pp.611
and 622. The imported native ATLAS words, permutation action and checked
involution/cubic incidence certificates retain their attribution.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer

private theorem two_group_ten_two_bound
    {P X : Type*} [Group P] [Finite P] [Finite X] [MulAction P X]
    (hP : IsPGroup 2 P) (hX : Nat.card X = 10)
    (hi : ∀ u : P, orderOf u = 2 → Nat.card (MulAction.fixedBy X u) = 2) :
    Nat.card P ≤ 16 := by
  classical
  by_cases htr : Subsingleton P
  · let := htr
    simp only [Nat.card_unique]
    omega
  have : Nontrivial P := not_subsingleton_iff_nontrivial.mp htr
  have : Nontrivial (center P) := hP.center_nontrivial
  have hc2 : 2 ∣ Nat.card (center P) :=
    by
      rcases (hP.to_subgroup (center P)).card_eq_or_dvd with he | hd
      · exact (ne_of_gt Finite.one_lt_card he).elim
      · exact hd
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center P) 2 hc2
  have hz2 : orderOf (z : P) = 2 := (Subgroup.orderOf_coe z).trans hz
  let Y := MulAction.fixedBy X (z : P)
  have hY : Nat.card Y = 2 := hi z hz2
  have hcomm (p : P) : (z : P) * p = p * z := (mem_center_iff.mp z.property p).symm
  let : MulAction P Y := {
    smul p x := ⟨p • x.val, by
      change (z : P) • (p • x.val) = p • x.val
      rw [←mul_smul,hcomm p,mul_smul,x.property]⟩
    one_smul x := Subtype.ext (one_smul P x.val)
    mul_smul p q x := Subtype.ext (mul_smul p q x.val) }
  let f : P →* Equiv.Perm Y := MulAction.toPermHom P Y
  let Q := f.ker
  have hQfix (q : Q) (x : Y) : (q : P) • x.val = x.val :=
    congrArg Subtype.val (congrArg (fun e : Equiv.Perm Y => e x) q.property)
  have hQbound : Nat.card Q ≤ 8 := by
    let Z := {x : X // x ∉ MulAction.fixedBy X (z : P)}
    have hZ : Nat.card Z = 8 := by
      have hh := Nat.card_congr (Equiv.sumCompl (fun x : X => x ∈ MulAction.fixedBy X (z : P)))
      rw [Nat.card_sum] at hh
      change Nat.card Y + Nat.card Z = Nat.card X at hh
      omega
    have : Nonempty Z := Finite.card_pos_iff.mp (by omega : 0 < Nat.card Z)
    let y : Z := Classical.choice inferInstance
    let j : Q → Z := fun q => ⟨(q : P) • y.val, by
      intro he
      apply y.property
      have hh := congrArg (fun x : X => (q : P)⁻¹ • x) he
      change (z : P) • y.val = y.val
      simpa only [←mul_smul,hcomm, mul_assoc,inv_mul_cancel_left,inv_mul_cancel,one_smul] using hh⟩
    have hfree : ∀ q : Q, (q : P) • y.val = y.val → q = 1 := by
      intro q hq
      let A := MulAction.stabilizer Q y.val
      have hA : IsPGroup 2 A := (hP.to_subgroup Q).to_subgroup A
      by_contra hq1
      have : Nontrivial A := ⟨⟨⟨q,hq⟩,1,fun he => hq1 (congrArg Subtype.val he)⟩⟩
      have hdiv : 2 ∣ Nat.card A := by
        rcases hA.card_eq_or_dvd with he | hd
        · exact (ne_of_gt Finite.one_lt_card he).elim
        · exact hd
      obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 hdiv
      have hu2 : orderOf ((u : Q) : P) = 2 :=
        (Subgroup.orderOf_coe (u : Q)).trans ((Subgroup.orderOf_coe u).trans hu)
      let e : Y ⊕ Unit → MulAction.fixedBy X ((u : Q) : P) :=
        fun a => match a with
        | Sum.inl x => ⟨x.val,hQfix u.val x⟩
        | Sum.inr _ => ⟨y.val,u.property⟩
      have he : Function.Injective e := by
        intro a b hab
        cases a with
        | inl a =>
          cases b with
          | inl b => exact congrArg Sum.inl (Subtype.ext (congrArg (fun v : MulAction.fixedBy X ((u : Q) : P) => (v : X)) hab))
          | inr b =>
            have hy : y.val ∈ MulAction.fixedBy X (z : P) :=
              (congrArg (fun v : MulAction.fixedBy X ((u : Q) : P) => (v : X)) hab) ▸ a.property
            exact (y.property hy).elim
        | inr a =>
          cases b with
          | inl b =>
            have hy : y.val ∈ MulAction.fixedBy X (z : P) :=
              (congrArg (fun v : MulAction.fixedBy X ((u : Q) : P) => (v : X)) hab).symm ▸ b.property
            exact (y.property hy).elim
          | inr b => exact congrArg Sum.inr (Subsingleton.elim _ _)
      have hb := Nat.card_le_card_of_injective e he
      rw [Nat.card_sum,hY,Nat.card_unique,hi _ hu2] at hb
      omega
    have hj : Function.Injective j := by
      intro a b hab
      have he : ((b⁻¹ * a : Q) : P) • y.val = y.val := by
        change ((b : P)⁻¹ * (a : P)) • y.val = y.val
        rw [mul_smul]
        have hab' : (a : P) • y.val = (b : P) • y.val := congrArg Subtype.val hab
        rw [hab']
        exact inv_smul_smul _ _
      have hh := hfree (b⁻¹*a) he
      exact (inv_mul_eq_one.mp hh).symm
    exact (Nat.card_le_card_of_injective j hj).trans_eq hZ
  have hf : Nat.card f.range ≤ 2 := by
    have hh : Nat.card (Equiv.Perm Y) = 2 := by
      rw [Nat.card_perm,hY]
      decide
    exact (Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective).trans_eq hh
  have hh := f.ker.card_mul_index
  rw [index_ker] at hh
  calc
    Nat.card P = Nat.card Q * Nat.card f.range := hh.symm
    _ ≤ 8 * 2 := Nat.mul_le_mul hQbound hf
    _ = 16 := by decide


/-- The ten-two pattern bounds the two-part of the full cubic centralizer. -/
theorem rudvalis_cubic_centralizer_not_sixtyFour (x : Rudvalis.Model)
    (hx : orderOf x = 3) :
    ¬ 64 ∣ Nat.card (centralizer ({x} : Set Rudvalis.Model)) := by
  intro hd
  let C := centralizer ({x} : Set Rudvalis.Model)
  let P : Sylow 2 C := Classical.choice inferInstance
  have hdP : 2^6 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card hd
  have hPcard : 64 ≤ Nat.card P := Nat.le_of_dvd (Nat.card_pos (α := P)) hdP
  have : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hdiv : 2 ∣ Nat.card P := by
    rcases P.isPGroup'.card_eq_or_dvd with he | hh
    · omega
    · exact hh
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 hdiv
  have hu2 : orderOf ((u : C) : Rudvalis.Model) = 2 :=
    (Subgroup.orderOf_coe (u : C)).trans ((Subgroup.orderOf_coe u).trans hu)
  have hc (p : P) : Commute x ((p : C) : Rudvalis.Model) :=
    (mem_centralizer_singleton_iff.mp p.val.property).symm
  let Y := {i : Fin 4060 // x • i = i}
  let : MulAction P Y := {
    smul p i := ⟨((p : C) : Rudvalis.Model) • i.val, by
      rw [←mul_smul,(hc p).eq,mul_smul,i.property]⟩
    one_smul i := Subtype.ext (one_smul Rudvalis.Model i.val)
    mul_smul p q i := Subtype.ext (mul_smul ((p : C) : Rudvalis.Model)
      ((q : C) : Rudvalis.Model) i.val) }
  have hY : Nat.card Y = 10 :=
    (Rudvalis.CubicElementary.commuting_pair_counts x u.val.val hx hu2 (hc u)).1
  have hfixed (v : P) (hv : orderOf v = 2) : Nat.card (MulAction.fixedBy Y v) = 2 := by
    let e : MulAction.fixedBy Y v ≃
        {i : Fin 4060 // x • i = i ∧ ((v : C) : Rudvalis.Model) • i = i} := {
      toFun i := ⟨i.val.val,i.val.property,congrArg Subtype.val i.property⟩
      invFun i := ⟨⟨i.val,i.property.1⟩,Subtype.ext i.property.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    rw [Nat.card_congr e]
    exact (Rudvalis.CubicElementary.commuting_pair_counts x v.val.val hx
      ((Subgroup.orderOf_coe v.val).trans ((Subgroup.orderOf_coe v).trans hv)) (hc v)).2
  have hb := two_group_ten_two_bound P.isPGroup' hY hfixed
  omega

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

/-- No subgroup of the native Rudvalis carrier has a quotient with a central
cubic and two-part at least 64 through a two-group kernel. -/
theorem rudvalis_no_cubic_center_quotient
    (A : Subgroup Rudvalis.Model) {Q : Type*} [Group Q] [Finite Q]
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
      centralizer ({((c : A) : Rudvalis.Model)} : Set Rudvalis.Model) := {
    toFun b := ⟨b.val.val,mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp b.property))⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro b d he
    exact Subtype.ext (Subtype.ext (congrArg
      (fun v : centralizer ({((c : A) : Rudvalis.Model)} : Set Rudvalis.Model) =>
        (v : Rudvalis.Model)) he))
  exact rudvalis_cubic_centralizer_not_sixtyFour c.val.val
    ((Subgroup.orderOf_coe c.val).trans hcA) (hd.trans (card_dvd_of_injective j hj))


open Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open WeakClosure.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original C.2.8 covering quotient excludes the ordinary Ru row,
without identifying its full module W with the seed V. -/
theorem no_ordinary_rudvalis_field_four
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (hf : S.field.degree = 2)
    (a : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (K : Subgroup H) (hK : IsComponent H K)
    (ek : K ⧸ center K ≃* Rudvalis.Model) : False := by
  let f := ek.toMonoidHom.comp (ordinaryCoverProjection h K hK)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ ek.injective]
    exact (ordinaryCoverProjection_kernel h K hK).1
  let A := f.range
  let q := f.rangeRestrict.quotientPCoreEquivOfSurjective f.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hk)
  let t : (A ⧸ pCore 2 A) ≃* SL(3,S.field.Carrier) := q.symm.trans (e.trans a)
  apply rudvalis_no_cubic_center_quotient A (QuotientGroup.mk' (pCore 2 A))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  · rw [Nat.card_congr (centerCongr t).toEquiv,Atlas.ExceptionalSupport.card_sl_center]
    norm_num [S.field.card_eq,hf]
  · rw [Nat.card_congr t.toEquiv,OddNormalizer.linear_three_order]
    norm_num [S.field.card_eq,hf]

/-- In particular the actual B=L fixed-summand configuration has no Ru component. -/
theorem no_original_rudvalis_field_four
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {H M R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M L R W)
    (hf : S.field.degree = 2)
    (a : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (K : Subgroup H) (hK : IsComponent H K)
    (ek : K ⧸ center K ≃* Rudvalis.Model) : False :=
  no_ordinary_rudvalis_field_four D S h (MulEquiv.refl _) hf a K hK ek

/-- The common covering-residual source now has only the J4 row. The
actual full module W, relative placement and full SL3 quotient are retained. -/
theorem c28_covering_ordinary_jankoFour
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : IsComponent H K) :
    Nonempty (K ⧸ center K ≃* Janko4.Model) ∧ S.field.degree = 2 ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) ∧
      Nat.card (center (L ⧸ pCore 2 L)) = 3 := by
  obtain ⟨hm,hf,⟨a⟩,hz⟩ := OddNormalizer.ordinary_last_models D S h hBL hc hVB e K hK
  exact ⟨hm.resolve_right (fun er =>
    no_ordinary_rudvalis_field_four D S h e hf a K hK er.some),hf,⟨a⟩,hz⟩


/-- The remaining J4 inspection has the literal injective seed image of order
64 and the full projected actor quotient. It retains the unchanged W. -/
theorem c28_covering_jankoFour_seed
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : IsComponent H K) :
    let hVB' := hVB.trans (pCoreIn_le 2 B)
    Nonempty (K ⧸ center K ≃* Janko4.Model) ∧ S.field.degree = 2 ∧
      Function.Injective (ordinarySeedProjection h hVB' K hK) ∧
      Nat.card (ordinarySeedProjection h hVB' K hK).range = 64 ∧
      Nonempty (((ordinaryCoverProjection h K hK).range ⧸
        pCore 2 (ordinaryCoverProjection h K hK).range) ≃* SL(3,S.field.Carrier)) := by
  obtain ⟨hk,hf,⟨a⟩,_⟩ := c28_covering_ordinary_jankoFour D S h hBL hc hVB e K hK
  exact ⟨hk,hf,
    ordinarySeedProjection_injective D S h hBL hc (hVB.trans (pCoreIn_le 2 B)) hf a K hK,
    ordinarySeedProjection_card D S h hBL hc (hVB.trans (pCoreIn_le 2 B)) hf a K hK,
    ⟨(ordinaryCoverQuotient h K hK).symm.trans (e.trans a)⟩⟩


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
