module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ProductFusion.Centralizers.Reduction
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ProductFusion.Centralizers.QuotientTransport
public import BenderSuzuki.SE.StrongEmbeddingConjugacy


/-!
# Excluding the mixed central quotient in Aschbacher's argument

Suppose the nonidentity product u = ab of the two factor involutions is central.
The quotient by ⟨u⟩ embeds both factors. Its induction conclusion has a proper
intersection-generated subgroup, leaving the nested and exceptional alternatives.

For nested images, the original factors have a nontrivial intersection: otherwise
the smaller factor embeds as a set in the two cosets of the other factor. An
intersection involution and the common image of a and b lie in the normal closure
of the first image factor, in either nesting orientation. Strong embedding makes
them conjugate there. Lifting this conjugacy and applying strong closure would
identify the two distinct lifts a and b.

For the exceptional alternative, lift its specified fused conjugator, retaining
its actual action on the image factors. The order-two image intersection forces
this lift to interchange a and b. The preimage of the centralizer of their common
image contains the fixed Sylow and acts on {a,b}. Sylow conjugacy inside this
preimage, together with strong closure, instead forces any such fused element to
fix a and b. This already excludes the exceptional alternative without using its
additional dihedral or semidihedral model clause.

Source: M. Aschbacher, *On finite groups of component type*, Illinois J.
Math. 19 (1975), Lemma 3.4(g), printed p.96, DOI 10.1215/ijm/1256050927.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
universe u v
variable {G : Type u} [Group G] [Finite G] {Q : Type v} [Group Q]
variable {S : Sylow 2 G} {A B : Subgroup G}

private theorem card_two_cases {X : Type*} [One X] {x : X}
    (hc : Nat.card X = 2) (hx : x ≠ 1) (y : X) : y = 1 ∨ y = x := by
  obtain ⟨z, hz, hall⟩ := (Nat.card_eq_two_iff' (1 : X)).mp hc
  by_cases hy : y = 1
  · exact Or.inl hy
  · exact Or.inr ((hall y hy).trans (hall x hx).symm)

omit [Finite G] in
private theorem quotient_fiber {u x y : G} [N : (zpowers u).Normal]
    (hu : orderOf u = 2)
    (hxy : QuotientGroup.mk' (zpowers u) x = QuotientGroup.mk' (zpowers u) y) :
    x = y ∨ x = u * y := by
  have hm : x * y⁻¹ ∈ zpowers u := by
    apply (QuotientGroup.eq_one_iff (N := zpowers u) _).mp
    change QuotientGroup.mk' (zpowers u) (x * y⁻¹) = 1
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hc : Nat.card (zpowers u) = 2 := (Nat.card_zpowers u).trans hu
  have hne : (⟨u, mem_zpowers u⟩ : zpowers u) ≠ 1 := by
    intro he
    have : u = 1 := congrArg Subtype.val he
    simp [this] at hu
  rcases card_two_cases hc hne (⟨x * y⁻¹, hm⟩ : zpowers u) with he | he
  · exact Or.inl (mul_inv_eq_one.mp (congrArg Subtype.val he))
  · exact Or.inr (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he))

omit [Finite G] in
private theorem factor_commute (h : Hypotheses S A B)
    {x y : G} (hx : x ∈ A) (hy : y ∈ B) : Commute x y :=
  (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h.commute hx) y hy).symm

omit [Finite G] in
private theorem quotient_same_involution {a b : G} (ha : orderOf a = 2)
    [N : (zpowers (a * b)).Normal] :
    QuotientGroup.mk' (zpowers (a * b)) a = QuotientGroup.mk' (zpowers (a * b)) b := by
  let q := QuotientGroup.mk' (zpowers (a * b))
  have hprod : q a * q b = 1 := by
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff (N := zpowers (a * b)) _).mpr (mem_zpowers _)
  have ha2 : q a * q a = 1 := by
    rw [← map_mul]
    have h := (orderOf_eq_prime_iff.mp ha).1
    simpa only [pow_two, map_one] using congrArg q h
  exact (mul_left_cancel (hprod.trans ha2.symm)).symm

private theorem central_mixed_not_mem (m : MinimalCounterexample S A B)
    {a b : G} (hu : a * b ∈ center G) (hne : a * b ≠ 1) :
    a * b ∉ A ∧ a * b ∉ B :=
  ⟨fun hm => hne (m.central_factor_eq_one (Or.inl hm) hu),
   fun hm => hne (m.central_factor_eq_one (Or.inr hm) hu)⟩

omit [Finite G] in
private theorem central_mixed_commutes (h : Hypotheses S A B)
    {a b : G} (ha : a ∈ A) (hb : b ∈ B) (hu : a * b ∈ center G)
    {x : G} (hx : x ∈ (A : Set G) ∪ B) : Commute x a ∧ Commute x b := by
  have hxu : Commute x (a * b) := mem_center_iff.mp hu x
  rcases hx with hx | hx
  · have hxb := factor_commute h hx hb
    exact ⟨by simpa using (hxu.mul_right hxb.inv_right), hxb⟩
  · have hxa := (factor_commute h ha hx).symm
    refine ⟨hxa, ?_⟩
    simpa [mul_assoc] using hxa.inv_right.mul_right hxu

private theorem inf_ne_bot_of_quotient_nested {u : G} [(zpowers u).Normal]
    (hu : orderOf u = 2) (hz : u ∈ center G)
    {C D : Subgroup G} (hr : TwoRankAtLeastTwo C)
    (hle : C.map (QuotientGroup.mk' (zpowers u)) ≤
      D.map (QuotientGroup.mk' (zpowers u))) : C ⊓ D ≠ ⊥ := by
  classical
  intro hinf
  have htriv {x : G} (hx : x ∈ C) (hy : x ∈ D) : x = 1 :=
    mem_bot.mp (hinf ▸ (show x ∈ C ⊓ D from ⟨hx, hy⟩))
  have hcoset {x : G} (hx : x ∈ C) (hn : x ∉ D) : u⁻¹ * x ∈ D := by
    obtain ⟨y, hy, hxy⟩ := hle (mem_map_of_mem _ hx)
    rcases quotient_fiber hu hxy.symm with he | he
    · exact (hn (he ▸ hy)).elim
    · simpa [he] using hy
  let f : C → Bool := fun x => decide ((x : G) ∈ D)
  have hf : Function.Injective f := by
    intro x y he
    have hm : ((x : G) ∈ D) ↔ (y : G) ∈ D := by simpa only [f, decide_eq_decide] using he
    apply Subtype.ext
    by_cases hx : (x : G) ∈ D
    · exact (htriv x.property hx).trans (htriv y.property (hm.mp hx)).symm
    · have hy : (y : G) ∉ D := fun hy => hx (hm.mpr hy)
      have hD := D.mul_mem (hcoset x.property hx) (D.inv_mem (hcoset y.property hy))
      have hxy : (x : G) * (y : G)⁻¹ ∈ D := by
        have heq : (u⁻¹ * (x : G)) * (u⁻¹ * (y : G))⁻¹ = (x : G) * (y : G)⁻¹ := by
          have hc := mem_center_iff.mp hz ((x : G) * (y : G)⁻¹)
          calc
            _ = u⁻¹ * ((x : G) * (y : G)⁻¹) * u := by group
            _ = (x : G) * (y : G)⁻¹ := by rw [mul_assoc, hc, inv_mul_cancel_left]
        rwa [heq] at hD
      exact mul_inv_eq_one.mp (htriv (C.mul_mem x.property (C.inv_mem y.property)) hxy)
  have hc := Nat.card_le_card_of_injective f hf
  have hbool : Nat.card Bool = 2 := by simp
  rw [hbool] at hc
  obtain ⟨E, hE, _⟩ := hr
  have he := Subgroup.card_le_card_group E
  rw [hE] at he
  omega

private theorem exists_intersection_involution (h : Hypotheses S A B)
    (hne : A ⊓ B ≠ ⊥) : ∃ t ∈ A ⊓ B, orderOf t = 2 := by
  have hp : IsPGroup 2 (A ⊓ B : Subgroup G) := (S.isPGroup'.to_le h.left_le).to_inf_left
  have hd : 2 ∣ Nat.card (A ⊓ B : Subgroup G) := hp.card_eq_or_dvd.resolve_left
    (fun hc => hne (Subgroup.card_eq_one.mp hc))
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := (A ⊓ B : Subgroup G)) 2 hd
  exact ⟨t, t.property, by simpa using ht⟩

private theorem no_quotient_fusion_to_intersection
    (m : MinimalCounterexample S A B)
    (hc : IsStronglyClosedSet ((A : Set G) ∪ B) (S : Subgroup G) ⊤)
    {a b : G} (ha : a ∈ A) (hb : b ∈ B) (ha2 : orderOf a = 2)
    (hb2 : orderOf b = 2) (hu : a * b ∈ center G) (hne : a * b ≠ 1)
    [(zpowers (a * b)).Normal] {t g : G} (ht : t ∈ A ⊓ B)
    (he : QuotientGroup.mk' (zpowers (a * b)) (g⁻¹ * a * g) =
      QuotientGroup.mk' (zpowers (a * b)) t) : False := by
  let q := QuotientGroup.mk' (zpowers (a * b))
  have hu2 := m.setup.mixed_orderOf ha hb ha2 hb2 hne
  have hun := central_mixed_not_mem m hu hne
  have huS : a * b ∈ S := (S : Subgroup G).mul_mem (m.setup.left_le ha) (m.setup.right_le hb)
  have hfix {x : G} (hx : x ∈ (A : Set G) ∪ B)
      (hxt : q (g⁻¹ * x * g) = q t) : g⁻¹ * x * g = t := by
    rcases quotient_fiber hu2 hxt with hh | hh
    · exact hh
    · have hs : g⁻¹ * x * g ∈ S := hh ▸
        (S : Subgroup G).mul_mem huS (m.setup.left_le ht.1)
      have hm := hc.2 x hx g (mem_top _) hs
      rw [hh] at hm
      rcases hm with hm | hm
      · exact (hun.1 (by simpa using A.mul_mem hm (A.inv_mem ht.1))).elim
      · exact (hun.2 (by simpa using B.mul_mem hm (B.inv_mem ht.2))).elim
  have ha' := hfix (Or.inl ha) he
  have hb' : g⁻¹ * b * g = t := hfix (Or.inr hb) (by
    rw [map_mul, map_mul, ← quotient_same_involution ha2]
    simpa only [map_mul] using he)
  have hab : a = b := by
    have hh := congrArg (fun x => g * x * g⁻¹) (ha'.trans hb'.symm)
    simpa [mul_assoc] using hh
  apply hne
  rw [hab]
  exact (pow_two b).symm.trans (orderOf_eq_prime_iff.mp hb2).1

private theorem no_nested_quotient
    (m : MinimalCounterexample S A B)
    (hc : IsStronglyClosedSet ((A : Set G) ∪ B) (S : Subgroup G) ⊤)
    {a b : G} (ha : a ∈ A) (hb : b ∈ B) (ha2 : orderOf a = 2)
    (hb2 : orderOf b = 2) (hu : a * b ∈ center G) (hne : a * b ≠ 1)
    [(zpowers (a * b)).Normal]
    (hn : A.map (QuotientGroup.mk' (zpowers (a * b))) ≤
        B.map (QuotientGroup.mk' (zpowers (a * b))) ∨
      B.map (QuotientGroup.mk' (zpowers (a * b))) ≤
        A.map (QuotientGroup.mk' (zpowers (a * b))))
    (hs : BenderSuzuki.IsStronglyEmbedded
      ((intersectionGenerated (A.map (QuotientGroup.mk' (zpowers (a * b))))
        (B.map (QuotientGroup.mk' (zpowers (a * b))))).subgroupOf
          (normalClosure (A.map (QuotientGroup.mk' (zpowers (a * b))) : Set (G ⧸ zpowers (a * b)))))) :
    False := by
  let q := QuotientGroup.mk' (zpowers (a * b))
  let L := normalClosure (A.map q : Set (G ⧸ zpowers (a * b)))
  have hu2 := m.setup.mixed_orderOf ha hb ha2 hb2 hne
  have hI : A ⊓ B ≠ ⊥ := by
    rcases hn with hn | hn
    · exact inf_ne_bot_of_quotient_nested hu2 hu m.setup.left_rank hn
    · rw [inf_comm]
      exact inf_ne_bot_of_quotient_nested hu2 hu m.setup.right_rank hn
  obtain ⟨t, ht, ht2⟩ := exists_intersection_involution m.setup hI
  have hi := (m.central_quotient_injective (zpowers (a * b)) (zpowers_le.mpr hu)).1
  have horder (x : G) (hx : x ∈ A) (hx2 : orderOf x = 2) : orderOf (q x) = 2 := by
    simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.orderOf_mk] using
      (orderOf_injective _ hi (⟨x, hx⟩ : A)).trans (by simpa using hx2)
  let aL : L := ⟨q a, subset_normalClosure (mem_map_of_mem q ha)⟩
  let tL : L := ⟨q t, subset_normalClosure (mem_map_of_mem q ht.1)⟩
  have hinv {x : L} (ho : orderOf (x : G ⧸ zpowers (a * b)) = 2) :
      BenderSuzuki.PFAppendixIII.IsInvolution x := by
    have hh : orderOf x = 2 := by simpa using ho
    exact ⟨(orderOf_eq_prime_iff.mp hh).2, (orderOf_eq_prime_iff.mp hh).1⟩
  obtain ⟨gL, hg⟩ := hs.involutions_conjugate
    (hinv (x := aL) (horder a ha ha2)) (hinv (x := tL) (horder t ht.1 ht2))
  obtain ⟨g, hgq⟩ := QuotientGroup.mk'_surjective (zpowers (a * b)) (gL : G ⧸ zpowers (a * b))
  apply no_quotient_fusion_to_intersection m hc ha hb ha2 hb2 hu hne ht (g := g)
  have he := congrArg Subtype.val hg
  change (gL : G ⧸ zpowers (a * b))⁻¹ * q a * gL = q t at he
  simpa only [map_mul, map_inv, hgq] using he

private theorem fused_pair_fixes
    (h : Hypotheses S A B)
    (hc : IsStronglyClosedSet ((A : Set G) ∪ B) (S : Subgroup G) ⊤)
    {a b : G} (ha : a ∈ A) (hb : b ∈ B) (hu : a * b ∈ center G)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hpair : ∀ k ∈ K, k * a * k⁻¹ = a ∨ k * a * k⁻¹ = b)
    {t : G} (ht : t ∈ K)
    (hf : ∃ x ∈ (A : Set G) ∪ B, ∃ k : G, k * x * k⁻¹ = t) :
    Commute t a := by
  obtain ⟨x, hx, k, hk⟩ := hf
  have hxS := hc.1 hx
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_orderOf_eq_pow (⟨x, hxS⟩ : S)
  have htorder : orderOf (⟨t, ht⟩ : K) = 2 ^ n := by
    rw [Subgroup.orderOf_mk, ← hk]
    have he := (MulAut.conj k).orderOf_eq x
    simpa only [MulAut.conj_apply, Subgroup.orderOf_mk] using he.trans (by simpa using hn)
  obtain ⟨y, hy⟩ := (S.subtype hSK).exists_isConj_of_orderOf_eq_prime_pow htorder
  obtain ⟨r, hr⟩ := isConj_iff.mp hy
  have hr' : (r : G) * t * (r : G)⁻¹ = ((y : K) : G) := congrArg Subtype.val hr
  have hxy : (r : G) * k * x * ((r : G) * k)⁻¹ = ((y : K) : G) := by
    rw [← hr', ← hk]
    group
  have hyS : ((y : K) : G) ∈ S := by
    have hh := y.property
    change (y : K) ∈ (S.subtype hSK : Subgroup K) at hh
    rw [Sylow.coe_subtype] at hh
    exact hh
  have hyU : ((y : K) : G) ∈ (A : Set G) ∪ B := by
    have hh := hc.2 x hx ((r : G) * k)⁻¹ (mem_top _)
      (show (((r : G) * k)⁻¹)⁻¹ * x * ((r : G) * k)⁻¹ ∈ S by
        simpa only [inv_inv, hxy] using hyS)
    simpa only [inv_inv, hxy] using hh
  have hcomm : Commute ((y : K) : G) ((r : G) * a * (r : G)⁻¹) := by
    rcases hpair r r.property with he | he
    · rw [he]
      exact (central_mixed_commutes h ha hb hu hyU).1
    · rw [he]
      exact (central_mixed_commutes h ha hb hu hyU).2
  have hh := congrArg (fun z => (r : G)⁻¹ * z * (r : G)) hcomm.eq
  rw [← hr'] at hh
  change t * a = a * t
  simpa [mul_assoc] using hh

omit [Finite G] in
private theorem map_conjugate (C : Subgroup G) (q : G →* Q) (g : G) :
    (conjugate C g).map q = conjugate (C.map q) (q g) := by
  simp only [conjugate, map_map]
  congr 1
  ext x
  simp

private theorem no_exceptional_quotient
    (m : MinimalCounterexample S A B)
    (hc : IsStronglyClosedSet ((A : Set G) ∪ B) (S : Subgroup G) ⊤)
    (hl : LocalControl S A B)
    {a b : G} (ha : a ∈ A) (hb : b ∈ B) (ha2 : orderOf a = 2)
    (hb2 : orderOf b = 2) (hu : a * b ∈ center G) (hne : a * b ≠ 1)
    [(zpowers (a * b)).Normal]
    (he : Exceptional (A.map (QuotientGroup.mk' (zpowers (a * b))))
      (B.map (QuotientGroup.mk' (zpowers (a * b))))) : False := by
  let q := QuotientGroup.mk' (zpowers (a * b))
  let I := A.map q ⊓ B.map q
  let K := (centralizer ({q a} : Set (G ⧸ zpowers (a * b)))).comap q
  have hu2 := m.setup.mixed_orderOf ha hb ha2 hb2 hne
  have hi := m.central_quotient_injective (zpowers (a * b)) (zpowers_le.mpr hu)
  have hqab : q a = q b := quotient_same_involution ha2
  have hqa : q a ≠ 1 := by
    intro heq
    have hh : (⟨a, ha⟩ : A) = 1 := hi.1 (by
      change q a = q 1
      simpa only [map_one] using heq)
    exact (orderOf_eq_prime_iff.mp ha2).2 (congrArg Subtype.val hh)
  have haI : q a ∈ I := ⟨mem_map_of_mem q ha, hqab ▸ mem_map_of_mem q hb⟩
  have hcases {x : G ⧸ zpowers (a * b)} (hx : x ∈ I) : x = 1 ∨ x = q a := by
    have hqa' : (⟨q a, haI⟩ : I) ≠ 1 := fun hh => hqa (congrArg Subtype.val hh)
    rcases card_two_cases he.2.2 hqa' (⟨x, hx⟩ : I) with hh | hh
    · exact Or.inl (congrArg Subtype.val hh)
    · exact Or.inr (congrArg Subtype.val hh)
  have ha_sq : a * a = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp ha2).1
  have hb_sq : b * b = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hb2).1
  have hua : (a * b) * a = b := by
    rw [mul_assoc, ← (factor_commute m.setup ha hb).eq, ← mul_assoc, ha_sq, one_mul]
  have hup : a * b ∈ S := (S : Subgroup G).mul_mem (m.setup.left_le ha) (m.setup.right_le hb)
  have hpre {C : Subgroup G} (hC : C ≤ S) {x : G} (hx : q x ∈ C.map q) : x ∈ S := by
    obtain ⟨y, hy, hyx⟩ := hx
    rcases quotient_fiber hu2 hyx.symm with hh | hh
    · exact hh ▸ hC hy
    · exact hh ▸ (S : Subgroup G).mul_mem hup (hC hy)
  have hpair : ∀ k ∈ K, k * a * k⁻¹ = a ∨ k * a * k⁻¹ = b := by
    intro k hk
    have hcomm : q k * q a = q a * q k := mem_centralizer_singleton_iff.mp hk
    have heq : q (k * a * k⁻¹) = q a := by
      rw [map_mul, map_mul, map_inv, hcomm, mul_assoc, mul_inv_cancel, mul_one]
    simpa only [hua] using quotient_fiber hu2 heq
  have hSK : (S : Subgroup G) ≤ K := by
    intro s hs
    have hs' : s⁻¹ ∈ S := (S : Subgroup G).inv_mem hs
    have hsa : s * a * s⁻¹ ∈ conjugate A s⁻¹ := by
      simpa only [conjugate, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv] using mem_map_of_mem (MulAut.conj s).toMonoidHom ha
    have hsb : s * b * s⁻¹ ∈ conjugate B s⁻¹ := by
      simpa only [conjugate, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv] using mem_map_of_mem (MulAut.conj s).toMonoidHom hb
    have heq : q (s * a * s⁻¹) = q (s * b * s⁻¹) := by simp only [map_mul, hqab]
    have hI : q (s * a * s⁻¹) ∈ I := by
      rcases hl.permutes_pair s⁻¹ hs' with hh | hh
      · rw [hh.1] at hsa
        rw [hh.2] at hsb
        exact ⟨mem_map_of_mem q hsa, heq ▸ mem_map_of_mem q hsb⟩
      · rw [hh.1] at hsa
        rw [hh.2] at hsb
        exact ⟨heq ▸ mem_map_of_mem q hsb, mem_map_of_mem q hsa⟩
    have hn : q (s * a * s⁻¹) ≠ 1 := by
      intro hh
      apply hqa
      have hh' := congrArg (fun z => (q s)⁻¹ * z * q s) hh
      simpa [map_mul, map_inv, mul_assoc] using hh'
    have hh := (hcases hI).resolve_left hn
    apply mem_centralizer_singleton_iff.mpr
    have hh' := congrArg (fun z => z * q s) hh
    simpa [map_mul, map_inv, mul_assoc] using hh'
  obtain ⟨⟨gbar, hgbar, kbar, hkbar⟩, _, hcard⟩ := he
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (zpowers (a * b)) kbar
  obtain ⟨x, hx, hxq⟩ := hkbar
  change q k = kbar at hk
  change q x = kbar⁻¹ * gbar * kbar at hxq
  let t := k * x * k⁻¹
  have htq : q t = gbar := by
    have hh := congrArg (fun z => kbar * z * kbar⁻¹) hxq
    simpa [t, map_mul, map_inv, hk, mul_assoc] using hh
  have htimage : (conjugate A t).map q = B.map q := by
    rw [map_conjugate, htq]
    exact hgbar
  have htAS : conjugate A t ≤ S := fun z hz =>
    hpre m.setup.right_le (htimage ▸ mem_map_of_mem q hz)
  have htcover : (conjugate A t : Set G) ⊆ (A : Set G) ∪ B := by
    rintro z ⟨w, hw, rfl⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
    apply hc.2 w (Or.inl hw) t (mem_top _)
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv] using htAS (mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom hw)
  have htAB : conjugate A t ≤ B := by
    rcases SubgroupClass.subset_union.mp htcover with hh | hh
    · have hh' : B.map q ≤ A.map q := htimage ▸ map_mono hh
      have hI : I = B.map q := inf_eq_right.mpr hh'
      have hsetup := m.central_quotient_hypotheses hc (zpowers (a * b)) (zpowers_le.mpr hu)
      obtain ⟨E, hE, _⟩ := hsetup.right_rank
      have hcE := Subgroup.card_le_card_group E
      have hcB : Nat.card (B.map q) = 2 := by rw [← hI]; exact hcard
      rw [hcB, hE] at hcE
      omega
    · exact hh
  have hta : t⁻¹ * a * t ∈ B := htAB (by
    simpa only [conjugate, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv] using mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom ha)
  have htbS : t⁻¹ * b * t ∈ S := by
    have huconj : (t⁻¹ * a * t) * (t⁻¹ * b * t) = a * b := by
      calc
        _ = t⁻¹ * (a * b) * t := by group
        _ = a * b := by rw [mul_assoc, ← mem_center_iff.mp hu t, inv_mul_cancel_left]
    have hbform : t⁻¹ * b * t = (t⁻¹ * a * t)⁻¹ * (a * b) := by
      rw [← huconj, inv_mul_cancel_left]
    rw [hbform]
    exact (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem (m.setup.right_le hta)) hup
  have htb : t⁻¹ * b * t ∈ A := by
    rcases hc.2 b (Or.inr hb) t (mem_top _) htbS with hh | hh
    · exact hh
    · have hh' : a * b ∈ B := by
        have hbprod := B.mul_mem hta hh
        have heq : (t⁻¹ * a * t) * (t⁻¹ * b * t) = a * b := by
          calc
            _ = t⁻¹ * (a * b) * t := by group
            _ = a * b := by rw [mul_assoc, ← mem_center_iff.mp hu t, inv_mul_cancel_left]
        rwa [heq] at hbprod
      exact ((central_mixed_not_mem m hu hne).2 hh').elim
  have hqta : q (t⁻¹ * a * t) = q a := by
    apply (hcases ?_).resolve_left
    · intro hh
      apply hqa
      have hh' := congrArg (fun z => q t * z * (q t)⁻¹) hh
      simpa [map_mul, map_inv, mul_assoc] using hh'
    · refine ⟨?_, mem_map_of_mem q hta⟩
      have heq : q (t⁻¹ * a * t) = q (t⁻¹ * b * t) := by simp only [map_mul, hqab]
      exact heq ▸ mem_map_of_mem q htb
  have htab : t⁻¹ * a * t = b := by
    exact congrArg Subtype.val (hi.2 (hqta.trans hqab) :
      (⟨t⁻¹ * a * t, hta⟩ : B) = ⟨b, hb⟩)
  have htK : t ∈ K := by
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (fun z => q t * z) hqta
    simpa [map_mul, map_inv, mul_assoc] using hh.symm
  have hfix := fused_pair_fixes m.setup hc ha hb hu K hSK hpair htK
    ⟨x, Or.inl hx, k, rfl⟩
  have hab : a = b := by
    calc
      a = t⁻¹ * a * t := by rw [mul_assoc, ← hfix.eq, inv_mul_cancel_left]
      _ = b := htab
  exact hne (by rw [hab]; exact hb_sq)

/-- The central-quotient step in source (g): a nonidentity mixed product of
factor involutions cannot be central. Both quotient alternatives are eliminated
using their actual quotient maps, with the first factor's normal closure retained. -/
theorem MinimalCounterexample.mixed_central_quotient_exclusion
    (m : MinimalCounterexample S A B)
    (hc : IsStronglyClosedSet ((A : Set G) ∪ B) (S : Subgroup G) ⊤)
    (hl : LocalControl S A B) : MixedCentralQuotientExclusion A B := by
  intro a ha b hb ha2 hb2 hne hu
  have hN : zpowers (a * b) ≤ center G := zpowers_le.mpr hu
  let : (zpowers (a * b)).Normal := ⟨fun x hx g => by
    simpa only [mem_center_iff.mp (hN hx) g, mul_assoc, mul_inv_cancel, mul_one] using hx⟩
  obtain ⟨hq, hproper⟩ := m.mixed_central_quotient_conclusion hc ha hb hu hne
  rcases hq with hgen | ⟨hn, hs⟩ | he
  · exact hproper hgen
  · exact no_nested_quotient m hc ha hb ha2 hb2 hu hne hn hs
  · exact no_exceptional_quotient m hc hl ha hb ha2 hb2 hu hne he

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
