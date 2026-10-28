module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.Setup
public import Theory.GroupTheory.IndexTwoNormalizer
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.Representation.BinaryOffender.ConjugationImage
public import Theory.Representation.GoldschmidtONan.Basic
public import Theory.Representation.BinaryOffender.ComponentSum

/-!
# Lifting the odd-branch supports through the original central quotient

The supports are inverse images of subspaces of the literal U/Z. Equivariance
transports their normalizers and conjugates. Odd-order averaging makes a
subspace of the residual moved space disjoint from the residual fixed space.
This supplies the fixed-vector premise used in the first paragraph of 14.6.17.
The local normalizer equality from 14.6.16 remains a separate source input.

Source: Aschbacher--Smith 14.6.12(2) and 14.6.17, pp.1031,1035--1036.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G]
variable {H U Z : Subgroup G} [IsElementaryAbelian 2 U]

/-- The actual preimage in U of a binary subspace of U/Z. -/
def supportPreimage (_a : LocalQuotientAction H U Z)
    (A : Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U))) : Subgroup G :=
  ((binarySubgroup A).comap (QuotientGroup.mk' (Z.subgroupOf U))).map U.subtype

theorem mem_supportPreimage (a : LocalQuotientAction H U Z)
    (A : Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U))) (u : U) :
    (u : G) ∈ supportPreimage a A ↔
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u) ∈ A := by
  change (u : G) ∈ ((binarySubgroup A).comap _).map U.subtype ↔ _
  constructor
  · rintro ⟨v,hv,he⟩
    have hev : v = u := U.subtype_injective he
    exact hev ▸ hv
  · intro hu
    exact ⟨u,hu,rfl⟩

theorem supportPreimage_le (a : LocalQuotientAction H U Z)
    (A : Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U))) :
    supportPreimage a A ≤ U := map_subtype_le _

theorem kernel_lt_supportPreimage (a : LocalQuotientAction H U Z)
    (A : Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U))) (hne : A ≠ ⊥) :
    Z < supportPreimage a A := by
  have hle : Z ≤ supportPreimage a A := by
    intro z hz
    apply (mem_supportPreimage a A ⟨z,a.kernel_le hz⟩).mpr
    have he : QuotientGroup.mk' (Z.subgroupOf U) ⟨z,a.kernel_le hz⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hz
    rw [he]
    exact A.zero_mem
  refine lt_of_le_of_ne hle ?_
  intro he
  apply hne
  apply le_bot_iff.mp
  intro v hv
  obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) v.toMul
  have huA : Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u) ∈ A := by
    rw [hu]
    exact hv
  have huz : (u : G) ∈ Z := he ▸ (mem_supportPreimage a A u).mpr huA
  have hzero := (QuotientGroup.eq_one_iff u).mpr (show u ∈ Z.subgroupOf U from huz)
  exact congrArg Additive.ofMul (hu.symm.trans hzero)

theorem supportPreimage_normalized (a : LocalQuotientAction H U Z)
    (A : Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U)))
    (B : Subgroup G) (hBH : B ≤ H)
    (hBA : actorImage H B ≤ subspaceStabilizer a.representation A) :
    B ≤ normalizer (supportPreimage a A : Set G) := by
  apply le_normalizer_iff.mpr
  intro b hb u hu
  have huU := supportPreimage_le a A hu
  apply (mem_supportPreimage a A
    ⟨b*u*b⁻¹,(a.normalizes (hBH hb) u).mp huU⟩).mpr
  rw [← a.conjugation ⟨b,hBH hb⟩ ⟨u,huU⟩]
  exact (hBA (mem_map_of_mem _ (show (⟨b,hBH hb⟩ : H) ∈ B.subgroupOf H from hb)) _).2
    ((mem_supportPreimage a A ⟨u,huU⟩).mp hu)

theorem supportPreimage_conjugate (a : LocalQuotientAction H U Z)
    (A : Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U))) (h : H) :
    (supportPreimage a A).map (MulAut.conj (h : G)).toMonoidHom =
      supportPreimage a (A.map (a.representation (QuotientGroup.mk' (pCore 2 H) h))) := by
  apply le_antisymm
  · rintro _ ⟨u,hu,rfl⟩
    have huU := supportPreimage_le a A hu
    apply (mem_supportPreimage a _
      ⟨(h:G)*u*(h:G)⁻¹,(a.normalizes h.property u).mp huU⟩).mpr
    refine ⟨_,(mem_supportPreimage a A ⟨u,huU⟩).mp hu,?_⟩
    exact a.conjugation h ⟨u,huU⟩
  · intro u hu
    have huU := supportPreimage_le a _ hu
    let v : U := ⟨((h⁻¹ : H):G)*u*((h⁻¹ : H):G)⁻¹,
      (a.normalizes (H.inv_mem h.property) u).mp huU⟩
    refine ⟨v,?_,by simp [v,MulAut.conj_apply,mul_assoc]⟩
    apply (mem_supportPreimage a A v).mpr
    obtain ⟨w,hw,he⟩ := (mem_supportPreimage a _ ⟨u,huU⟩).mp hu
    have hv : Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) v) = w := by
      rw [← a.conjugation h⁻¹ ⟨u,huU⟩,← he,map_inv]
      exact a.representation.inv_self_apply _ _
    exact hv ▸ hw

theorem supportPreimage_disjoint_modulo (a : LocalQuotientAction H U Z)
    (A B : Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U))) (hd : Disjoint A B) :
    supportPreimage a A ⊓ supportPreimage a B ≤ Z := by
  intro u hu
  have huU := supportPreimage_le a A hu.1
  have he := Submodule.disjoint_def.mp hd _
    ((mem_supportPreimage a A ⟨u,huU⟩).mp hu.1)
    ((mem_supportPreimage a B ⟨u,huU⟩).mp hu.2)
  exact (QuotientGroup.eq_one_iff (⟨u,huU⟩ : U)).mp (congrArg Additive.toMul he)

/-- No residual-fixed vector survives on a lifted residual moved subspace.
The residual is O²(H), while its action is through the literal H/O₂(H). -/
theorem supportPreimage_fixedFree [Finite G] (a : LocalQuotientAction H U Z)
    (hodd : Odd (Nat.card (pResidual 2 (H ⧸ pCore 2 H))))
    (A : Submodule (ZMod 2) (Additive (U ⧸ Z.subgroupOf U)))
    (hA : A ≤ subspaceCommutator a.representation ⊤ (pResidual 2 (H ⧸ pCore 2 H))) :
    ∀ u ∈ supportPreimage a A,
      (∀ k ∈ residual H, ⁅u,k⁆ ∈ Z) → u ∈ Z := by
  intro u hu hfix
  have huU := supportPreimage_le a A hu
  let v := Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) ⟨u,huU⟩)
  have hf : v ∈ fixedSpace a.representation (pResidual 2 (H ⧸ pCore 2 H)) := by
    rintro ⟨k,hk⟩
    have hr : (pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H)) =
        pResidual 2 (H ⧸ pCore 2 H) := map_pResidual_quotient 2 (pCore 2 H)
    obtain ⟨b,hb,rfl⟩ := hr ▸ hk
    change a.representation (QuotientGroup.mk' (pCore 2 H) b) v = v
    rw [a.conjugation]
    apply congrArg Additive.ofMul
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (b:G)*u*(b:G)⁻¹ / u ∈ Z
    have hc := Z.inv_mem (hfix b (mem_map_of_mem _ hb))
    simpa only [mul_inv_rev,inv_inv,commutatorElement_def,div_eq_mul_inv,mul_assoc] using hc
  have hd : Disjoint (fixedSpace a.representation (pResidual 2 (H ⧸ pCore 2 H)))
      (subspaceCommutator a.representation ⊤ (pResidual 2 (H ⧸ pCore 2 H))) := by
    simpa only [Representation.RegularCyclicNormalClosure.displacementSpan,
      subspaceCommutator,eq_comm] using
      (Representation.GoldschmidtONan.isCompl_fixed_moved_of_odd
        (ρ := a.representation) hodd).disjoint
  have hv : v = 0 := Submodule.disjoint_def.mp hd _ hf
    (hA ((mem_supportPreimage a A ⟨u,huU⟩).mp hu))
  exact (QuotientGroup.eq_one_iff (⟨u,huU⟩ : U)).mp (congrArg Additive.toMul hv)


theorem actorImage_normalizes (A B : Subgroup G) (hAH : A ≤ H)
    (hn : B ≤ normalizer (A : Set G)) :
    actorImage H B ≤ normalizer (actorImage H A : Set _) := by
  apply le_trans (map_mono ?_) (le_normalizer_map (QuotientGroup.mk' (pCore 2 H)))
  rw [← subgroupOf_normalizer_eq hAH]
  exact fun _ hx => hn hx

/-- O²(H) lies in the index-two subgroup H₀ from 14.6.12. -/
theorem residual_le_of_index_two [Finite G]
    (H0 : Subgroup G) (h0H : H0 ≤ H) (hi : H0.relIndex H = 2) :
    residual H ≤ H0 := by
  let : (H0.subgroupOf H).Normal := normal_of_index_eq_two hi
  have hp : IsPGroup 2 (H ⧸ H0.subgroupOf H) :=
    isPGroup_iff_card_dvd_pow.mpr ⟨1,by change H0.relIndex H ∣ 2^1; rw [hi]; decide⟩
  have hr := (pResidual_le_iff_isPGroup_quotient 2 (H0.subgroupOf H)).mpr hp
  exact (map_mono hr).trans_eq (map_subgroupOf_eq_of_le h0H)


/-- Quotient actors retain literal conjugation by members of H. -/
theorem actorImage_conjugate (A : Subgroup G) (hAH : A ≤ H) (h : H) :
    actorImage H (A.map (MulAut.conj (h : G)).toMonoidHom) =
      (actorImage H A).map
        (MulAut.conj (QuotientGroup.mk' (pCore 2 H) h)).toMonoidHom := by
  have hsub : (A.map (MulAut.conj (h : G)).toMonoidHom).subgroupOf H =
      (A.subgroupOf H).map (MulAut.conj h).toMonoidHom := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le, map_map]
    · conv_lhs => rw [← map_subgroupOf_eq_of_le hAH, map_map]
      rfl
    · rintro _ ⟨a,ha,rfl⟩
      exact H.mul_mem (H.mul_mem h.property (hAH ha)) (H.inv_mem h.property)
  unfold actorImage
  rw [hsub,map_map,map_map]
  congr 1

/-- The first lifted moved summand and all its outside conjugates satisfy
the algebraic support premises in 14.6.17. The ambient fitting containment
and 14.6.16 local normalizer equality are separate source obligations. -/
theorem exchanged_support_geometry [Finite G]
    (a : LocalQuotientAction H U Z)
    (T H0 H1 H2 : Subgroup G) (hTH : T ≤ H)
    (h0H : H0 ≤ H) (h1H : H1 ≤ H) (h2H : H2 ≤ H)
    (hi : H0.relIndex H = 2)
    (h0N1 : H0 ≤ normalizer (H1 : Set G))
    (h0N2 : H0 ≤ normalizer (H2 : Set G))
    (x : G) (hx : x ∈ T) (hxN : x ∉ normalizer (H1 : Set G))
    (hex : H1.map (MulAut.conj x⁻¹).toMonoidHom = H2)
    (hne : subspaceCommutator a.representation ⊤ (actorImage H H1) ≠ ⊥)
    (hd : Disjoint (subspaceCommutator a.representation ⊤ (actorImage H H1))
      (subspaceCommutator a.representation ⊤ (actorImage H H2))) :
    let W := supportPreimage a (subspaceCommutator a.representation ⊤ (actorImage H H1))
    let S := T ⊓ normalizer (H1 : Set G)
    W ≤ U ∧ Z < W ∧ residual H ≤ normalizer (W : Set G) ∧
      S ≤ normalizer (W : Set G) ∧ S.relIndex T = 2 ∧
      ∀ t ∈ T, t ∉ S →
        W ⊓ W.map (MulAut.conj t⁻¹).toMonoidHom ≤ Z ∧
        residual H ≤ normalizer (W.map (MulAut.conj t⁻¹).toMonoidHom : Set G) := by
  let W (B : Subgroup G) := supportPreimage a
    (subspaceCommutator a.representation ⊤ (actorImage H B))
  have hnorm (A B : Subgroup G) (hAH : A ≤ H) (hBH : B ≤ H)
      (hn : B ≤ normalizer (A : Set G)) : B ≤ normalizer (W A : Set G) := by
    apply supportPreimage_normalized a _ B hBH
    apply subspaceCommutator_invariant_normalizer a.representation
      (le_subspaceStabilizer _ ⊤ (by intros; trivial))
    exact actorImage_normalizes A B hAH hn
  have hr0 := residual_le_of_index_two H0 h0H hi
  have hrH : residual H ≤ H := map_subtype_le _
  refine ⟨supportPreimage_le a _,kernel_lt_supportPreimage a _ hne,
    hnorm H1 (residual H) h1H hrH (hr0.trans h0N1),
    hnorm H1 _ h1H (inf_le_left.trans hTH) inf_le_right,
    normalizer_relIndex_eq_two_of_index_two_overgroup T H H0 H1 hTH hi h0N1 ⟨x,hx,hxN⟩,?_⟩
  intro t ht htS
  have hconj := map_conj_eq_of_outside_normalizer T H H0 H1 H2 hTH h1H
    hi h0N1 x hx hxN hex t ht htS
  have hW : (W H1).map (MulAut.conj t⁻¹).toMonoidHom = W H2 := by
    rw [show W H1 = supportPreimage a
      (subspaceCommutator a.representation ⊤ (actorImage H H1)) from rfl,
      supportPreimage_conjugate a _ (⟨t⁻¹,H.inv_mem (hTH ht)⟩ : H),moved_map_conjugate,
      ← actorImage_conjugate H1 h1H (⟨t⁻¹,H.inv_mem (hTH ht)⟩ : H),hconj]
  change W H1 ⊓ (W H1).map (MulAut.conj t⁻¹).toMonoidHom ≤ Z ∧
    residual H ≤ normalizer (((W H1).map (MulAut.conj t⁻¹).toMonoidHom : Subgroup G) : Set G)
  rw [hW]
  exact ⟨supportPreimage_disjoint_modulo a _ _ hd,
    hnorm H2 (residual H) h2H hrH (hr0.trans h0N2)⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
