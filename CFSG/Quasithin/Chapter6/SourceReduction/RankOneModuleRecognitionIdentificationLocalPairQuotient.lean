module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalPairFusion
public import Theory.GroupTheory.SymmetricThreeConjugateKernel
public import Theory.GroupTheory.SymmetricThreeTwoCore

/-!
# Removing the central kernel of the source pair action

Modulo the quaternion core, the two layer images are involutions and the
remaining kernel of the symmetric-three action is central. Their product has
sixth power one, so this kernel has order at most two. Internal conjugacy of
the original layers then removes the kernel by the central-extension lemma.
The resulting surjection identifies the literal two-core and its S₃ quotient.

Source: Aschbacher--Smith, 6.2.6(2), printed p.682.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]

private theorem card_two_generator {U : Subgroup G} (hU : Nat.card U = 2) :
    ∃ u ∈ U, u ^ 2 = 1 ∧ U = zpowers u := by
  obtain ⟨u, hu, _⟩ := (Nat.card_eq_two_iff' (1 : U)).mp hU
  have h2 : (u : G)^2=1 := by
    have he := pow_card_eq_one' (x := u)
    rw [hU] at he
    exact congrArg Subtype.val he
  refine ⟨u, u.property, h2, ?_⟩
  apply (eq_of_le_of_card_ge (zpowers_le.mpr u.property) ?_).symm
  rw [Nat.card_zpowers, hU, orderOf_eq_prime h2 (fun he => hu (Subtype.ext he))]

private theorem central_symmetricThree_pair_kernel_two
    (f : G →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center G) (U V : Subgroup G)
    (hU : Nat.card U = 2) (hV : Nat.card V = 2)
    (hUf : Nat.card (U.map f) = 2) (hVf : Nat.card (V.map f) = 2)
    (hgen : U ⊔ V = ⊤) : IsPGroup 2 f.ker := by
  obtain ⟨u, hu, hu2, hUz⟩ := card_two_generator hU
  obtain ⟨v, hv, hv2, hVz⟩ := card_two_generator hV
  have hfu : f u ≠ 1 := by
    intro he
    rw [hUz, MonoidHom.map_zpowers, he, zpowers_one_eq_bot, card_bot] at hUf
    contradiction
  have hfv : f v ≠ 1 := by
    intro he
    rw [hVz, MonoidHom.map_zpowers, he, zpowers_one_eq_bot, card_bot] at hVf
    contradiction
  have hab : (f u * f v)^3=1 := by
    have hh : ∀ a b : Equiv.Perm (Fin 3), a^2=1 → b^2=1 → a≠1 → b≠1 →
        (a*b)^3=1 := by decide +kernel
    exact hh (f u) (f v) (by rw [← map_pow, hu2, map_one])
      (by rw [← map_pow, hv2, map_one]) hfu hfv
  have hcen : (u*v)^3 ∈ center G := hc (by
    change f ((u*v)^3)=1
    rw [map_pow, map_mul, hab])
  have hui : u⁻¹=u := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hu2)
  have hvi : v⁻¹=v := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hv2)
  have hinv : u*(u*v)*u⁻¹=(u*v)⁻¹ := by
    rw [mul_inv_rev, hui, hvi, ← mul_assoc, show u*u=1 from by simpa only [pow_two] using hu2, one_mul]
  have h3 : (u*v)^3=((u*v)^3)⁻¹ := by
    calc
      _ = u*(u*v)^3*u⁻¹ := by rw [mem_center_iff.mp hcen u, mul_inv_cancel_right]
      _ = (u*(u*v)*u⁻¹)^3 := conj_pow.symm
      _ = ((u*v)^3)⁻¹ := by rw [hinv, inv_pow]
  have h6 : (u*v)^6=1 := by
    change (u*v)^(3*2)=1
    rw [pow_mul, pow_two]
    conv_lhs => lhs; rw [h3]
    exact inv_mul_cancel _
  have hcl : closure ({v,u}:Set G)=⊤ := by
    rw [← hgen, hUz, hVz, zpowers_eq_closure, zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
    exact Set.pair_comm v u
  have hcard : Nat.card G ≤ 12 := by
    have hh := (closure_pair_finite_card_le_of_involutions (by decide : 0<6) v u hv2 hu2 h6).2
    rwa [hcl, card_top] at hh
  have h6card : Nat.card (Equiv.Perm (Fin 3))=6 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hh := f.ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr hf, card_top, h6card] at hh
  have hpos := Nat.card_pos (α := f.ker)
  have hsmall : Nat.card f.ker=1 ∨ Nat.card f.ker=2 := by omega
  rcases hsmall with h1 | h2
  · exact IsPGroup.of_card (n:=0) h1
  · exact IsPGroup.of_card (n:=1) h2


omit [Finite G] in
private theorem center_image_le (Q : Subgroup G) [Q.Normal] :
    (center G).map (QuotientGroup.mk' Q) ≤ center (G ⧸ Q) := by
  rintro _ ⟨z,hz,rfl⟩
  apply mem_center_iff.mpr
  intro x
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective Q x
  rw [← map_mul, ← map_mul, mem_center_iff.mp hz y]

private theorem central_factor_kernel_two
    (f : G →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (Q B A : Subgroup G) [Q.Normal]
    (hker : f.ker = Q ⊔ center G) (hQ : IsPGroup 2 Q)
    (hBK : B ⊓ f.ker ≤ Q) (hAK : A ⊓ f.ker ≤ Q)
    (hBf : Nat.card (B.map f) = 2) (hAf : Nat.card (A.map f) = 2)
    (hgen : B ⊔ A = ⊤) : IsPGroup 2 f.ker := by
  have hQK : Q ≤ f.ker := hker.symm ▸ le_sup_left
  let q := QuotientGroup.mk' Q
  let fbar := QuotientGroup.lift Q f hQK
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective Q
  have hfbar : Function.Surjective fbar := QuotientGroup.lift_surjective_of_surjective Q f hf hQK
  have hbarc : fbar.ker ≤ center (G ⧸ Q) := by
    rw [QuotientGroup.ker_lift, hker, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    exact center_image_le Q
  have hbarcard (U : Subgroup G) (hUK : U ⊓ f.ker ≤ Q) (hUf : Nat.card (U.map f) = 2) :
      Nat.card (U.map q) = 2 := by
    have hi : U ⊓ Q = U ⊓ f.ker := le_antisymm (inf_le_inf_left _ hQK) (le_inf inf_le_left hUK)
    rw [← relIndex_ker U q, QuotientGroup.ker_mk', ← inf_relIndex_left,
      hi, inf_relIndex_left, relIndex_ker]
    exact hUf
  have hbarf (U : Subgroup G) (hUf : Nat.card (U.map f) = 2) :
      Nat.card ((U.map q).map fbar) = 2 := by
    rw [map_map, QuotientGroup.lift_comp_mk']
    exact hUf
  have hbargen : B.map q ⊔ A.map q = ⊤ := by
    rw [← Subgroup.map_sup, hgen, map_top_of_surjective q hq]
  have hkbar := central_symmetricThree_pair_kernel_two fbar hfbar hbarc
    (B.map q) (A.map q) (hbarcard B hBK hBf) (hbarcard A hAK hAf)
    (hbarf B hBf) (hbarf A hAf) hbargen
  have hh := hkbar.comap_of_ker_isPGroup q (by rw [QuotientGroup.ker_mk']; exact hQ)
  change IsPGroup 2 (fbar.comp q).ker at hh
  rwa [QuotientGroup.lift_comp_mk'] at hh

variable {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- Internal fusion removes the central kernel and identifies the literal two-core. -/
theorem local_non_two_pair_twoCore_quotient
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (g : G)
    (hleft : (layer L R ⊓ normalizer
      ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)).relIndex (layer L R) = 2)
    (hright : ((layer L R).map (MulAut.conj g).toMonoidHom ⊓
      normalizer (layer L R : Set G)).relIndex
        ((layer L R).map (MulAut.conj g).toMonoidHom) = 2)
    (hnon : ¬ IsPGroup 2 (layer L R ⊔
      (layer L R).map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    let J := B ⊔ A
    localPairCore B A = J.pCoreIn 2 ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3)) := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let J := B ⊔ A
  let Q := localPairCore B A
  let BJ := B.subgroupOf J
  let AJ := A.subgroupOf J
  let QJ := Q.subgroupOf J
  have hBJ : B ≤ J := le_sup_left
  have hAJ : A ≤ J := le_sup_right
  have hQJ : Q ≤ J := sup_le (inf_le_left.trans hBJ) (inf_le_left.trans hAJ)
  have hgen : BJ ⊔ AJ = ⊤ := by rw [← subgroupOf_sup hBJ hAJ, subgroupOf_self]
  obtain ⟨hn, d, hK, hB, hA, _, _, _⟩ :=
    local_non_two_pair_outer_action h hnatural hE g hleft hright hnon
  obtain ⟨hn', d', hK', ⟨e'⟩⟩ :=
    local_non_two_pair_outer_symmetricThree h hnatural hE g hleft hright hnon
  let f := seedOrthogonalAction J Q hn d
  let f' := seedOrthogonalAction J Q hn' d'
  have heK : f.ker = f'.ker := map_injective J.subtype_injective (hK.trans hK'.symm)
  let e : f.range ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.quotientKerEquivRange f).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq heK).trans
        ((QuotientGroup.quotientKerEquivRange f').trans e'))
  let fS := e.toMonoidHom.comp f.rangeRestrict
  have hfS : Function.Surjective fS := e.surjective.comp f.rangeRestrict_surjective
  have hkS : fS.ker = f.ker := by
    ext x
    change e (f.rangeRestrict x)=1 ↔ f x=1
    rw [e.map_eq_one_iff]
    exact ⟨fun he => congrArg Subtype.val he, fun he => Subtype.ext he⟩
  have hker : fS.ker = QJ ⊔ center J := by
    rw [hkS]
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hQJ, map_center_subtype_eq_inf_centralizer]
    exact hK
  let : QJ.Normal := (normal_subgroupOf_iff_le_normalizer hQJ).mpr hn
  have hpQ : IsPGroup 2 QJ := (IsPGroup.of_card (n:=5) d.card).comap_subtype
  have hKN : f.ker.map J.subtype ≤ normalizer (B : Set G) ⊓ normalizer (A : Set G) := by
    rw [hK]
    refine sup_le (sup_le ?_ ?_) (le_inf ?_ ?_)
    · exact le_inf (inf_le_left.trans B.le_normalizer) inf_le_right
    · exact le_inf inf_le_right (inf_le_left.trans A.le_normalizer)
    · exact (inf_le_right.trans (centralizer_le hBJ)).trans (Subgroup.centralizer_le_normalizer _)
    · exact (inf_le_right.trans (centralizer_le hAJ)).trans (Subgroup.centralizer_le_normalizer _)
  have hBK : BJ ⊓ fS.ker ≤ QJ := by
    intro x hx
    have hxK := mem_map_of_mem J.subtype (hkS ▸ hx.2)
    exact (show B ⊓ normalizer (A : Set G) ≤ Q from le_sup_left) ⟨hx.1,(hKN hxK).2⟩
  have hAK : AJ ⊓ fS.ker ≤ QJ := by
    intro x hx
    have hxK := mem_map_of_mem J.subtype (hkS ▸ hx.2)
    exact (show A ⊓ normalizer (B : Set G) ≤ Q from le_sup_right) ⟨hx.1,(hKN hxK).1⟩
  have hBf : Nat.card (BJ.map fS)=2 := by
    rw [← relIndex_ker, hkS, relIndex_ker]
    exact hB
  have hAf : Nat.card (AJ.map fS)=2 := by
    rw [← relIndex_ker, hkS, relIndex_ker]
    exact hA
  have hpK : IsPGroup 2 fS.ker :=
    central_factor_kernel_two fS hfS QJ BJ AJ hker hpQ hBK hAK hBf hAf hgen
  obtain ⟨k,hk,_,hconj⟩ := local_non_two_pair_internal_conjugacy h hnatural hE g hleft hright hnon
  let kJ : J := ⟨k,hk⟩
  have hconjJ : BJ.conjBy kJ = AJ := by
    apply map_injective J.subtype_injective
    change (BJ.map (MulAut.conj kJ).toMonoidHom).map J.subtype = AJ.map J.subtype
    rw [map_subgroupOf_eq_of_le hAJ, map_map]
    have hecomp : J.subtype.comp (MulAut.conj kJ).toMonoidHom =
        (MulAut.conj k).toMonoidHom.comp J.subtype := rfl
    rw [hecomp, ← map_map, map_subgroupOf_eq_of_le hBJ]
    exact hconj
  have hcentral : ⁅fS.ker, (⊤ : Subgroup J)⁆ ≤ QJ := by
    rw [← QuotientGroup.ker_mk' QJ, ← Subgroup.map_eq_bot_iff]
    rw [map_commutator, map_top_of_surjective _ (QuotientGroup.mk'_surjective QJ)]
    apply commutator_top_right_eq_bot_iff_le_center.mpr
    rw [hker, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    exact center_image_le QJ
  have hKeq : fS.ker = QJ :=
    ker_eq_of_symmetric_three_conjugate_pair fS hfS hpK BJ QJ
      (hker.symm ▸ le_sup_left) hBK hcentral hBf kJ (hconjJ.symm ▸ hgen)
  have hcore : QJ = pCore 2 J := hKeq.symm.trans (ker_eq_twoCore_of_surjective_perm_three fS hfS hpK)
  constructor
  · have he := congrArg (Subgroup.map J.subtype) hcore
    rwa [map_subgroupOf_eq_of_le hQJ] at he
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq (hKeq.trans hcore).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective fS hfS)⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
