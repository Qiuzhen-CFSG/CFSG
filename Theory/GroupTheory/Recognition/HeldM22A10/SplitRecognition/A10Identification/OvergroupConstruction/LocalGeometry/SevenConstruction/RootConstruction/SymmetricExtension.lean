module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.Factor
import Theory.Alternating.Aut

/-!
# Held's symmetric extension of the root factor

For the explicit root factor `W ≃ A₇`, adjoining mu-prime gives an index-two
extension of order 5040. Its conjugation action on W is faithful: a kernel
element has square in the center of W, hence any nonidentity kernel element
would be an involution centralizing W.

Such an involution x cannot exist. It centralizes v, so conjugation by tau-prime
puts x in the root centralizer. Every involution in `⟨uv⟩ W` lies in W, since
`uv` has order three and centralizes W. The single involution class of A₇
therefore makes x conjugate to `pi * mu`, and hence to mu. But then
`|W| = 2520` divides `|C_G(x)| = 2880`, a contradiction. This proves the
exclusion directly from the marked local geometry, without a global fusion
theorem. The faithful action and the proved identification `Aut(A₇) ≃ S₇`
now give the actual multiplicative equivalence.

The final theorem retains the finite simple and nonfusion hypotheses of its
source consumer. The argument itself needs only finiteness, the given local
structures, and the supplied noncentral involution centralizer order.

Source: D. Held, *A Characterization of some multiply transitive permutation
groups, I*, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 5.5, p.237; the coordinate identity used in
the exclusion is Lemma 5.8, p.238, proved independently in `RootActions`.
The elementary A₇ cycle-type argument follows the same parity computation as
`alternatingGroup.involution_cycleType_of_degree_le_six` in
`Theory/SpecificGroups/Alternating/SmallInvolutionCentralizers.lean`.
-/

open Subgroup Equiv

private theorem sup_factor {G : Type*} [Group G] (H K : Subgroup G)
    (hn : K ≤ normalizer (H : Set G)) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  let X := H ⊔ K
  let : (H.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le H.le_normalizer hn)
  have htop : H.subgroupOf X ⊔ K.subgroupOf X = ⊤ :=
    (codisjoint_subgroupOf_sup H K).eq_top
  have hx' : (⟨x, hx⟩ : X) ∈ H.subgroupOf X ⊔ K.subgroupOf X := by rw [htop]; trivial
  obtain ⟨h, hh, k, hk, he⟩ := mem_sup_of_normal_left.mp hx'
  exact ⟨h, hh, k, hk, congrArg Subtype.val he⟩

private theorem seven_cycleType (x : alternatingGroup (Fin 7)) (hx : orderOf x = 2) :
    (x : Perm (Fin 7)).cycleType = {2, 2} := by
  have ho : orderOf (x : Perm (Fin 7)) = 2 := (Subgroup.orderOf_coe x).trans hx
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hbound := (x : Perm (Fin 7)).sum_cycleType_le
  rw [hk] at hbound
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hbound
  have hsign := Perm.mem_alternatingGroup.mp x.property
  rw [Perm.sign_of_cycleType', hk] at hsign
  have hkbound : k ≤ 2 := by omega
  have hk1 : k = 1 := by
    interval_cases k
    · norm_num at hsign
    · rfl
    · norm_num at hsign
  simpa [hk1] using hk

private theorem seven_involutions_isConj (x y : alternatingGroup (Fin 7))
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  apply alternatingGroup.isConj_of
    (Perm.isConj_iff_cycleType_eq.mpr ((seven_cycleType x hx).trans (seven_cycleType y hy).symm))
  rw [← Perm.sum_cycleType, seven_cycleType x hx]
  decide

namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : Source.SixLocalData D e) (F : RootFactor D e L)

private theorem involution_mem_factor {y : G} (hy : orderOf y = 2)
    (hc : y ∈ centralizer ({L.u * L.v} : Set G)) : y ∈ F.W := by
  have hn : zpowers (L.u * L.v) ≤ normalizer (F.W : Set G) := by
    apply zpowers_le.mpr
    apply centralizer_le_normalizer (F.W : Set G)
    intro w hw
    exact mem_centralizer_singleton_iff.mp (F.W_le_centralizer D e L hw)
  rw [F.centralizer_root, sup_comm] at hc
  obtain ⟨w, hw, r, hr, rfl⟩ := sup_factor F.W (zpowers (L.u * L.v)) hn hc
  have hr3 : r ^ 3 = 1 := by
    have hd := orderOf_dvd_of_mem_zpowers hr
    rw [root_order D e L] at hd
    exact orderOf_dvd_iff_pow_eq_one.mp hd
  have hwr : Commute w r := by
    have hsub : zpowers (L.u * L.v) ≤ centralizer ({w} : Set G) := by
      apply zpowers_le.mpr
      exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp (F.W_le_centralizer D e L hw)).symm
    exact (mem_centralizer_singleton_iff.mp (hsub hr)).symm
  have hy2 : (w * r) ^ 2 = 1 := hy ▸ pow_orderOf_eq_one (w * r)
  have hy3 : (w * r) ^ 3 = w * r := by rw [pow_succ, hy2, one_mul]
  rw [hwr.mul_pow, hr3, mul_one] at hy3
  exact hy3 ▸ F.W.pow_mem hw 3

private theorem pi_mu_isConj_mu : IsConj (pi D e * mu D e) (mu D e) := by
  let g := modelElement 4
  have hg : g * (modelElement 0 * modelElement 1) * g⁻¹ = modelElement 1 := by
    decide +kernel
  apply isConj_iff.mpr
  refine ⟨D.a10ModelEmbedding e g, ?_⟩
  simpa only [element, map_mul, map_inv] using congrArg (D.a10ModelEmbedding e) hg

private theorem centralizer_card_conj {x y : G} (h : IsConj x y) :
    Nat.card (centralizer ({x} : Set G)) = Nat.card (centralizer ({y} : Set G)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  let f := MulAut.conj g
  have he : f x = y := hg
  rw [← he]
  apply Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)
  intro a
  change a ∈ centralizer ({x} : Set G) ↔ f a ∈ centralizer ({f x} : Set G)
  simp only [mem_centralizer_singleton_iff, ← map_mul, f.injective.eq_iff]

/-- No ambient involution centralizes the explicit A₇ root factor. This is
Held's exclusion in the proof of 5.5, derived from the marked local geometry. -/
public theorem RootFactor.no_centralizing_involution [Finite G]
    (hcentralizer : Nat.card (centralizer ({D.a10NoncentralInvolution e} : Set G)) = 2880)
    (x : G) (hx : orderOf x = 2) : x ∉ centralizer (F.W : Set G) := by
  intro hxc
  let f := MulAut.conj (tau' D e)
  have hv : f L.v = (L.u * L.v)⁻¹ := by
    simpa only [f, MulAut.conj_apply, coordinate_inv D e 4 (by decide)] using tau'_v D e L
  have hcv : Commute L.v x := hxc L.v (F.A_le D e L L.v_mem)
  have hc : f x ∈ centralizer ({L.u * L.v} : Set G) := by
    have h : Commute (f L.v) (f x) := hcv.map f.toMonoidHom
    rw [hv] at h
    exact mem_centralizer_singleton_iff.mpr (Commute.inv_left_iff.mp h).symm.eq
  have hfo : orderOf (f x) = 2 := (f.orderOf_eq x).trans hx
  have hfw := involution_mem_factor D e L F hfo hc
  let y : F.W := ⟨f x, hfw⟩
  let m : F.W := ⟨pi D e * mu D e, F.A_le D e L L.pi_mu_mem⟩
  have hm : orderOf (pi D e * mu D e) = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp (pi_mu_isConj_mu D e)
    have horder := (MulAut.conj g).orderOf_eq (pi D e * mu D e)
    change orderOf (g * (pi D e * mu D e) * g⁻¹) = _ at horder
    rw [hg] at horder
    rw [← horder]
    exact orderOf_eq_prime (element_square D e 1 (by decide)) (element_ne_one D e 1)
  have hy : orderOf y = 2 := (Subgroup.orderOf_coe y).symm.trans hfo
  have hm' : orderOf m = 2 := (Subgroup.orderOf_coe m).symm.trans hm
  have hym : IsConj y m := by
    have h := seven_involutions_isConj (F.alternatingEquiv y) (F.alternatingEquiv m)
      ((F.alternatingEquiv.orderOf_eq y).trans hy) ((F.alternatingEquiv.orderOf_eq m).trans hm')
    simpa using F.alternatingEquiv.symm.toMonoidHom.map_isConj h
  have hconj : IsConj x (mu D e) :=
    (isConj_iff.mpr ⟨tau' D e, rfl⟩).trans ((F.W.subtype.map_isConj hym).trans (pi_mu_isConj_mu D e))
  have hC : Nat.card (centralizer ({x} : Set G)) = 2880 :=
    (centralizer_card_conj hconj).trans hcentralizer
  have hW : Nat.card F.W = 2520 := by
    rw [Nat.card_congr F.alternatingEquiv.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card]
    decide
  have hle : F.W ≤ centralizer ({x} : Set G) := by
    intro w hw
    exact mem_centralizer_singleton_iff.mpr (hxc w hw)
  have hd := card_dvd_of_le hle
  rw [hW, hC] at hd
  norm_num at hd

private theorem extension_two_cosets [Finite G] {x : G}
    (hx : x ∈ F.W ⊔ zpowers (mu' D e)) : x ∈ F.W ∨ x * mu' D e ∈ F.W := by
  classical
  obtain ⟨w, hw, t, ht, rfl⟩ := sup_factor F.W (zpowers (mu' D e))
    (zpowers_le.mpr (F.mu'_normalizes D e L)) hx
  have ho : orderOf (mu' D e) = 2 :=
    orderOf_eq_prime (element_square D e 2 (by decide)) (element_ne_one D e 2)
  rw [mem_zpowers_iff_mem_range_orderOf, ho] at ht
  have ht' : t = 1 ∨ t = mu' D e := by
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
    have hn' : n < 2 := Finset.mem_range.mp hn
    interval_cases n <;> simp
  rcases ht' with rfl | rfl
  · exact Or.inl (by simpa using hw)
  · exact Or.inr (by simpa only [mul_assoc, ← pow_two, element_square D e 2 (by decide), mul_one] using hw)

private theorem extension_index [Finite G] :
    (F.W.subgroupOf (F.W ⊔ zpowers (mu' D e))).index = 2 := by
  apply relIndex_eq_two_iff_exists_notMem_and.mpr
  refine ⟨mu' D e, mem_sup_right (mem_zpowers _), F.mu'_not_mem D e L, ?_⟩
  intro x hx
  exact (extension_two_cosets D e L F hx).symm

private theorem extension_card [Finite G] :
    Nat.card (F.W ⊔ zpowers (mu' D e) : Subgroup G) = 5040 := by
  have hc : Nat.card (F.W.subgroupOf (F.W ⊔ zpowers (mu' D e))) = 2520 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show F.W ≤ F.W ⊔ zpowers (mu' D e) from le_sup_left)).toEquiv,
      Nat.card_congr F.alternatingEquiv.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card]
    decide
  rw [← (F.W.subgroupOf (F.W ⊔ zpowers (mu' D e))).index_mul_card,
    extension_index D e L F, hc]

private theorem factor_centralizer_eq_one {x : G} (hx : x ∈ F.W)
    (hc : x ∈ centralizer (F.W : Set G)) : x = 1 := by
  have he : F.alternatingEquiv ⟨x, hx⟩ ∈ center (alternatingGroup (Fin 7)) := by
    rw [mem_center_iff]
    intro a
    obtain ⟨w, rfl⟩ := F.alternatingEquiv.surjective a
    rw [← map_mul, ← map_mul]
    apply congrArg F.alternatingEquiv
    apply Subtype.ext
    exact hc w w.property
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
  have h := F.alternatingEquiv.injective (he.trans (map_one F.alternatingEquiv).symm)
  exact congrArg Subtype.val h

private noncomputable def factorAutEquiv : MulAut F.W ≃* Perm (Fin 7) :=
  (MulAut.congr F.alternatingEquiv).trans
    (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)))
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))).symm

private theorem faithful_extension_equiv [Finite G]
    (hcentralizer : Nat.card (centralizer ({D.a10NoncentralInvolution e} : Set G)) = 2880) :
    Nonempty ((F.W ⊔ zpowers (mu' D e) : Subgroup G) ≃* Perm (Fin 7)) := by
  let X := F.W ⊔ zpowers (mu' D e)
  have hn : X ≤ normalizer (F.W : Set G) :=
    sup_le F.W.le_normalizer (zpowers_le.mpr (F.mu'_normalizes D e L))
  let a : X →* MulAut F.W := F.W.normalizerMonoidHom.comp (inclusion hn)
  have ha : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff a).mp
    apply bot_unique
    intro x hx
    have hxN : inclusion hn x ∈ F.W.normalizerMonoidHom.ker := hx
    rw [normalizerMonoidHom_ker] at hxN
    have hxc : (x : G) ∈ centralizer (F.W : Set G) := hxN
    have hxs : (x : G) ^ 2 ∈ F.W :=
      (F.W.subgroupOf X).sq_mem_of_index_two (extension_index D e L F) x
    have hx2 : (x : G) ^ 2 = 1 :=
      factor_centralizer_eq_one D e L F hxs ((centralizer (F.W : Set G)).pow_mem hxc 2)
    by_cases hx1 : (x : G) = 1
    · exact Subtype.ext hx1
    · exact False.elim (F.no_centralizing_involution D e L hcentralizer x
        (orderOf_eq_prime hx2 hx1) hxc)
  let f : X →* Perm (Fin 7) := (factorAutEquiv D e L F).toMonoidHom.comp a
  have hf : Function.Injective f := (factorAutEquiv D e L F).injective.comp ha
  refine ⟨MulEquiv.ofBijective f (hf.bijective_of_nat_card_le ?_)⟩
  rw [extension_card D e L F, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

/-- The symmetric-group clause of Held 5.5, conditional on the actual A₇ root
factor supplied by 5.4. Faithfulness and the exclusion of a centralizing
involution are proved, rather than imposed as additional premises. -/
public theorem RootFactor.exists_symmetricEquiv [Finite G] [IsSimpleGroup G]
    (_hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hcentralizer : Nat.card (centralizer ({D.a10NoncentralInvolution e} : Set G)) = 2880) :
    Nonempty ((F.W ⊔ zpowers (mu' D e) : Subgroup G) ≃* Perm (Fin 7)) :=
  faithful_extension_equiv D e L F hcentralizer

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction
