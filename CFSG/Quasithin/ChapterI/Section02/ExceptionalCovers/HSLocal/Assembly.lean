module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule
public import Theory.GroupTheory.PCoreFromTwoNormalizers

/-!
# The HS lifting and core-square clauses of I.2.2(5)

The two-central cover calculation supplies the actual centralizer data needed
by the normalizer module argument. The latter excludes non-two-central images
of involutions in M. Since M has odd index, a conjugate of every involution of
K lies in M, giving the same exclusion throughout K. A lift of a quotient
involution has order dividing four, so every non-two-central lift has order
four. Consequently every noncentral involution of K has a two-central image,
and the distinguished-square calculation applies to its original centralizer
core, without an additional class-marking hypothesis.

The local constructions are reexported with their literal maps and subgroups:
X=O²(C_K(u)), R=O₂(X), M the normalizer preimage, Q=O₂(M), E=Φ(Q), and Qbar in
M/E. In particular the core image and A₅ quotient/action, order-four orbit,
order-seven decomposition, elementary eight and nonsplit binary module retain
the source incidences. The centralizer input to the normalizer theorem is
constructed here, not an extra hypothesis of the lifting conclusions.

The only earlier-source inputs are the center-order bound and genuine universal
B.4.8(2), whose parent producers are qt-i01-multiplier-j2-hs and
qt-b-04-natural-extensions. Restriction (i) has already been discharged by
central transfer in the imported local proofs. The exceptional-cover parent
retains the independent outer-inversion clause of (5b).

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, I.2.2(5),
printed pp.409–412 / PDF pp.420–423, especially the final HS paragraph.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.BlockNormalizer
open CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.ThreeCovers.CentralExtension
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
universe v
variable {K : Type v} [Group K] [Finite K] [Group.IsPerfect K]

/-- Every involution of the cover with nontrivial image has a two-central image.
Odd-index conjugacy applies the actual normalizer module obstruction. -/
theorem involution_image_twoCentral (h48 : EarlierB48Two.{v,v})
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (x : K) (hx : x ^ 2 = 1) (hximage : orderOf (modelMap e x) = 2) :
    TwoCentral (modelMap e x) := by
  obtain ⟨u, hu⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (center K))) e0
  have hu' : modelMap e u = e0 := hu
  have hindex : ¬ 2 ∣ (M e).index := by
    rw [M, index_comap_of_surjective baseNormalizer
      (e.surjective.comp (QuotientGroup.mk'_surjective (center K)))]
    exact ModelGeometry.normalizer_index_not_even
  have horder : orderOf x = 2 := orderOf_eq_prime hx (by
    intro h
    simp [h] at hximage)
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, horder, pow_one])
  obtain ⟨g, hg⟩ := exists_conj_overgroup_of_index_primeTo (zpowers x) (M e) hp hindex
  let y : M e := ⟨(MulAut.conj g) x, hg (mem_zpowers x)⟩
  have hy : y ^ 2 = 1 := by
    apply Subtype.ext
    change ((MulAut.conj g) x) ^ 2 = 1
    rw [← map_pow, hx, map_one]
  have himage : modelMap e (y : K) = (MulAut.conj (modelMap e g)) (modelMap e x) := by
    simp only [y, MulAut.conj_apply, map_mul, map_inv]
  have hyimage : orderOf (modelMap e (y : K)) = 2 := by
    rw [himage, MulEquiv.orderOf_eq, hximage]
  have hc := NormalizerModule.involution_image_twoCentral h48 e hZ u hu'
    (CentralizerRestriction.normalizerCentralizerInput e hZ u hu') y hy hyimage
  rw [himage] at hc
  have hc' := hc.map (MulAut.conj (modelMap e g)).symm
  simpa only [MulEquiv.symm_apply_apply] using hc'

/-- Every lift of the non-two-central HS class has order four. -/
theorem order_four_of_nonTwoCentral_image (h48 : EarlierB48Two.{v,v})
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (x : K) (hx : orderOf (modelMap e x) = 2)
    (hc : ¬ TwoCentral (modelMap e x)) : orderOf x = 4 := by
  have hxZ : x ^ 2 ∈ center K := by
    rw [← modelMap_ker e, MonoidHom.mem_ker, map_pow, ← hx, pow_orderOf_eq_one]
  have hx4 : x ^ 4 = 1 := by
    have h := pow_card_eq_one' (x := (⟨x ^ 2, hxZ⟩ : center K))
    rw [hZ] at h
    have h' := congrArg Subtype.val h
    simpa only [coe_pow, coe_one, ← pow_mul] using h'
  have hnot2 : x ^ 2 ≠ 1 := fun h => hc (involution_image_twoCentral h48 e hZ x h hx)
  obtain ⟨n, hn, ho⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show orderOf x ∣ 2 ^ 2 from orderOf_dvd_of_pow_eq_one hx4)
  interval_cases n
  · have hx1 : x = 1 := orderOf_eq_one_iff.mp ho
    exact (hnot2 (by rw [hx1, one_pow])).elim
  · exact (hnot2 (by simpa only [ho, pow_one] using pow_orderOf_eq_one x)).elim
  · exact ho

/-- The source square assertion, with no extra two-central marking. -/
theorem hasUniqueCoreSquareLift (h48 : EarlierB48Two.{v,v})
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : orderOf u = 2) (hun : u ∉ center K) : HasUniqueCoreSquareLift u := by
  have hus : u ^ 2 = 1 := by rw [← hu, pow_orderOf_eq_one]
  have himage : orderOf (modelMap e u) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, hus, map_one]
    · intro h
      apply hun
      rwa [← modelMap_ker e, MonoidHom.mem_ker]
  exact CentralizerRestriction.twoCentral_hasUniqueCoreSquareLift e hZ u himage
    (involution_image_twoCentral h48 e hZ u hus himage)

omit [Group.IsPerfect K] in
/-- The quotient convention used by the other exceptional-cover rows. -/
theorem twoCentral_lift_order_two
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : orderOf (QuotientGroup.mk' (center K) u) = 2)
    (hc : TwoCentral (QuotientGroup.mk' (center K) u)) : orderOf u = 2 :=
  order_two_of_twoCentral_image e hZ u ((e.orderOf_eq _).trans hu) (hc.map e)

/-- The literal central quotient, with its non-two-central mark retained. -/
theorem nonTwoCentral_lift_order_four (h48 : EarlierB48Two.{v,v})
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : orderOf (QuotientGroup.mk' (center K) u) = 2)
    (hc : ¬ TwoCentral (QuotientGroup.mk' (center K) u)) : orderOf u = 4 := by
  apply order_four_of_nonTwoCentral_image h48 e hZ u ((e.orderOf_eq _).trans hu)
  intro h
  exact hc (by simpa only [modelMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply] using h.map e.symm)

omit [Group.IsPerfect K] in
/-- I.2.2(5a) for the actual central quotient of an HS cover. -/
theorem twoCentral_involution_lifting
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2) :
    ∀ x : K ⧸ center K, IsSylowCentralInvolution x →
      ∃ u : K, QuotientGroup.mk' (center K) u = x ∧ orderOf u = 2 := by
  rintro x ⟨ho, P, hxP, hP⟩
  have hc : TwoCentral x := by
    refine ⟨P, hxP, mem_center_iff.mpr ?_⟩
    intro y
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hP y.property))
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (center K) x
  exact ⟨u, rfl, twoCentral_lift_order_two e hZ u ho hc⟩

/-- The lifting input consumed by the parent's outer-inversion argument. -/
theorem nonTwoCentral_involution_lifting (h48 : EarlierB48Two.{v,v})
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2) :
    NonTwoCentralInvolutionLifting K := by
  intro x hx hc
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (center K) x
  exact ⟨u, rfl, nonTwoCentral_lift_order_four h48 e hZ u hx hc⟩

/-- The HS row of I.2.2(5a), the lifting clause of (5b), and (5c).
The parent supplies the multiplier center bound and genuine B.4.8(2), and
retains the independent outer-inversion clause of (5b). -/
theorem lifting_and_core_square (h48 : EarlierB48Two.{v,v})
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2) :
    (∀ x : K ⧸ center K, IsSylowCentralInvolution x →
      ∃ u : K, QuotientGroup.mk' (center K) u = x ∧ orderOf u = 2) ∧
    NonTwoCentralInvolutionLifting K ∧
    (∀ u : K, orderOf u = 2 → u ∉ center K → HasUniqueCoreSquareLift u) :=
  ⟨twoCentral_involution_lifting e hZ, nonTwoCentral_involution_lifting h48 e hZ,
    hasUniqueCoreSquareLift h48 e hZ⟩

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
