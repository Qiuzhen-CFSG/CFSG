module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SplitNormalizer.Inputs
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.QuotientFusion.Images
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Lifting the marked quotient A₅

Let B be the preimage of the recognized A₅ under the literal map
C_G(t) → C_G(t)/⟨t⟩. Its order is 120. Intersecting the marked Sylow
subgroup with B gives an elementary subgroup of order eight containing E
and t. The local involution census makes E closed under fusion in B,
so binary transfer gives a normal subgroup N of index two containing E
and avoiding t.

The quotient map restricts to an isomorphism N ≃ A₅. Perfectness then
identifies N with the derived subgroup of B, making its ambient image
normal relative to C_G(t). The cubic X₁ lies in both index-two kernels.
This constructs `LiftedFive`, the input to the marked splitting and
normalizer consumer, without assuming simplicity of G or a splitting.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1(1), printed p.260.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
variable {G : Type*} [Group G] [Finite G] {D : Seed G} {t : G}

private theorem preimage_card (F : LocalFrame D t) (Q : RecognizedQuotient F)
    (ht : orderOf t = 2) : Nat.card (Q.kernel.M.comap (quotientMap t)) = 120 := by
  have hi : (Q.kernel.M.comap (quotientMap t)).index = 2 :=
    (Q.kernel.M.index_comap_of_surjective (QuotientGroup.mk'_surjective _)).trans Q.kernel.index
  have h := (Q.kernel.M.comap (quotientMap t)).index_mul_card
  rw [hi, Q.kernel.centralizer_card ht Q.equiv] at h
  omega

private theorem image_E_le (F : LocalFrame D t) (Q : RecognizedQuotient F) :
    LocalFrame.quotientImage F.E ≤ Q.kernel.M := by
  rw [← Q.geometry.closed_eq, ← Q.kernel.intersection, subgroupOf_map_subtype]
  exact inf_le_left

private theorem exists_lift_kernel (F : LocalFrame D t) (Q : RecognizedQuotient F)
    (L : LocalCensus D) (ht : OtherInvolution D t) :
    ∃ N : Subgroup (Q.kernel.M.comap (quotientMap t)), N.Normal ∧ N.index = 2 ∧
      F.E ≤ N.map ((involutionCentralizer t).subtype.comp
        (Q.kernel.M.comap (quotientMap t)).subtype) ∧
      ∀ x : Q.kernel.M.comap (quotientMap t), (x : involutionCentralizer t) =
        centralInvolution t → x ∉ N := by
  classical
  let B := Q.kernel.M.comap (quotientMap t)
  let : Q.kernel.M.Normal := Q.kernel.normal
  let : B.Normal := inferInstance
  obtain ⟨S, hS⟩ := F.A.exists_subgroupOf_eq_of_normal B
  let j : S →* G := (involutionCentralizer t).subtype.comp (B.subtype.comp
    (S : Subgroup B).subtype)
  have hj : Function.Injective j :=
    (involutionCentralizer t).subtype_injective.comp
      (B.subtype_injective.comp (S : Subgroup B).subtype_injective)
  have hjA (x : S) : j x ∈ F.E ⊔ F.U := by
    rw [← F.A_eq]
    have hx : (x : B) ∈ (S : Subgroup B) := x.property
    rw [hS] at hx
    exact mem_map_of_mem _ hx
  have hEA (x : G) (hx : x ∈ F.E) :
      (⟨x, F.join_le_centralizer (mem_sup_left hx)⟩ : involutionCentralizer t) ∈
        (F.A : Subgroup (involutionCentralizer t)) := by
    rw [← F.quotient_A_eq]
    exact mem_sup_left hx
  have hEB (x : G) (hx : x ∈ F.E) :
      (⟨x, F.join_le_centralizer (mem_sup_left hx)⟩ : involutionCentralizer t) ∈ B :=
    image_E_le F Q (mem_map_of_mem _ hx)
  let V := F.E.comap j
  have hVmap : V.map j = F.E := by
    apply le_antisymm
    · exact map_comap_le j F.E
    · intro x hx
      let xc : involutionCentralizer t := ⟨x, F.join_le_centralizer (mem_sup_left hx)⟩
      let xb : B := ⟨xc, hEB x hx⟩
      have hxb : xb ∈ (S : Subgroup B) := by rw [hS]; exact hEA x hx
      exact mem_map.mpr ⟨⟨xb, hxb⟩, hx, rfl⟩
  have hVc : Nat.card V = 4 := by
    rw [← card_map_of_injective (K := V) hj, hVmap, F.E_card]
  have hSc : Nat.card S = 8 := by
    rw [S.card_eq_multiplicity, preimage_card F Q ht.1]
    decide +kernel
  have hVi : V.index = 2 := by
    have h := V.index_mul_card
    rw [hVc, hSc] at h
    omega
  have hpow (x : S) : x ^ 2 = 1 := by
    apply hj
    rw [map_pow, map_one]
    let : IsElementaryAbelian 2 (F.E ⊔ F.U : Subgroup G) := F.elementary
    exact elemPow_eq_one_of_isElementaryAbelian _ (hjA x)
  have hclosed (x y : S) (hx : orderOf x = 2)
      (hxy : IsConj (x : B) (y : B)) : x ∈ V ↔ y ∈ V := by
    have hconj : IsConj (j x) (j y) :=
      ((involutionCentralizer t).subtype.comp B.subtype).map_isConj hxy
    have hxo : orderOf (j x) = 2 := (orderOf_injective j hj x).trans hx
    have hyo : orderOf (j y) = 2 := hconj.choose_spec.orderOf_eq.symm.trans hxo
    change j x ∈ F.E ↔ j y ∈ F.E
    rw [← F.involution_fusion L (hjA x) hxo, ← F.involution_fusion L (hjA y) hyo]
    exact ⟨fun h => h.trans hconj, fun h => h.trans hconj.symm⟩
  have htB : centralInvolution t ∈ B := by
    change quotientMap t (centralInvolution t) ∈ Q.kernel.M
    have he : quotientMap t (centralInvolution t) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (mem_zpowers _)
    rw [he]
    exact Q.kernel.M.one_mem
  let tb : B := ⟨centralInvolution t, htB⟩
  have htS : tb ∈ (S : Subgroup B) := by
    rw [hS]
    change centralInvolution t ∈ (F.A : Subgroup (involutionCentralizer t))
    rw [← F.quotient_A_eq]
    exact mem_sup_right F.t_mem
  let w : S := ⟨tb, htS⟩
  have hw : orderOf w = 2 := by
    rw [← orderOf_injective j hj w]
    exact ht.1
  have hwV : w ∉ V := F.t_not_mem_E ht.1
  obtain ⟨N, hn, hi, hinter⟩ := S.exists_normal_index_two_of_involution_fusion V hVi
    (fun x hx => subset_closure ⟨hx, hpow x⟩) hclosed w hw hwV
  refine ⟨N, hn, hi, ?_, ?_⟩
  · intro x hx
    rw [← hVmap] at hx
    obtain ⟨v, hv, rfl⟩ := mem_map.mp hx
    have hvN : (v : B) ∈ N := by
      change v ∈ N.subgroupOf (S : Subgroup B)
      rw [hinter]
      exact hv
    exact mem_map.mpr ⟨v, hvN, rfl⟩
  · intro x hx hxN
    have hxt : x = tb := Subtype.ext hx
    have hwN : w ∈ N.subgroupOf (S : Subgroup B) := by
      change tb ∈ N
      rwa [← hxt]
    rw [hinter] at hwN
    exact hwV hwN

/-- Lift the marked quotient A₅ into the literal involution centralizer.
Transfer separates E from t, and perfectness makes the resulting complement
characteristic in the normal preimage. No simplicity assumption is needed. -/
theorem RecognizedQuotient.nonempty_liftedFive {F : LocalFrame D t}
    (Q : RecognizedQuotient F) (L : LocalCensus D) (ht : OtherInvolution D t) :
    Nonempty (LiftedFive F) := by
  classical
  let B := Q.kernel.M.comap (quotientMap t)
  let : Q.kernel.M.Normal := Q.kernel.normal
  let : B.Normal := inferInstance
  obtain ⟨N, hNn, hNi, hNE, hNt⟩ := exists_lift_kernel F Q L ht
  let : N.Normal := hNn
  let f : N →* Q.kernel.M :=
    ((quotientMap t).subgroupComap Q.kernel.M).comp N.subtype
  have hfi : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro x hx
    have hxk : ((x : B) : involutionCentralizer t) ∈ quotientKernel t :=
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)
    rcases (LocalFrame.quotient_mem_kernel_iff ht.1 _).mp hxk with h | h
    · exact Subtype.ext (Subtype.ext h)
    · exact (hNt (x : B) h x.property).elim
  have hNc : Nat.card N = 60 := by
    have h := N.index_mul_card
    rw [hNi, preimage_card F Q ht.1] at h
    omega
  have hMc : Nat.card Q.kernel.M = 60 :=
    (Nat.card_congr Q.equiv.toEquiv).trans card_A5
  let e : N ≃* A5 := (MulEquiv.ofBijective f
    (hfi.bijective_of_nat_card_le (by rw [hNc, hMc]))).trans Q.equiv
  let : Group.IsPerfect A5 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect N :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hderived : _root_.commutator B = N := by
    apply le_antisymm
    · have hc : Nat.card (B ⧸ N) = 2 := hNi
      let : IsCyclic (B ⧸ N) := isCyclic_of_prime_card hc
      exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
    · rw [← N.commutator_eq_self]
      exact commutator_mono le_top le_top
  let Kc := N.map B.subtype
  have hKc : Kc = ⁅B, B⁆ := by
    change N.map B.subtype = ⁅B, B⁆
    rw [← hderived, map_subtype_commutator]
  let : Kc.Normal := by rw [hKc]; infer_instance
  let C := involutionCentralizer t
  let K := Kc.map C.subtype
  have hKC : K ≤ C := map_subtype_le _
  have hKnormal : (K.subgroupOf C).Normal := by
    have he : K.subgroupOf C = Kc :=
      comap_map_eq_self_of_injective C.subtype_injective Kc
    rw [he]
    infer_instance
  let ec : N ≃* Kc := N.equivMapOfInjective B.subtype B.subtype_injective
  let eg : Kc ≃* K := Kc.equivMapOfInjective C.subtype C.subtype_injective
  refine ⟨{ K := K
            le_centralizer := hKC
            normal := hKnormal
            equiv := eg.symm.trans (ec.symm.trans e)
            E_le := ?_
            X1_le := ?_ }⟩
  · simpa only [K, Kc, map_map] using hNE
  · intro x hx
    let xc : C := ⟨x, F.X1_le hx⟩
    have hx3 : xc ^ 3 = 1 := by
      apply Subtype.ext
      have h := pow_card_eq_one' (x := (⟨x, hx⟩ : F.X1))
      rw [F.X1_card] at h
      exact congrArg (fun a : F.X1 => (a : G)) h
    have hxB : xc ∈ B := by
      change quotientMap t xc ∈ Q.kernel.M
      have hq3 : (quotientMap t xc) ^ 2 * quotientMap t xc = 1 := by
        rw [← pow_succ, ← map_pow, hx3, map_one]
      have hs := Q.kernel.M.sq_mem_of_index_two Q.kernel.index (quotientMap t xc)
      rw [eq_inv_of_mul_eq_one_left hq3] at hs
      exact Q.kernel.M.inv_mem_iff.mp hs
    let xb : B := ⟨xc, hxB⟩
    have hxb3 : xb ^ 2 * xb = 1 := by
      rw [← pow_succ]
      exact Subtype.ext hx3
    have hxN : xb ∈ N := by
      have hs := N.sq_mem_of_index_two hNi xb
      rw [eq_inv_of_mul_eq_one_left hxb3] at hs
      exact N.inv_mem_iff.mp hs
    exact mem_map.mpr ⟨xc, mem_map.mpr ⟨xb, hxN, rfl⟩, rfl⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
