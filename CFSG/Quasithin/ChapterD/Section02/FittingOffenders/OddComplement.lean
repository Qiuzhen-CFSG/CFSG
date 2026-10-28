module

public import CFSG.Quasithin.ChapterD.Section02.Inheritance
public import Theory.Representation.GoldschmidtONan.Basic
public import Theory.Representation.BinaryOffender.FaithfulRankOne
public import Theory.Representation.BinaryOffender.InvolutionRatio
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.Representation.BinaryOffender.OddOrderSmallCodimension
public import Theory.Representation.BinaryOffender.UniformFixedSpace
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration
public import Theory.GroupAction.HyperplaneCommutatorGeneration

/-!
# Centralizing the fixed complement of the three-core

Aschbacher--Smith, *The Classification of Quasithin Groups*, D.2.14(5),
printed pp.185--187 of `refs/quasithin.pdf` (1 March 2004 manuscript).

Odd averaging gives the invariant splitting `V = [V,P] ⊕ C_V(P)`.
The action of A on the moved summand is faithful: its kernel centralizes
P, and `C_A(P)=1`. Coprime hyperplane generation and `[P,A]=P` then
exclude fixed codimension at most one for that faithful four-group action.
This uses the odd core and its full movement, not just an abstract faithful
four-group representation.

Full movement by `P Q` gives `C_V(P) = [C_V(P),Q]`. On this complement,
if A had fixed codimension at most two, each displacement image of an
actor element would have dimension at most two. The commuting Q preserves
that image. Since its order is prime to six, its binary action there is
trivial. Equivariance and full Q-movement force the displacement itself
to vanish. This proves the source's lower bound three for a noncentral
complement, using displacement images in place of the quotient by `C_W(A)`.
Additivity of fixed codimensions now contradicts the budget four.

The last theorem applies the argument to the original starred offender
and `P = O₃(G)`, deriving that budget from its action ratio. The earlier
core reductions and the explicit complementary subgroup Q remain inputs.
No unconditional form of all of D.2.14 is asserted. The parent assembly
constructs Q and supplies its centralization from D.2.13.
-/

public section

namespace CFSG.Quasithin.ChapterD.OddComplement
open Representation.BinaryOffender Subgroup
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem odd_fixed_moved_complement {Z : Subgroup G}
    (hZ : Odd (Nat.card Z)) :
    IsCompl (subspaceCommutator ρ ⊤ Z) (fixedSpace ρ Z) := by
  have hs := Representation.GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) hZ
  have he : Representation.RegularCyclicNormalClosure.displacementSpan ρ Z ⊤ =
      subspaceCommutator ρ ⊤ Z := by
    unfold Representation.RegularCyclicNormalClosure.displacementSpan subspaceCommutator
    congr 1
    ext v
    simp only [Set.mem_ofPred_eq, eq_comm]
  rw [he] at hs
  exact hs.symm

private theorem moved_on_invariant_eq_inf (D : Submodule (ZMod 2) V) (Z : Subgroup G)
    (hZ : Odd (Nat.card Z)) (hD : Z ≤ subspaceStabilizer ρ D) :
    subspaceCommutator ρ D Z = D ⊓ subspaceCommutator ρ ⊤ Z := by
  classical
  let := Fintype.ofFinite Z
  have hcard : (Fintype.card Z : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := hZ
    rw [← Nat.card_eq_fintype_card, hk]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, Nat.cast_one, zero_add]
  let N : V →ₗ[ZMod 2] V := ∑ z : Z, ρ z
  have hN (v : V) : N v = ∑ z : Z, ρ z v := LinearMap.sum_apply _ _ _
  have hfixed (v : V) : N v ∈ fixedSpace ρ Z := by
    intro z
    change ρ (z : G) (N v) = N v
    simp only [hN, map_sum, ← Module.End.mul_apply, ← map_mul]
    exact (Group.mulLeft_bijective z).sum_comp (fun y : Z => ρ y v)
  have hdiff (v : V) (hv : v ∈ D) : N v - v ∈ subspaceCommutator ρ D Z := by
    have hm : (∑ z : Z, (ρ z v - v)) ∈ subspaceCommutator ρ D Z :=
      Submodule.sum_mem _ fun z _ => Submodule.subset_span ⟨z, z.property, v, hv, rfl⟩
    rw [Finset.sum_sub_distrib, ← hN, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul (ZMod 2), hcard, one_smul] at hm
    exact hm
  have hm := subspaceCommutator_mono_left ρ (show D ≤ ⊤ from le_top) Z
  refine le_antisymm (le_inf (subspaceCommutator_le_of_invariant ρ hD) hm) ?_
  intro v hv
  have hNu : N v ∈ subspaceCommutator ρ ⊤ Z := by
    simpa only [sub_add_cancel] using
      (subspaceCommutator ρ ⊤ Z).add_mem (hm (hdiff v hv.1)) hv.2
  have hz : N v = 0 := (odd_fixed_moved_complement ρ hZ).disjoint.le_bot ⟨hNu, hfixed v⟩
  simpa only [hz, zero_sub, neg_neg] using (subspaceCommutator ρ D Z).neg_mem (hdiff v hv.1)

omit [Finite G] in
private theorem fixedSpace_split (U W : Submodule (ZMod 2) V) (A : Subgroup G)
    (hc : IsCompl U W) (hU : A ≤ subspaceStabilizer ρ U)
    (hW : A ≤ subspaceStabilizer ρ W) :
    (U ⊓ fixedSpace ρ A) ⊔ (W ⊓ fixedSpace ρ A) = fixedSpace ρ A := by
  refine le_antisymm (sup_le inf_le_right inf_le_right) ?_
  intro v hv
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ U ⊔ W by rw [hc.sup_eq_top]; trivial)
  have he (a : A) : (⟨ρ a u, (hU a.property u).2 hu⟩ : U) = ⟨u, hu⟩ ∧
      (⟨ρ a w, (hW a.property w).2 hw⟩ : W) = ⟨w, hw⟩ := by
    have hh := (U.prodEquivOfIsCompl W hc).injective
      (show (U.prodEquivOfIsCompl W hc)
          (⟨ρ a u, (hU a.property u).2 hu⟩, ⟨ρ a w, (hW a.property w).2 hw⟩) =
        (U.prodEquivOfIsCompl W hc) (⟨u, hu⟩, ⟨w, hw⟩) from
          (map_add (ρ a) u w).symm.trans (hv a))
    exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
  exact Submodule.mem_sup.mpr ⟨u, ⟨hu, fun a => congrArg Subtype.val (he a).1⟩,
    w, ⟨hw, fun a => congrArg Subtype.val (he a).2⟩, rfl⟩


variable [FiniteDimensional (ZMod 2) V]

private theorem no_faithful_four_coatom (hf : Function.Injective ρ)
    (P A : Subgroup G) (hP : IsPGroup 3 P) (hA : IsElementaryTwo A)
    (hcA : Nat.card A = 4) (hPA : ⁅P, A⁆ = P)
    (hm : subspaceCommutator ρ ⊤ P = ⊤) (hd : fixedCodim ρ A ≤ 1) : False := by
  let : IsElementaryAbelian 2 A := hA.2
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let F := fixedSpace ρ A
  let S := subspaceStabilizer ρ F
  have hAS : A ≤ S := fixedSpace_subactor_stabilized ρ hA le_rfl
  have hgen := iSup_hyperplane_centralizer_commutator (by decide : 3 ≠ 2) P A hP
    (le_normalizer_iff_commutator_le_left.mpr hPA.le)
  have hPS : P ≤ S := by
    rw [← hPA, ← hgen]
    apply iSup₂_le
    intro B hB
    let B₀ := B.map A.subtype
    have hBA : B₀ ≤ A := map_subtype_le B
    have hcard : Nat.card B₀ = 2 := by
      have hh := B.card_mul_index
      rw [hB, hcA] at hh
      have hmap : Nat.card B₀ = Nat.card B := card_map_of_injective A.subtype_injective
      omega
    have hBn : B₀ ≠ ⊥ := by intro he; rw [he, card_bot] at hcard; omega
    have hpos := fixedCodim_pos_of_faithful ρ hf hBn
    have hle := Submodule.finrank_mono (fixedSpace_antitone ρ hBA)
    have ha := fixedCodim_add_finrank ρ A
    have hb := fixedCodim_add_finrank ρ B₀
    have he : fixedSpace ρ B₀ = F :=
      (fixedSpace_eq_of_fixedCodim_eq ρ hBA (by omega)).symm
    have hCS : P ⊓ centralizer (B₀ : Set G) ≤ S := by
      dsimp only [S]
      rw [← he]
      exact fixedSpace_invariant_normalizer ρ
        (inf_le_right.trans (centralizer_le_normalizer _))
    apply commutator_le.mpr
    intro p hp a ha
    exact S.mul_mem (S.mul_mem (S.mul_mem (hCS hp) (hAS ha)) (S.inv_mem (hCS hp)))
      (S.inv_mem (hAS ha))
  have hFP : F ≤ fixedSpace ρ P := by
    rw [← hPA]
    exact le_fixedSpace_commutator_of_invariant ρ hPS le_rfl
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hc := odd_fixed_moved_complement ρ (hn ▸ (by decide : Odd 3).pow)
  have hF : F = ⊥ := le_bot_iff.mp (by
    intro v hv
    have hu : v ∈ subspaceCommutator ρ ⊤ P := by rw [hm]; trivial
    exact hc.disjoint.le_bot ⟨hu, hFP hv⟩)
  have hvdim : Module.finrank (ZMod 2) V ≤ 1 := by
    have hh := fixedCodim_add_finrank ρ A
    change fixedCodim ρ A + Module.finrank (ZMod 2) F = _ at hh
    rw [hF, finrank_bot, add_zero] at hh
    omega
  obtain ⟨a, ha, han⟩ := (Subgroup.nontrivial_iff_exists_ne_one A).mp
    ((Subgroup.nontrivial_iff_ne_bot A).mpr hA.1)
  have ho : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) han
  have hne : zpowers a ≠ ⊥ := by
    intro he
    exact han (he.le (mem_zpowers a))
  have hpos := fixedCodim_pos_of_faithful ρ hf hne
  have hhalf := (involution_actor_rank_and_fixedCodim ρ a ho).2.2.2
  omega

omit [Finite G] in
/-- Fixed codimensions add on an invariant direct sum. -/
private theorem fixedCodim_split (U W : Submodule (ZMod 2) V) (A : Subgroup G)
    (hc : IsCompl U W) (hU : A ≤ subspaceStabilizer ρ U)
    (hW : A ≤ subspaceStabilizer ρ W) :
    fixedCodim ρ A =
      fixedCodim (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) +
      fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) := by
  have hsum := fixedSpace_split ρ U W A hc hU hW
  have hdis : Disjoint (U ⊓ fixedSpace ρ A) (W ⊓ fixedSpace ρ A) :=
    hc.disjoint.mono inf_le_left inf_le_left
  have hf := Submodule.finrank_sup_add_finrank_inf_eq
    (U ⊓ fixedSpace ρ A) (W ⊓ fixedSpace ρ A)
  rw [hsum, hdis.eq_bot, finrank_bot, add_zero] at hf
  have ht := Submodule.finrank_add_eq_of_isCompl hc
  have hn := fixedCodim_add_finrank ρ A
  have hu := fixedCodim_restrictedSubgroup ρ U A hU
  have hw := fixedCodim_restrictedSubgroup ρ W A hW
  have hlu := Submodule.finrank_mono (show U ⊓ fixedSpace ρ A ≤ U from inf_le_left)
  have hlw := Submodule.finrank_mono (show W ⊓ fixedSpace ρ A ≤ W from inf_le_left)
  omega

/-- The full odd-core movement excludes a faithful four-group with fixed
codimension one. The conclusion is false without these core hypotheses. -/
private theorem two_le_fixedCodim_of_faithful_four (hf : Function.Injective ρ)
    (P A : Subgroup G) (hP : IsPGroup 3 P) (hA : IsElementaryTwo A)
    (hcA : Nat.card A = 4) (hPA : ⁅P, A⁆ = P)
    (hm : subspaceCommutator ρ ⊤ P = ⊤) : 2 ≤ fixedCodim ρ A := by
  by_contra hn
  exact no_faithful_four_coatom ρ hf P A hP hA hcA hPA hm (by omega)

omit [Finite G] in
private theorem small_subspace_fixed (D : Submodule (ZMod 2) V) (Q : Subgroup G)
    (hQ : Nat.Coprime (Nat.card Q) 6) (hst : Q ≤ subspaceStabilizer ρ D)
    (hd : Module.finrank (ZMod 2) D ≤ 2) : D ≤ fixedSpace ρ Q := by
  let σ := subspaceImageRepresentation ρ D
  let Q' := restrictedSubgroup ρ D Q
  have hcard : Nat.card Q' ∣ Nat.card Q := by
    exact ⟨Nat.card (subspaceKernel ρ D Q),
      (card_subspaceKernel_mul_image ρ D Q hst).symm.trans (Nat.mul_comm _ _)⟩
  have hcop : Nat.Coprime (Nat.card Q') 6 := hQ.coprime_dvd_left hcard
  have he (q : Q') : q = 1 := by
    have ho : Odd (orderOf (q : subspaceActionImage ρ D)) := by
      have hodd := (hcop.coprime_dvd_right (by decide : 2 ∣ 6)).odd_of_right
      simpa only [Subgroup.orderOf_coe] using hodd.of_dvd_nat (orderOf_dvd_natCard q)
    have hc : fixedCodim σ (zpowers (q : subspaceActionImage ρ D)) ≤ 2 := by
      have hh := fixedCodim_add_finrank σ (zpowers (q : subspaceActionImage ρ D))
      omega
    have ht := orderOf_dvd_three_of_odd_fixedCodim_le_two σ
      (subspaceImageRepresentation_injective ρ D) q ho hc
    have hdiv : orderOf q ∣ 3 := by simpa only [Subgroup.orderOf_coe] using ht
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (hcop.coprime_dvd_right (by decide : 3 ∣ 6)) (orderOf_dvd_natCard q) hdiv)
  intro v hv q
  let q' : Q' := ⟨subspaceActionHom ρ D ⟨q, hst q.property⟩,
    ⟨⟨q, hst q.property⟩, q.property, rfl⟩⟩
  have hh := congrArg (fun z : Q' => (σ z ⟨v, hv⟩ : D)) (he q')
  have hvv : σ q' ⟨v, hv⟩ = ⟨v, hv⟩ := by simpa only [Subgroup.coe_one, map_one, Module.End.one_apply] using hh
  exact congrArg Subtype.val hvv

omit [Finite G] in
/-- A commuting group of order prime to six that moves the whole module
forces any nontrivial actor to have fixed codimension at least three.
This is proved on the literal displacement images of the actor elements. -/
private theorem fixedSpace_eq_top_of_coprime_six (Q A : Subgroup G)
    (hQ : Nat.Coprime (Nat.card Q) 6) (hQA : ⁅Q,A⁆ = ⊥)
    (hm : subspaceCommutator ρ ⊤ Q = ⊤) (hd : fixedCodim ρ A ≤ 2) :
    fixedSpace ρ A = ⊤ := by
  apply top_unique
  intro v _ a
  let N : V →ₗ[ZMod 2] V := ρ a - LinearMap.id
  have hcomm (q : Q) (w : V) : ρ q (ρ a w) = ρ a (ρ q w) := by
    have he := (commutator_eq_bot_iff_le_centralizer.mp hQA q.property) a a.property
    simp only [← Module.End.mul_apply, ← map_mul]
    rw [he]
  have hNcomm (q : Q) (w : V) : ρ q (N w) = N (ρ q w) := by
    change ρ q (ρ a w - w) = ρ a (ρ q w) - ρ q w
    rw [map_sub, hcomm]
  have hst : Q ≤ subspaceStabilizer ρ N.range := by
    apply le_subspaceStabilizer
    rintro q hq _ ⟨w, rfl⟩
    exact ⟨ρ q w, (hNcomm ⟨q, hq⟩ w).symm⟩
  have hdim : Module.finrank (ZMod 2) N.range ≤ 2 := by
    have he := fixedCodim_zpowers_eq_displacement_rank ρ (a : G)
    have hle := Submodule.finrank_mono
      (fixedSpace_antitone ρ (zpowers_le.mpr a.property))
    have ha := fixedCodim_add_finrank ρ A
    have hz := fixedCodim_add_finrank ρ (zpowers (a : G))
    change fixedCodim ρ (zpowers (a : G)) = Module.finrank (ZMod 2) N.range at he
    omega
  have hfix := small_subspace_fixed ρ N.range Q hQ hst hdim
  have hkill : subspaceCommutator ρ ⊤ Q ≤ N.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, hq, w, _, rfl⟩
    change N (ρ q w - w) = 0
    have he : ρ q (N w) = N w := hfix ⟨w, rfl⟩ ⟨q, hq⟩
    rw [map_sub, ← hNcomm ⟨q, hq⟩, he, sub_self]
  have hz : N v = 0 := hkill (by rw [hm]; trivial)
  exact sub_eq_zero.mp hz
end CFSG.Quasithin.ChapterD.OddComplement

namespace CFSG.Quasithin.ChapterD.OddComplement
open Representation.BinaryOffender Subgroup
open scoped Pointwise
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem card_restricted_dvd (D : Submodule (ZMod 2) V) (B : Subgroup G)
    (hB : B ≤ subspaceStabilizer ρ D) :
    Nat.card (restrictedSubgroup ρ D B) ∣ Nat.card B := by
  exact ⟨Nat.card (subspaceKernel ρ D B),
    (card_subspaceKernel_mul_image ρ D B hB).symm.trans (Nat.mul_comm _ _)⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem restricted_commutator_bot (D : Submodule (ZMod 2) V)
    (B C : Subgroup G) (hB : B ≤ subspaceStabilizer ρ D)
    (hC : C ≤ subspaceStabilizer ρ D) (hBC : ⁅B,C⁆ = ⊥) :
    ⁅restrictedSubgroup ρ D B, restrictedSubgroup ρ D C⁆ = ⊥ := by
  have he : ⁅B.subgroupOf (subspaceStabilizer ρ D),
      C.subgroupOf (subspaceStabilizer ρ D)⁆ = ⊥ := by
    apply Subgroup.map_injective (subspaceStabilizer ρ D).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hB,
      Subgroup.map_subgroupOf_eq_of_le hC, hBC, Subgroup.map_bot]
  unfold restrictedSubgroup
  rw [← Subgroup.map_commutator, he, Subgroup.map_bot]

omit [FiniteDimensional (ZMod 2) V] in
/-- Faithfulness on the original module puts the kernel on the moved
summand inside the centralizer of the odd core. -/
private theorem moved_kernel_le_centralizer (hf : Function.Injective ρ)
    (P A : Subgroup G) (hodd : Odd (Nat.card P))
    (hAP : A ≤ normalizer (P : Set G)) :
    subspaceKernel ρ (subspaceCommutator ρ ⊤ P) A ≤ A ⊓ centralizer (P : Set G) := by
  let U := subspaceCommutator ρ ⊤ P
  let W := fixedSpace ρ P
  have hs := odd_fixed_moved_complement ρ hodd
  have hPst : P ≤ subspaceStabilizer ρ U := subspaceCommutator_invariant ρ ⊤ P
  have hAst : A ≤ subspaceStabilizer ρ W := fixedSpace_invariant_normalizer ρ hAP
  intro a ha
  refine ⟨ha.1, ?_⟩
  intro p hp
  apply hf
  ext v
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ U ⊔ W by rw [hs.sup_eq_top]; trivial)
  have hau : ρ a u = u := ha.2 u hu
  have hapu : ρ a (ρ p u) = ρ p u := ha.2 (ρ p u) ((hPst hp u).2 hu)
  have hpw : ρ p w = w := hw ⟨p, hp⟩
  have hpaw : ρ p (ρ a w) = ρ a w := ((hAst ha.1 w).2 hw) ⟨p, hp⟩
  simp only [map_mul, Module.End.mul_apply, map_add]
  rw [hau, hpaw, hapu, hpw]

/-- The actual action image on `[V,P]` spends at least two codimensions.
The faithfulness of A on P is transported through its literal action map. -/
theorem moved_fixedCodim_ge_two (hf : Function.Injective ρ)
    (P A : Subgroup G) (hP : IsPGroup 3 P) (hA : IsElementaryTwo A)
    (hcA : Nat.card A = 4) (hAP : A ≤ normalizer (P : Set G))
    (hfaith : A ⊓ centralizer (P : Set G) = ⊥) (hPA : ⁅P,A⁆ = P) :
    2 ≤ fixedCodim (subspaceImageRepresentation ρ (subspaceCommutator ρ ⊤ P))
      (restrictedSubgroup ρ (subspaceCommutator ρ ⊤ P) A) := by
  let U := subspaceCommutator ρ ⊤ P
  let σ := subspaceImageRepresentation ρ U
  let P' := restrictedSubgroup ρ U P
  let A' := restrictedSubgroup ρ U A
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hodd : Odd (Nat.card P) := hn ▸ (by decide : Odd 3).pow
  have hPst : P ≤ subspaceStabilizer ρ U := subspaceCommutator_invariant ρ ⊤ P
  have hAst : A ≤ subspaceStabilizer ρ U :=
    subspaceCommutator_invariant_normalizer ρ (le_subspaceStabilizer ρ ⊤ (by simp)) hAP
  have hk : subspaceKernel ρ U A = ⊥ := by
    apply le_bot_iff.mp
    exact (moved_kernel_le_centralizer ρ hf P A hodd hAP).trans_eq hfaith
  have hc : Nat.card A' = 4 := by
    have hh := card_subspaceKernel_mul_image ρ U A hAst
    simpa only [hk, card_bot, one_mul, hcA] using hh
  have hAn : ¬ U ≤ fixedSpace ρ A := by
    intro he
    have ha : A ≤ subspaceKernel ρ U A := by
      intro a ha
      exact ⟨ha, fun v hv => he hv ⟨a, ha⟩⟩
    exact hA.1 (le_bot_iff.mp (ha.trans_eq hk))
  have hA' := hA.restrictedSubgroup ρ U hAst hAn
  have hP' : IsPGroup 3 P' := hP.comap_subtype.map _
  have hm : subspaceCommutator σ ⊤ P' = ⊤ := by
    apply restricted_commutator_eq_top ρ U P hPst
    rw [moved_on_invariant_eq_inf ρ U P hodd hPst, inf_idem]
  exact two_le_fixedCodim_of_faithful_four σ (subspaceImageRepresentation_injective ρ U)
    P' A' hP' hA' hc (restrictedSubgroup_commutator ρ U hPst hAst hPA) hm

omit [FiniteDimensional (ZMod 2) V] in
/-- Full movement by the odd product `P Q` makes the P-fixed summand fully
moved by Q. Both the fixed space and the action image are the original ones. -/
theorem fixed_complement_moved (P Q : Subgroup G) [P.Normal]
    (hP : IsPGroup 3 P) (hQ : Nat.Coprime (Nat.card Q) 6)
    (hm : subspaceCommutator ρ ⊤ (P ⊔ Q) = ⊤) :
    subspaceCommutator ρ (fixedSpace ρ P) Q = fixedSpace ρ P := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hPodd : Odd (Nat.card P) := hn ▸ (by decide : Odd 3).pow
  have hQodd : Odd (Nat.card Q) :=
    (hQ.coprime_dvd_right (by decide : 2 ∣ 6)).odd_of_right
  have hdis : Disjoint P Q := disjoint_of_coprime_natCard (by
    rw [hn]
    exact (hQ.coprime_dvd_right (by decide : 3 ∣ 6)).symm.pow_left n)
  have hodd : Odd (Nat.card (P ⊔ Q : Subgroup G)) := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint P Q le_normalizer_of_normal hdis]
    exact hPodd.mul hQodd
  have hzero : fixedSpace ρ (P ⊔ Q) = ⊥ := by
    simpa only [hm, top_inf_eq] using (odd_fixed_moved_complement ρ hodd).disjoint.eq_bot
  let W := fixedSpace ρ P
  let σ := subspaceImageRepresentation ρ W
  let Q' := restrictedSubgroup ρ W Q
  have hst : Q ≤ subspaceStabilizer ρ W :=
    fixedSpace_invariant_normalizer ρ le_normalizer_of_normal
  have hQ'odd : Odd (Nat.card Q') := hQodd.of_dvd_nat (card_restricted_dvd ρ W Q hst)
  have hfixed : fixedSpace σ Q' = ⊥ := by
    apply le_bot_iff.mp
    intro w hw
    have hwQ : (w : V) ∈ fixedSpace ρ Q := by
      exact (fixedSpace_restrictedSubgroup ρ W Q hst).le hw
    have hwPQ : (w : V) ∈ fixedSpace ρ (P ⊔ Q) := by
      intro x
      have hx : (x : G) ∈ (P : Set G) * (Q : Set G) := by
        rw [← normal_mul P Q]
        exact x.property
      obtain ⟨p, hp, q, hq, he⟩ := hx
      change ρ (x : G) (w : V) = w
      rw [← he, map_mul, Module.End.mul_apply]
      have hqf : ρ q (w : V) = w := hwQ ⟨q, hq⟩
      rw [hqf]
      exact w.property ⟨p, hp⟩
    exact Subtype.ext (hzero.le hwPQ)
  have hfull : subspaceCommutator σ ⊤ Q' = ⊤ := by
    simpa only [hfixed, sup_bot_eq] using (odd_fixed_moved_complement σ hQ'odd).sup_eq_top
  have hh := congrArg (Submodule.map W.subtype) hfull
  simpa only [σ, Q', subspaceCommutator_restricted_map ρ W Q hst,
    Submodule.map_top, Submodule.range_subtype] using hh

/-- The source fixed-complement argument, with the preceding core reductions
explicit. No component codimension estimate is assumed. -/
theorem fixed_complement_centralized (hf : Function.Injective ρ)
    (P A Q : Subgroup G) [P.Normal]
    (hP : IsPGroup 3 P) (hA : IsElementaryTwo A) (hcA : Nat.card A = 4)
    (hfaith : A ⊓ centralizer (P : Set G) = ⊥) (hPA : ⁅P,A⁆ = P)
    (hQ : Nat.Coprime (Nat.card Q) 6) (hQA : ⁅Q,A⁆ = ⊥)
    (hm : subspaceCommutator ρ ⊤ (P ⊔ Q) = ⊤) (hd : fixedCodim ρ A ≤ 4) :
    fixedSpace ρ P ≤ fixedSpace ρ A := by
  let U := subspaceCommutator ρ ⊤ P
  let W := fixedSpace ρ P
  have hAP : A ≤ normalizer (P : Set G) := le_normalizer_of_normal
  have hAU : A ≤ subspaceStabilizer ρ U :=
    subspaceCommutator_invariant_normalizer ρ (le_subspaceStabilizer ρ ⊤ (by simp)) hAP
  have hAW : A ≤ subspaceStabilizer ρ W := fixedSpace_invariant_normalizer ρ hAP
  have hQW : Q ≤ subspaceStabilizer ρ W :=
    fixedSpace_invariant_normalizer ρ le_normalizer_of_normal
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hc := odd_fixed_moved_complement ρ (hn ▸ (by decide : Odd 3).pow)
  have hsplit := fixedCodim_split ρ U W A hc hAU hAW
  have htwo := moved_fixedCodim_ge_two ρ hf P A hP hA hcA hAP hfaith hPA
  change 2 ≤ fixedCodim (subspaceImageRepresentation ρ U) (restrictedSubgroup ρ U A) at htwo
  have hsmall : fixedCodim (subspaceImageRepresentation ρ W)
      (restrictedSubgroup ρ W A) ≤ 2 := by omega
  have hQ' : Nat.Coprime (Nat.card (restrictedSubgroup ρ W Q)) 6 :=
    hQ.coprime_dvd_left (card_restricted_dvd ρ W Q hQW)
  have hfix := fixedSpace_eq_top_of_coprime_six (subspaceImageRepresentation ρ W)
    (restrictedSubgroup ρ W Q) (restrictedSubgroup ρ W A) hQ'
    (restricted_commutator_bot ρ W Q A hQW hAW hQA)
    (restricted_commutator_eq_top ρ W Q hQW (fixed_complement_moved ρ P Q hP hQ hm))
    hsmall
  intro w hw
  exact (fixedSpace_restrictedSubgroup ρ W A hAW).le
    (show (⟨w,hw⟩ : W) ∈ fixedSpace (subspaceImageRepresentation ρ W)
      (restrictedSubgroup ρ W A) by rw [hfix]; trivial)
end CFSG.Quasithin.ChapterD.OddComplement

namespace CFSG.Quasithin.ChapterD.OddComplement
open Representation.BinaryOffender Subgroup
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- D.2.14(5) after the stated elementary-core and complementary-factor
reductions. The two component codimension bounds are conclusions of the
proof, not hypotheses. The stronger general argument above needs only that
P is a three-group; the extra hypotheses here retain the exact source-stage
contract. -/
theorem fixed_complement_commutator_eq_bot (hf : Function.Injective ρ)
    (P A Q : Subgroup G) [P.Normal] [Q.Normal]
    (hP : IsElementaryAbelian 3 P) {s : ℕ}
    (_hcP : Nat.card P = 3 ^ s) (_hs : s = 2 ∨ s = 3)
    (hA : IsElementaryAbelian 2 A) (hcA : Nat.card A = 4)
    (_hAP : A ≤ normalizer (P : Set G))
    (hfaith : A ⊓ centralizer (P : Set G) = ⊥)
    (_hcommon : P ⊓ centralizer (A : Set G) = ⊥) (hPA : ⁅P,A⁆ = P)
    (hQ : Nat.Coprime (Nat.card Q) 6) (_hPQ : ⁅P,Q⁆ = ⊥) (hQA : ⁅Q,A⁆ = ⊥)
    (hm : subspaceCommutator ρ ⊤ (P ⊔ Q) = ⊤) (hd : fixedCodim ρ A ≤ 4) :
    subspaceCommutator ρ (fixedSpace ρ P) A = ⊥ := by
  let : IsElementaryAbelian 3 P := hP
  have hAn : A ≠ ⊥ := by intro he; rw [he, card_bot] at hcA; omega
  exact (subspaceCommutator_eq_bot_iff ρ (fixedSpace ρ P) A).mpr
    (fixed_complement_centralized ρ hf P A Q (IsElementaryAbelian.isPGroup 3 P)
      ⟨hAn,hA⟩ hcA hfaith hPA hQ hQA hm hd)
end CFSG.Quasithin.ChapterD.OddComplement

namespace CFSG.Quasithin.ChapterD
open Representation.BinaryOffender Subgroup
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- Application to the original starred offender and the actual three-core.
The QhatStar ratio inequality and |A|=4 supply the budget four. The earlier
D.2.13 support argument and elementary-core reductions still supply the
explicit Q, its centralization, product movement, and the core hypotheses;
this is not an unconditional assertion of all of D.2.14. -/
theorem source_lemma_D_2_14_fixed_complement_of_odd_complement
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hcA : Nat.card A = 4) (Q : Subgroup G) [Q.Normal]
    (hP : IsElementaryAbelian 3 (pCore 3 G)) {s : ℕ}
    (hcP : Nat.card (pCore 3 G) = 3 ^ s) (hs : s = 2 ∨ s = 3)
    (hfaith : A ⊓ centralizer (pCore 3 G : Set G) = ⊥)
    (hcommon : pCore 3 G ⊓ centralizer (A : Set G) = ⊥)
    (hPA : ⁅pCore 3 G,A⁆ = pCore 3 G)
    (hQ : Nat.Coprime (Nat.card Q) 6) (hPQ : ⁅pCore 3 G,Q⁆ = ⊥)
    (hQA : ⁅Q,A⁆ = ⊥)
    (hm : subspaceCommutator ρ ⊤ (pCore 3 G ⊔ Q) = ⊤) :
    subspaceCommutator ρ (fixedSpace ρ (pCore 3 G)) A = ⊥ := by
  have hr : rank A = 2 := by simp only [rank, hcA]; decide
  have hd : fixedCodim ρ A ≤ 4 := by
    have hh := (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp
      (hA.1.2.2.2.trans_le hA.1.1)
    simpa only [hr] using hh
  exact OddComplement.fixed_complement_commutator_eq_bot ρ hf (pCore 3 G) A Q
    hP hcP hs hA.1.2.1.2 hcA le_normalizer_of_normal hfaith hcommon hPA hQ hPQ hQA hm hd
end CFSG.Quasithin.ChapterD
