module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource.ExceptionalOdd.JankoFour
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension
public import Theory.SpecificGroups.Janko4.Model.Center
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.Mathieu.QuinticSylowActors
public import Theory.SpecificGroups.SymmetricFive.NoForty

/-!
# Quintic actors and the native J₄ Sylow geometry

A subgroup of J₄ containing a full Sylow two-subgroup and having order
dividing 2^a times five has a nontrivial two-core. Its canonical elementary
closure reduces it to the literal Mathieu subgroup, first involution
centralizer, or symmetric-linear subgroup. The order-eight closure rows
are impossible by minimality and the absence of seven. The three remaining
quotient maps reduce to the native M₂₄, M₂₂ and S₅ Sylow bounds.

The first centralizer retains its normal series with binary kernel,
cubic scalar section and M₂₂ quotient; the scalar is removed only through
the actual coprime-kernel map. The J₄ outer-automorphism theorem then detects
a faithful quintic actor in an intrinsic Sylow overgroup. The source-pair
application is in `RankOneModuleGenericExceptionalCartanGlobalPrimeJankoFour`.

Source: Aschbacher–Smith A.3.15 and 5.1.13, printed pp.50–51,636–637,
applied in 5.2.2, pp.648–649 of refs/quasithin.pdf; GLS3 Table 5.3i.
The imported ATLAS matrix words and certificates retain their attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime.JankoFourActors
variable {G Y : Type*} [Group G] [Finite G] [Group Y] [Finite Y]

private theorem prime_divisor {m a r : ℕ} (hd : m ∣ 2^a * 5)
    (hr : r.Prime) (hm : r ∣ m) : r = 2 ∨ r = 5 := by
  rcases hr.dvd_mul.mp (hm.trans hd) with h | h
  · exact .inl ((Nat.dvd_prime Nat.prime_two).mp (hr.dvd_of_dvd_pow h) |>.resolve_left hr.ne_one)
  · exact .inr ((Nat.dvd_prime Nat.prime_five).mp h |>.resolve_left hr.ne_one)

private theorem prime_free {m a r : ℕ} (hd : m ∣ 2^a * 5)
    (hr : r.Prime) (h2 : r ≠ 2) (h5 : r ≠ 5) : ¬ r ∣ m := by
  intro hh
  exact (prime_divisor hd hr hh).elim h2 h5

omit [Finite G] [Finite Y] in
private theorem five_image (f : G →* Y)
    (hk : Nat.Coprime 5 (Nat.card f.ker)) (J : Subgroup G)
    (h5 : 5 ∣ Nat.card J) : 5 ∣ Nat.card (J.map f) := by
  let g := f.comp J.subtype
  have hkg : Nat.Coprime 5 (Nat.card g.ker) :=
    hk.of_dvd_right (card_dvd_of_injective
      (show g.ker →* f.ker from
        { toFun := fun x => ⟨x.val.val,x.property⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl })
      (fun x y he => Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => (z : G)) he))))
  have hc := g.ker.card_mul_index
  rw [index_ker] at hc
  rw [←hc] at h5
  have hi := hkg.dvd_of_dvd_mul_left h5
  simpa only [g,MonoidHom.range_comp,range_subtype] using hi

omit [Finite Y] in
private theorem lift_bound (f : G →* Y) (hf : Function.Surjective f)
    (hk : Nat.Coprime 5 (Nat.card f.ker)) {a : ℕ}
    (hY : ∀ (S : Sylow 2 Y) (J : Subgroup Y), (S : Subgroup Y) ≤ J →
      Nat.card J ∣ 2^a * 5 → ¬ 5 ∣ Nat.card J)
    (S : Sylow 2 G) (J : Subgroup G) (hSJ : (S : Subgroup G) ≤ J)
    (hd : Nat.card J ∣ 2^a * 5) : ¬ 5 ∣ Nat.card J := by
  intro h5
  exact hY (S.mapSurjective hf) (J.map f) (map_mono hSJ)
    ((J.card_map_dvd f).trans hd) (five_image f hk J h5)

omit [Finite Y] in
private theorem equiv_bound (e : G ≃* Y) {a : ℕ}
    (hY : ∀ (S : Sylow 2 Y) (J : Subgroup Y), (S : Subgroup Y) ≤ J →
      Nat.card J ∣ 2^a * 5 → ¬ 5 ∣ Nat.card J)
    (S : Sylow 2 G) (J : Subgroup G) (hSJ : (S : Subgroup G) ≤ J)
    (hd : Nat.card J ∣ 2^a * 5) : ¬ 5 ∣ Nat.card J := by
  have hh := hY (S.mapSurjective e.surjective) (J.map e.toMonoidHom)
    (map_mono hSJ) (by rwa [card_map_of_injective e.injective])
  rwa [card_map_of_injective e.injective] at hh

private theorem normal_bound (N : Subgroup G) [N.Normal]
    (hi : Nat.Coprime 5 N.index) {a : ℕ}
    (hN : ∀ (S : Sylow 2 N) (J : Subgroup N), (S : Subgroup N) ≤ J →
      Nat.card J ∣ 2^a * 5 → ¬ 5 ∣ Nat.card J)
    (S : Sylow 2 G) (J : Subgroup G) (hSJ : (S : Subgroup G) ≤ J)
    (hd : Nat.card J ∣ 2^a * 5) : ¬ 5 ∣ Nat.card J := by
  intro h5
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal N
  have hdJ : Nat.card (J.subgroupOf N) ∣ Nat.card J := by
    apply card_dvd_of_injective
      (show J.subgroupOf N →* J from
        { toFun := fun x => ⟨x.val.val,x.property⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl })
    exact fun x y he => Subtype.ext (Subtype.ext (congrArg (fun z : J => (z : G)) he))
  have hcard : Nat.card (J.subgroupOf N) = Nat.card (N.subgroupOf J) := by
    apply Nat.card_congr
    exact { toFun := fun x => ⟨⟨x.val.val,x.property⟩,x.val.property⟩
            invFun := fun x => ⟨⟨x.val.val,x.property⟩,x.val.property⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  apply hN P (J.subgroupOf N) (by rw [hP]; exact comap_mono hSJ) (hdJ.trans hd)
  rw [hcard]
  have hc := (N.subgroupOf J).card_mul_index
  have hic : Nat.Coprime 5 (N.subgroupOf J).index :=
    hi.of_dvd_right (N.relIndex_dvd_index_of_normal J)
  exact hic.dvd_of_dvd_mul_right (hc ▸ h5)

omit [Finite Y] in
private theorem two_kernel_coprime (f : G →* Y) (hk : IsPGroup 2 f.ker) :
    Nat.Coprime 5 (Nat.card f.ker) := by
  obtain ⟨b,hb⟩ := hk.exists_card_eq
  rw [hb]
  exact (by decide : Nat.Coprime 5 2).pow_right b

private theorem m24_bound {a : ℕ} (S : Sylow 2 Sporadic.Mathieu.M24)
    (J : Subgroup Sporadic.Mathieu.M24) (hSJ : (S : Subgroup _) ≤ J)
    (hd : Nat.card J ∣ 2^a * 5) : ¬ 5 ∣ Nat.card J := by
  rw [Sporadic.Mathieu.M24QuinticSylow.card_eq_1024 S J hSJ
    (prime_free hd Nat.prime_three (by decide) (by decide))]
  decide

private theorem m22_bound {a : ℕ} (S : Sylow 2 Sporadic.Mathieu.M22)
    (J : Subgroup Sporadic.Mathieu.M22) (hSJ : (S : Subgroup _) ≤ J)
    (hd : Nat.card J ∣ 2^a * 5) : ¬ 5 ∣ Nat.card J := by
  rw [Sporadic.Mathieu.M22QuinticSylow.card_eq_128 S J hSJ
    (prime_free hd Nat.prime_three (by decide) (by decide))
    (prime_free hd (by decide : Nat.Prime 11) (by decide) (by decide))]
  decide

private theorem symmetric_bound {a : ℕ} (S : Sylow 2 (Equiv.Perm (Fin 5)))
    (J : Subgroup (Equiv.Perm (Fin 5))) (hSJ : (S : Subgroup _) ≤ J)
    (hd : Nat.card J ∣ 2^a * 5) : ¬ 5 ∣ Nat.card J := by
  intro h5
  have h8 : 8 ∣ Nat.card J := by
    have hs : Nat.card S = 8 := by
      rw [S.card_eq_multiplicity,Nat.card_eq_fintype_card,Fintype.card_perm]
      decide +kernel
    exact hs ▸ card_dvd_of_le hSJ
  have hc : Nat.card J ∣ 120 := by
    simpa [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] using J.card_subgroup_dvd_card
  have h3 := prime_free hd Nat.prime_three (by decide) (by decide)
  have hn : ∀ m ∈ (120 : ℕ).divisors, 8 ∣ m → ¬ 3 ∣ m → 5 ∣ m → m = 40 := by decide +kernel
  exact _root_.SymmetricFive.subgroup_card_ne_forty J
    (hn _ (Nat.mem_divisors.mpr ⟨hc,by decide⟩) h8 h3 h5)

open Janko4 Janko4.LocalStructure
open Janko4.OuterReduction.OddIndex
open Janko4.LocalStructure.SymmetricLinear
attribute [local irreducible] modelGroup matrixA matrixB

private theorem max1_bound {a : ℕ}
    (S : Sylow 2 (Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four))
    (J : Subgroup (Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four))
    (hSJ : (S : Subgroup _) ≤ J) (hd : Nat.card J ∣ 2^a * 5) :
    ¬ 5 ∣ Nat.card J := by
  let e := localQuotientEquivM24 matrixA_mul_self matrixB_pow_four
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (Cardinality.localKernel matrixA_mul_self matrixB_pow_four))
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk',
      localKernel_eq_twoCore]
    exact pCore_isPGroup
  exact lift_bound f (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (two_kernel_coprime f hk) m24_bound S J hSJ hd

private theorem max2_bound {a : ℕ}
    (S : Sylow 2 InvolutionCentralizers.First.centralizer)
    (J : Subgroup InvolutionCentralizers.First.centralizer)
    (hSJ : (S : Subgroup _) ≤ J) (hd : Nat.card J ∣ 2^a * 5) :
    ¬ 5 ∣ Nat.card J := by
  let N := InvolutionCentralizers.First.QuotientExtension.H
  have hi : N.index = 2 := by
    change Nat.card (InvolutionCentralizers.First.centralizer ⧸ N) = 2
    rw [Nat.card_congr InvolutionCentralizers.First.QuotientExtension.centralizerQuotientEquivC2.toEquiv]
    exact Nat.card_zmod 2
  apply normal_bound N (by rw [hi]; decide) _ S J hSJ hd
  let f := InvolutionCentralizers.First.QuotientExtension.mathieuProjection
  have hk : Nat.card f.ker = 2^13 * 3 := by
    rw [InvolutionCentralizers.First.QuotientExtension.mathieuProjection_ker,
      Nat.card_congr (subgroupOfEquivOfLe InvolutionCentralizers.First.QuotientExtension.R_le_H).toEquiv,
      card_eq_card_quotient_mul_card_subgroup
        (InvolutionCentralizers.First.QuotientExtension.Q.subgroupOf
          InvolutionCentralizers.First.QuotientExtension.R),
      Nat.card_congr InvolutionCentralizers.First.QuotientExtension.RQuotientEquivC3.toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe InvolutionCentralizers.First.QuotientExtension.Q_le_R).toEquiv,
      InvolutionCentralizers.First.centralizer_twoCore_card]
    norm_num [Nat.card_zmod]
  exact lift_bound f InvolutionCentralizers.First.QuotientExtension.mathieuProjection_surjective
    (by rw [hk]; decide) m22_bound

private theorem max4_bound {a : ℕ} (S : Sylow 2 max4Subgroup)
    (J : Subgroup max4Subgroup) (hSJ : (S : Subgroup _) ≤ J)
    (hd : Nat.card J ∣ 2^a * 5) : ¬ 5 ∣ Nat.card J := by
  apply lift_bound max4Projection max4Projection_surjective
    (two_kernel_coprime _ max4Projection_kernel_isTwoGroup) _ S J hSJ hd
  let f : QuotientModel →* Equiv.Perm (Fin 5) := MonoidHom.fst _ _
  have hf : Function.Surjective f := fun x => ⟨(x,1),rfl⟩
  have hk : Nat.card f.ker = 168 := by
    have hc := f.ker.card_mul_index
    rw [index_ker,f.range_eq_top_of_surjective hf,card_top,quotientModel_card] at hc
    have ht : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    rw [ht] at hc
    omega
  exact lift_bound f hf (by rw [hk]; decide) symmetric_bound

omit [Finite G] in
private theorem subgroup_bound (M : Subgroup G) {a : ℕ}
    (hM : ∀ (S : Sylow 2 M) (J : Subgroup M), (S : Subgroup M) ≤ J →
      Nat.card J ∣ 2^a * 5 → ¬ 5 ∣ Nat.card J)
    (S : Sylow 2 G) (J : Subgroup G) (hSJ : (S : Subgroup G) ≤ J)
    (hJM : J ≤ M) (hd : Nat.card J ∣ 2^a * 5) : ¬ 5 ∣ Nat.card J := by
  have hh := hM (S.subtype (hSJ.trans hJM)) (J.subgroupOf M) (comap_mono hSJ)
    (by rwa [Nat.card_congr (subgroupOfEquivOfLe hJM).toEquiv])
  rwa [Nat.card_congr (subgroupOfEquivOfLe hJM).toEquiv] at hh

private theorem twoCore_ne_bot {a : ℕ} (S : Sylow 2 Model) (J : Subgroup Model)
    (hSJ : (S : Subgroup Model) ≤ J) (hd : Nat.card J ∣ 2^a * 5) : pCore 2 J ≠ ⊥ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply twoCore_ne_bot_of_solvable_small_odd_core (p := 5) (d := 1) (t := 21) (by decide)
    (isSolvable_of_prime_dvd_card_eq_two_or_prime J Nat.prime_five (fun r hr h => prime_divisor hd hr h))
    (fun r hr h => prime_divisor hd hr h)
  · have hc : Nat.Coprime (Nat.card (pCore 5 J)) (2^a) := by
      obtain ⟨b,hb⟩ := (pCore_isPGroup (p := 5) (G := J)).exists_card_eq
      rw [hb]
      exact (by decide : Nat.Coprime 5 2).pow b a
    exact Nat.le_of_dvd (by decide) (hc.dvd_of_dvd_mul_left
      ((pCore 5 J).card_subgroup_dvd_card.trans hd))
  · exact (ambient_sylow_card S) ▸ card_dvd_of_le hSJ
  · intro n hn
    interval_cases n <;> norm_num [Fin.prod_univ_succ]

open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Source
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

private theorem closure_not_eight {a : ℕ} (S : Sylow 2 Model) (J : Subgroup Model)
    (hSJ : (S : Subgroup Model) ≤ J) (hd : Nat.card J ∣ 2^a * 5) :
    Nat.card (elementaryClosure S J hSJ) ≠ 8 := by
  intro he
  let E := centralClosure S J hSJ
  let := centralClosure_elementary_of_twoCore_ne_bot S J hSJ (twoCore_ne_bot S J hSJ hd)
  have hc : Nat.card E = 8 := (card_map_of_injective J.subtype_injective).symm.trans he
  exact not_minimal_normal_elementary_eight_of_solvable_seven_free E hc
    (isSolvable_of_prime_dvd_card_eq_two_or_prime J Nat.prime_five (fun r hr h => prime_divisor hd hr h))
    (prime_free hd (by decide : Nat.Prime 7) (by decide) (by decide))
    (by intro C hCE hCn; let := hCn; exact centralClosure_minimal S J hSJ C hCE)

private theorem fixed_sylow_bound {a : ℕ} (S : Sylow 2 Model) (J : Subgroup Model)
    (hS : (S : Subgroup Model) = twoSubgroup)
    (hSJ : (S : Subgroup Model) ≤ J) (hd : Nat.card J ∣ 2^a * 5) : ¬ 5 ∣ Nat.card J := by
  have hJN := overgroup_le_elementaryClosure_normalizer S J hSJ
  have hnot8 := closure_not_eight S J hSJ hd
  rcases elementaryClosure_catalogue S J hSJ hS (twoCore_ne_bot S J hSJ hd)
    with hm | h1 | h2 | h3 | h4
  · exact subgroup_bound _ max1_bound S J hSJ hm hd
  · have hc : Nat.card (elementaryClosure S J hSJ) = 2 := by
      rw [h1,KernelOrders.pureKernelCatalogue.2 1]
      rfl
    obtain ⟨e⟩ := normalizer_equiv_max2_of_closure_card_two S J hSJ hc
    exact subgroup_bound _ (equiv_bound (e.trans (sourceSubgroupEquivLocal.trans
      ((MulEquiv.subgroupCongr localSubgroup_eq_top).trans
        (Subgroup.topEquiv.trans InvolutionCentralizers.First.centralizerEquiv.symm)))) max2_bound)
      S J hSJ hJN hd
  · rw [h2] at hJN
    let g := MatrixNormalizerBounds.ThirdConjugacy.conjugator
    exact subgroup_bound _ (equiv_bound ((MulAut.conj g).subgroupMap max4Subgroup).symm max4_bound)
      S J hSJ (hJN.trans candidate_two_normalizer_le_max4_conjugate) hd
  · exact (hnot8 (by rw [h3,KernelOrders.pureKernelCatalogue.2 3]; rfl)).elim
  · exact (hnot8 (by rw [h4,KernelOrders.pureKernelCatalogue.2 4]; rfl)).elim

/-- The native J₄ Sylow geometry has no overgroup of order dividing 2^a·5
whose order is divisible by five. The literal local quotient kernels are retained. -/
theorem no_five_sylow_overgroup {a : ℕ} (S : Sylow 2 Model) (J : Subgroup Model)
    (hSJ : (S : Subgroup Model) ≤ J) (hd : Nat.card J ∣ 2^a * 5) : ¬ 5 ∣ Nat.card J := by
  obtain ⟨T,hT⟩ := (IsPGroup.of_card twoSubgroup_card).exists_le_sylow
  have hTf : (T : Subgroup Model) = twoSubgroup := by
    symm
    apply eq_of_le_of_card_ge hT
    rw [ambient_sylow_card T,twoSubgroup_card]
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model S T
  let e := MulAut.conj g
  have he : (S : Subgroup Model).map e.toMonoidHom = T := congrArg Sylow.toSubgroup hg
  have hh := fixed_sylow_bound T (J.map e.toMonoidHom) hTf
    (by rw [←he]; exact map_mono hSJ)
    (by rwa [card_map_of_injective e.injective])
  rwa [card_map_of_injective e.injective] at hh

/-- A faithful quintic actor on a normal J₄ factor is detected in its
inner automorphism group and excluded by the actual Sylow-overgroup bound. -/
theorem no_five_actor (K E : Subgroup G) [K.Normal] (S : Sylow 2 G) {a : ℕ}
    (e : K ≃* Model) (hE : Nat.card E = 5)
    (hd : Disjoint E (centralizer (K : Set G)))
    (hc : Nat.card (E ⊔ (S : Subgroup G) : Subgroup G) ∣ 2^a * 5) : False := by
  have hz : center K = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center Model at hh
    rw [Janko4.model_center_eq_bot,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  apply no_odd_actor_of_sylow_order_bound K E S (by decide : Odd 5) hz
    (Janko4.AdequateLocal.outer_isPGroup_two.of_equiv (MulAut.outerCongr e).symm) _ hE hd hc
  intro P J hJ hPJ
  exact equiv_bound e no_five_sylow_overgroup P J hPJ hJ

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime.JankoFourActors
