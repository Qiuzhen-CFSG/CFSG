module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.RankOne
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Hall.Source
public import Theory.GroupTheory.ConjugatePairKernelGeneration
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# The literal pair projection and its kernel

The original starred Sylow subgroup makes the image of I = ⟨V,Vʰ⟩ equal
K*. Restriction of the starred map, followed by the earlier natural marking,
gives a surjection to SL₂(q) compatible with the original map on K.
Its initial kernel is I ∩ O₂(H).

To identify that kernel with P = BBʰ, use the actual odd Hall subgroup's
D₀ ≤ L. This subgroup normalizes V; a nonidentity split diagonal in its
image fixes no involution. Coprime decomposition therefore generates V
modulo B by commutators with D₀. Consequently I/P is two-perfect. The
conjugate-pair transfer theorem removes its central two-kernel, giving
P = O₂(I). This includes q = 4 without a Schur-cover exception. The
complementary Sylow fixed spaces then construct the literal natural
marking of P, without identifying its coordinates with those of V.

The earlier natural marking, starred Sylow image, fixed-space conclusion
and D₀ ≤ L are the preceding 11.3.7 inputs owned by
qt-d-1222-shadow-common-action. The source counterexample application is
in Identification.lean; qt-d-1222-shadow-common-core retains their discharge.
No pair projection, core equality or natural-pair marking is assumed.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, printed p.774,
first two paragraphs. The Hall action supplies the chapter-specific step
beyond the splitting alternatives of E.2.10(7), printed pp.222--223.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore

private theorem kernel_le_of_pair_odd_action
    {E A : Type*} [Group E] [Finite E] [Group A]
    (q : E →* A) (hk : IsPGroup 2 q.ker)
    (U : Subgroup E) (hU : IsPGroup 2 U) (g : E)
    (hgen : U ⊔ U.map (MulAut.conj g).toMonoidHom = ⊤)
    (hn : q.ker ≤ normalizer (U : Set E))
    (R : Sylow 2 A) (hR : U.map q = R)
    (N : Subgroup E) [N.Normal] (hN : N ≤ q.ker)
    (hUN : U ⊓ q.ker ≤ N)
    (C : Subgroup E) (ho : Odd (Nat.card C))
    (hCU : C ≤ normalizer (U : Set E))
    (hfix : U ⊓ centralizer (C : Set E) ≤ q.ker) : q.ker ≤ N := by
  have hC : C ≤ pResidual 2 E :=
    OddHall.odd_subgroup_le _ _ (isPGroup_quotient_pResidual 2) ho
  have hcomm : ⁅U,C⁆ ≤ pResidual 2 E :=
    (commutator_mono le_rfl hC).trans (commutator_le_right _ _)
  have hdec : U ≤ pResidual 2 E ⊔ N := by
    have hcop : (Nat.card C).Coprime (Nat.card U) := by
      obtain ⟨n,hn⟩ := hU.exists_card_eq
      rw [hn]
      exact (Nat.coprime_two_right.mpr ho).pow_right n
    conv_lhs => rw [eq_commutator_sup_centralizer_of_solvable_coprime U C hCU
      (@IsNilpotent.to_isSolvable U _ hU.isNilpotent) hcop]
    exact sup_le (hcomm.trans le_sup_left)
      ((le_inf inf_le_left hfix).trans hUN |>.trans le_sup_right)
  have htop : pResidual 2 E ⊔ N = ⊤ := by
    apply top_unique
    rw [←hgen]
    apply sup_le hdec
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hdec
    have he : (pResidual 2 E ⊔ N).map (MulAut.conj g).toMonoidHom = pResidual 2 E ⊔ N :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
    exact hh.trans he.le
  let π := QuotientGroup.mk' N
  let f := QuotientGroup.lift N q hN
  have hcomp : f.comp π = q := by ext; rfl
  have hp : IsPPerfect 2 (E ⧸ N) := by
    apply (pResidual_eq_top_iff 2 _).mp
    rw [←map_pResidual_of_surjective 2 π (QuotientGroup.mk'_surjective N)]
    have he := congrArg (Subgroup.map π) htop
    simpa only [Subgroup.map_sup,show N.map π = ⊥ from QuotientGroup.map_mk'_self N,sup_bot_eq,
      map_top_of_surjective π (QuotientGroup.mk'_surjective N)] using he
  have hker : f.ker = q.ker.map π := QuotientGroup.ker_lift N q hN
  have hn' : f.ker ≤ normalizer (U.map π : Set (E ⧸ N)) := by
    rw [hker]
    exact (map_mono hn).trans (U.le_normalizer_map π)
  have hconj : (U.map (MulAut.conj g).toMonoidHom).map π =
      (U.map π).map (MulAut.conj (π g)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
  have hgen' : U.map π ⊔ (U.map π).map (MulAut.conj (π g)).toMonoidHom = ⊤ := by
    rw [←hconj,←Subgroup.map_sup,hgen,map_top_of_surjective π (QuotientGroup.mk'_surjective N)]
  have hR' : (U.map π).map f = R := by rw [map_map,hcomp]; exact hR
  have hi : U.map π ⊓ f.ker = ⊥ := by
    apply bot_unique
    rintro x ⟨⟨u,hu,rfl⟩,hk⟩
    exact (QuotientGroup.eq_one_iff u).mpr (hUN ⟨hu,hk⟩)
  have he := kernel_eq_intersection_pair_of_twoPerfect hp f (hker.symm ▸ hk.map π)
    (U.map π) (hU.map π) (π g) hgen' hn' R hR'
  rw [hi,Subgroup.map_bot,bot_sup_eq] at he
  intro x hx
  exact (QuotientGroup.eq_one_iff x).mp (he.le (hker.symm ▸ mem_map_of_mem π hx))

private theorem involution_eq_one_of_conjugate_diagonal
    {F : Type*} [Field F] [CharP F 2]
    (x d b : Matrix.SpecialLinearGroup (Fin 2) F) (a : F) (ha : a ≠ 1)
    (hd : (b*d*b⁻¹).val = !![a,0;0,a⁻¹])
    (hx : x^2 = 1) (hc : x*d = d*x) : x = 1 := by
  let y := b*x*b⁻¹
  have hy : y^2 = 1 := by
    change (MulAut.conj b x)^2 = 1
    rw [←map_pow,hx,map_one]
  have hc' : y * (b*d*b⁻¹) = (b*d*b⁻¹) * y := by
    change MulAut.conj b x * MulAut.conj b d = MulAut.conj b d * MulAut.conj b x
    rw [←map_mul,←map_mul,hc]
  have ha0 : a ≠ 0 := by
    have he := (b*d*b⁻¹).property
    rw [hd,Matrix.det_fin_two] at he
    change a*a⁻¹-0*0=1 at he
    simp only [mul_zero,sub_zero] at he
    exact left_ne_zero_of_mul_eq_one he
  have hdiff : a - a⁻¹ ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    have hs : a^2 = 1 := by
      calc
        _ = a*a⁻¹ := by rw [sq,←he]
        _ = 1 := mul_inv_cancel₀ ha0
    exact ha ((frobenius_inj F 2) (by simpa only [frobenius_def,one_pow] using hs))
  have h01 : y.val 0 1 = 0 := by
    have he := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F => z.val 0 1) hc'
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,hd] at he
    change y.val 0 0*0+y.val 0 1*a⁻¹=a*y.val 0 1+0*y.val 1 1 at he
    simp only [mul_zero,zero_mul,zero_add,add_zero] at he
    exact (mul_eq_zero.mp (show (a-a⁻¹)*y.val 0 1=0 by linear_combination -he)).resolve_left hdiff
  have h10 : y.val 1 0 = 0 := by
    have he := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F => z.val 1 0) hc'
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,hd] at he
    change y.val 1 0*a+y.val 1 1*0=0*y.val 0 0+a⁻¹*y.val 1 0 at he
    simp only [mul_zero,zero_mul,zero_add,add_zero] at he
    exact (mul_eq_zero.mp (show (a-a⁻¹)*y.val 1 0=0 by linear_combination he)).resolve_left hdiff
  have hdiag (i : Fin 2) : y.val i i = 1 := by
    have he := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F => z.val i i) hy
    have hs : (y.val i i)^2 = 1 := by
      fin_cases i <;> simpa [sq,Matrix.mul_apply,Fin.sum_univ_two,h01,h10] using he
    exact (frobenius_inj F 2) (by simpa only [frobenius_def,one_pow] using hs)
  have hy1 : y = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01,h10,hdiag]
  exact (MulAut.conj b).map_eq_one_iff.mp hy1

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {h : G}

private theorem source_pair_projection
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hk : outsideResidual H ≤ pairGroup V h)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (c : NaturalQuotientMarking T H S.field)
    (Rstar : Sylow 2 (residualStar T H))
    (hRstar : (Rstar : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (V.subgroupOf H).map (starProjection T H)) :
    ∃ (q : pairGroup V h →* Matrix.SpecialLinearGroup (Fin 2) S.field.Carrier),
      Function.Surjective q ∧
      q.ker = (H.pCoreIn 2).subgroupOf (pairGroup V h) ∧
      (∀ k : outsideResidual H, q (inclusion hk k) = Hall.quotientMap c k) ∧
      ∃ R : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) S.field.Carrier),
        (V.subgroupOf (pairGroup V h)).map q = R := by
  let := source_residualQuotient_simple hmodel
  let I := pairGroup V h
  have hIH : I ≤ H := pairGroup_le s hh
  let t : I →* Star T H := (starProjection T H).comp (inclusion hIH)
  have hv : (V.subgroupOf H).map (starProjection T H) ≤ residualStar T H := by
    rw [←hRstar]
    exact map_subtype_le _
  have him : (I.subgroupOf H).map (starProjection T H) = residualStar T H := by
    change ((pairGroup V h).subgroupOf H).map (starProjection T H) = _
    rw [pairGroup_eq_residual_join_seed s hh hk,
      subgroupOf_sup (outsideResidual_le H) (D.le_sylow.trans s.outside.1.1.2),Subgroup.map_sup]
    exact sup_eq_left.mpr hv
  have hrange : t.range = residualStar T H := by
    rw [MonoidHom.range_comp,inclusion_range]
    exact him
  let t' : I →* residualStar T H := t.codRestrict _ (fun x => hrange ▸ ⟨x,rfl⟩)
  have ht' : Function.Surjective t' := by
    intro x
    have hx : (x : Star T H) ∈ t.range := hrange.symm ▸ x.property
    obtain ⟨y,hy⟩ := hx
    exact ⟨y,Subtype.ext hy⟩
  let e := (residualStarEquiv T H s.outside.1.1.2 s.moves_omega_center).symm.trans c.quotientEquiv
  let q := e.toMonoidHom.comp t'
  have hker : q.ker = (H.pCoreIn 2).subgroupOf I := by
    ext x
    change e (t' x) = 1 ↔ (x : G) ∈ H.pCoreIn 2
    rw [e.map_eq_one_iff]
    have he : t' x = 1 ↔ t x = 1 := Subtype.ext_iff
    rw [he]
    change QuotientGroup.mk' _ (inclusion hIH x) = 1 ↔ _
    change inclusion hIH x ∈ (QuotientGroup.mk'
      ((centralizer (omegaClosure T H : Set G)).subgroupOf H)).ker ↔ _
    rw [QuotientGroup.ker_mk',source_star_denominator_eq_core s hmodel]
    exact (mem_map_iff_mem (f := H.subtype) H.subtype_injective).symm
  have hcompat (k : outsideResidual H) : q (inclusion hk k) = Hall.quotientMap c k := by
    change c.quotientEquiv
      ((residualStarEquiv T H s.outside.1.1.2 s.moves_omega_center).symm
        (t' (inclusion hk k))) = c.quotientEquiv (QuotientGroup.mk' _ k)
    congr 1
    apply (residualStarEquiv T H s.outside.1.1.2 s.moves_omega_center).symm_apply_eq.mpr
    apply Subtype.ext
    exact (residualStarEquiv_apply T H s.outside.1.1.2 s.moves_omega_center k).symm
  let R := Rstar.mapSurjective (f := e.toMonoidHom) e.surjective
  have hR : (V.subgroupOf I).map q = R := by
    change (V.subgroupOf I).map (e.toMonoidHom.comp t') = (Rstar : Subgroup _).map e.toMonoidHom
    rw [←map_map]
    congr 1
    apply map_injective (residualStar T H).subtype_injective
    rw [map_map,hRstar]
    change (V.subgroupOf I).map ((starProjection T H).comp (inclusion hIH)) = _
    rw [←map_map]
    congr 1
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x,show (x:G) ∈ I from mem_sup_left hx⟩,hx,Subtype.ext rfl⟩
  exact ⟨q,e.surjective.comp ht',hker,hcompat,R,hR⟩

/-- The projection on the original pair, its full kernel, both literal Sylow
images, and compatibility with the previously marked residual quotient. -/
theorem source_pair_projection_kernel
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hm : h ∉ normalizer (L : Set G)) (hnot : ¬ V ≤ H.pCoreIn 2)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (c : NaturalQuotientMarking T H S.field)
    (Rstar : Sylow 2 (residualStar T H))
    (hRstar : (Rstar : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (V.subgroupOf H).map (starProjection T H))
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hAL : oddCartanPart A ≤ L) :
    ∃ (q : pairGroup V h →* Matrix.SpecialLinearGroup (Fin 2) S.field.Carrier),
      Function.Surjective q ∧
      q.ker = (pairCore V H h).subgroupOf (pairGroup V h) ∧
      (∀ k : outsideResidual H, q (inclusion
        (source_residual_le_pairGroup s hh hm hnot hmodel Rstar hRstar) k) =
          Hall.quotientMap c k) ∧
      ∃ R Q : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) S.field.Carrier),
        (V.subgroupOf (pairGroup V h)).map q = R ∧
        ((V.map (MulAut.conj h).toMonoidHom).subgroupOf (pairGroup V h)).map q = Q := by
  have hk := source_residual_le_pairGroup s hh hm hnot hmodel Rstar hRstar
  obtain ⟨q,hq,hker,hcompat,R,hR⟩ := source_pair_projection s hh hk hmodel c Rstar hRstar
  obtain ⟨k,hkK,hkI,hkM,hkV,hkB⟩ := exists_internal_pair_conjugator s hh hm hk
  let I := pairGroup V h
  let U := V.subgroupOf I
  let N := (pairCore V H h).subgroupOf I
  let C := (oddCartanPart A).subgroupOf I
  let kI : I := ⟨k,hkI⟩
  have hKI : oddCartanPart A ≤ I := (oddCartanPart_le_residual_of_hall _ A hA hHall).trans hk
  have hconj : U.map (MulAut.conj kI).toMonoidHom =
      (V.map (MulAut.conj h).toMonoidHom).subgroupOf I := by
    rw [←hkV]
    exact (conj_smul_subgroupOf (show V ≤ I from le_sup_left) kI)
  have hgen : U ⊔ U.map (MulAut.conj kI).toMonoidHom = ⊤ := by
    rw [hconj,←subgroupOf_sup (show V ≤ I from le_sup_left)
      (show V.map (MulAut.conj h).toMonoidHom ≤ I from le_sup_right)]
    exact subgroupOf_self I
  have hU : IsPGroup 2 U := by let := D.elementary; exact (IsElementaryAbelian.isPGroup 2 V).comap_subtype
  have hqker : IsPGroup 2 q.ker := by rw [hker]; exact (isPGroup_pCoreIn 2 H).comap_subtype
  have hn : q.ker ≤ normalizer (U : Set I) := by
    rw [hker]
    intro x hx
    rw [mem_normalizer_iff]
    intro y
    exact mem_normalizer_iff.mp (core_normalizes_seed s hx) y
  let : N.Normal := pairCore_normal s hh
  have hN : N ≤ q.ker := by rw [hker]; exact comap_mono (pairCore_le_core hh)
  have hUN : U ⊓ q.ker ≤ N := by
    rintro x ⟨hx,hxk⟩
    rw [hker] at hxk
    exact mem_sup_left (show (x:G) ∈ axis V H from ⟨hx,hxk⟩)
  have ho : Odd (Nat.card C) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hKI).toEquiv]
    have hoA : Odd (Nat.card A) := by
      rw [←Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv]
      exact OddHall.odd_hall_odd hHall
    exact hoA.of_dvd_nat (card_dvd_of_le (oddCartanPart_le A))
  have hCU : C ≤ normalizer (U : Set I) := by
    intro d hd
    rw [mem_normalizer_iff]
    intro v
    exact mem_normalizer_iff.mp (D.normalizes (hAL hd)) v
  obtain ⟨d,hd,b,a,ha,hdiag⟩ := Hall.source_conjugate_diagonal s c A hA hHall
  have hfix : U ⊓ centralizer (C : Set I) ≤ q.ker := by
    rintro x ⟨hx,hxc⟩
    have hpow : (q x)^2 = 1 := by
      rw [←map_pow]
      have hxp : x^2 = 1 := by
        apply Subtype.ext
        let := D.elementary
        exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (x:G) hx
      rw [hxp,map_one]
    have hc : q x * Hall.quotientMap c d = Hall.quotientMap c d * q x := by
      rw [←hcompat d,←map_mul,←map_mul]
      exact congrArg q (mem_centralizer_iff.mp hxc (inclusion hk d) hd).symm
    exact involution_eq_one_of_conjugate_diagonal (q x) (Hall.quotientMap c d) b a ha hdiag hpow hc
  have hNker : q.ker = N := le_antisymm
    (kernel_le_of_pair_odd_action q hqker U hU kI hgen hn R hR N hN hUN C ho hCU hfix) hN
  let Q := R.mapSurjective (f := (MulAut.conj (q kI)).toMonoidHom) (MulAut.conj (q kI)).surjective
  have hQ : ((V.map (MulAut.conj h).toMonoidHom).subgroupOf I).map q = Q := by
    rw [←hconj]
    change (U.map (MulAut.conj kI).toMonoidHom).map q =
      (R : Subgroup _).map (MulAut.conj (q kI)).toMonoidHom
    rw [←hR,map_map,map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]
  exact ⟨q,hq,hNker,hcompat,R,Q,hR,hQ⟩

/-- Rank-one recognition of the literal pair from the preceding source inputs.
The original field is retained, with no extra kernel or splitting premise. -/
theorem source_pair_recognition
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hm : h ∉ normalizer (L : Set G))
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hnot : ¬ V ≤ H.pCoreIn 2)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (c : NaturalQuotientMarking T H S.field)
    (Rstar : Sylow 2 (residualStar T H))
    (hRstar : (Rstar : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (V.subgroupOf H).map (starProjection T H))
    (A : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hAL : oddCartanPart A ≤ L) :
    pairCore V H h = (pairGroup V h).pCoreIn 2 ∧
      Nonempty (PairNaturalMarking V H h S.field) := by
  obtain ⟨q,hq,hker,_,R,Q,hR,hQ⟩ :=
    source_pair_projection_kernel s hh hm hnot hmodel c Rstar hRstar A hA hHall hAL
  exact ⟨pairCore_eq_twoCore_of_projection hh q hq hker,
    natural_pair_of_projection s hh hf
      (source_residual_le_pairGroup s hh hm hnot hmodel Rstar hRstar)
      q hq hker R Q hR hQ⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
