module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFixedPlane
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSixteenActor
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceInterchange
/-!
# Excluding the original order-sixteen centralizer interval

Even kernel growth bounds every original point-core actor by order four.
Rank one makes each nontrivial actor either the critical involution or a
square root of it. Its action therefore gives [Q,C_U(Uα)] ≤ V. The actual
L-interchange of the two critical spans preserves Q and V, yielding the
reciprocal containment [Q,C_{Uα}(U)] ≤ V. This contradicts the order-sixteen
interval's previously proved movement obstruction.

The final application removes that interval from the original centralizer
series. It proves O₂(L₁) = O₂(K), retaining the central branch and the faithful
order-64 interval with exact kernel O₂(H) and both central flanks. It assumes
no later Data or recognition record. The remaining extraspecial exclusion,
residual classification and four-input assembly through 14.7.52 are still open.
Source: Aschbacher–Smith, 14.7.15(2), 14.7.16(3),(5) and 14.7.20(2),(3),
printed pp.1047–1049, refs/quasithin.pdf.
-/
public noncomputable section

open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual point-core image has exponent dividing four. -/
theorem extraspecial_core_fourth_power
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (b : F.H) (hb : (b : G) ∈ Q T L) : (starMap F b)^4=1 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨σ,hσ,hf,hd,_⟩ := extraspecial_section h hab structural previous hex hcard hexp s
  obtain ⟨z,hz,hgen,hfree⟩ := exists_fixedFree_cubic_of_point_normal h structural hn s σ hσ
  have hZ : IsPGroup 3 (zpowers z) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers,pow_one] using hz)
  have hfixed : invariants (σ.comp (zpowers z).subtype) = ⊥ := by
    apply bot_unique
    intro v hv
    exact hfree v (hv ⟨z,mem_zpowers z⟩)
  have hbR : starMap F b ∈ star F (F.Ri L 1) := by
    rw [←(core_product_of_point_normal h hab structural hn).2]
    exact mem_map_of_mem (starMap F) hb
  have hcomm : ∀ z' : zpowers z, Commute (σ z') (σ (starMap F b)) := by
    intro z'
    have hc := point_core_star_centralizes_of_normal h structural hn hbR
    exact (show Commute (z' : HStar F.H) (starMap F b) from
      hc z' (hgen ▸ z'.property)).map σ
  have hRS : star F (F.Ri L 1) ≤ star F (T : Subgroup G) := by
    rw [point_core_star_eq_centralizer_of_normal h structural hn]
    exact inf_le_left
  have hp : IsPGroup 2 (star F (F.Ri L 1)) :=
    (T.isPGroup'.comap_subtype.map (starMap F)).to_le hRS
  obtain ⟨n,hnpow⟩ := hp.exists_orderOf_eq_pow ⟨starMap F b,hbR⟩
  have hpow : (σ (starMap F b))^(2^n)=1 := by
    rw [←map_pow]
    have hh : (starMap F b)^(2^n)=1 := congrArg Subtype.val
      (hnpow ▸ pow_orderOf_eq_one (⟨starMap F b,hbR⟩ : star F (F.Ri L 1)))
    rw [hh,map_one]
  have hc := Representation.two_power_cube_zero_of_commuting_three_group
    σ (zpowers z) hZ hfixed hd _ hpow hcomm
  have h4 : (σ (starMap F b)-1)^4=0 := by rw [show 4=3+1 from rfl,pow_succ,hc,zero_mul]
  let : Nontrivial (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)) :=
    Module.nontrivial_of_finrank_pos (by omega : 0<Module.finrank (ZMod 2) (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)))
  let : CharP (Module.End (ZMod 2) (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U))) 2 :=
    charP_of_injective_algebraMap' (ZMod 2) 2
  apply hf
  rw [map_pow,map_one]
  have heq : (σ (starMap F b)-1)^4=(σ (starMap F b))^4-1 := by
    simpa only [show 2^2=4 from rfl,one_pow] using
      sub_pow_char_pow_of_commute 2 2 (Commute.one_right (σ (starMap F b)))
  exact sub_eq_zero.mp (heq.symm.trans h4)

/-- The core moves the critical centralizer only inside the original seed. -/
theorem extraspecial_core_critical_centralizer_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ⁅Q T L,F.U ⊓ centralizer (c.Uα : Set G)⁆ ≤ V := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨a,b,ha,hane,ha2,_,_,hb,hba,hbo⟩ :=
    exists_extraspecial_critical_actor_square_root h hab structural previous faithful he c hs
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨σ,hσ,_,hd,_⟩ := extraspecial_section h hab structural previous hex hcard hexp s
  let R := star F (F.Ri L 1)
  have hRS : R ≤ star F (T : Subgroup G) := by
    dsimp only [R]
    rw [point_core_star_eq_centralizer_of_normal h structural hn]
    exact inf_le_left
  have hp : IsPGroup 2 R := (T.isPGroup'.comap_subtype.map (starMap F)).to_le hRS
  let z : R := ⟨starMap F a,mem_map_of_mem (starMap F) (critical_le_Ri h structural c ha)⟩
  have hz : z ≠ 1 := fun hh => hane (congrArg Subtype.val hh)
  let : Nontrivial R := nontrivial_of_ne z 1 hz
  have hr := (primeRank_le_iff_elementary_card_le R).mp
    (point_core_rank_one_of_extraspecial_residual h structural hex hcard)
  obtain ⟨t,_,_,huniq⟩ := hp.exists_central_involution_of_no_elementary_four
    (fun E hE hEcard => by have hh := hr E hE; norm_num [hEcard] at hh)
  have hzt : z=t := (huniq z (Subtype.ext ha2)).resolve_left hz
  have hcases (q : F.H) (hq : (q : G) ∈ Q T L) :
      starMap F q=1 ∨ starMap F q=starMap F a ∨ (starMap F q)^2=starMap F a := by
    have hqR : starMap F q ∈ R := by
      dsimp only [R]
      rw [←(core_product_of_point_normal h hab structural hn).2]
      exact mem_map_of_mem (starMap F) hq
    let x : R := ⟨starMap F q,hqR⟩
    have hx4 : x^4=1 := Subtype.ext (extraspecial_core_fourth_power h hab structural previous ⟨e⟩ q hq)
    rcases huniq (x^2) (by simpa only [←pow_mul] using hx4) with hx|hx
    · rcases huniq x hx with hx|hx
      · exact Or.inl (congrArg Subtype.val hx)
      · exact Or.inr (Or.inl (congrArg Subtype.val (hx.trans hzt.symm)))
    · exact Or.inr (Or.inr (congrArg Subtype.val (hx.trans hzt.symm)))
  have hmove (q : F.H) (hq : (q : G) ∈ Q T L)
      (v : Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)) (hv : ρ a v=v) :
      ρ q v-v ∈ s.imageSpace V := by
    rcases hcases q hq with hq1|hqa|hqa
    · have hq' : ρ q=1 := by
        rw [←hσ]
        change σ (starMap F q)=1
        rw [hq1,map_one]
      simp only [hq',Module.End.one_apply,sub_self,Submodule.zero_mem]
    · have hq' : ρ q=ρ a := by
        rw [←hσ]
        change σ (starMap F q)=σ (starMap F a)
        rw [hqa]
      simp only [hq',hv,sub_self,Submodule.zero_mem]
    · have hk := (extraspecial_critical_root_fixed_plane h hab structural previous ⟨e⟩ s c hs
        a q ha hane hq hqa (extraspecial_core_fourth_power h hab structural previous ⟨e⟩ q hq)).1
      have hsquare : (ρ q)^2=ρ a := by
        rw [←hσ]
        change (σ (starMap F q))^2=σ (starMap F a)
        rw [←map_pow,hqa]
      let : Nontrivial (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)) :=
        Module.nontrivial_of_finrank_pos (by omega : 0<Module.finrank (ZMod 2)
          (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)))
      let : CharP (Module.End (ZMod 2) (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U))) 2 :=
        charP_of_injective_algebraMap' (ZMod 2) 2
      have hsquare' : (ρ q-1)^2=ρ a-1 := by
        rw [sub_pow_char_of_commute 2 (Commute.one_right (ρ q)),hsquare,one_pow]
      rw [←hk]
      change (ρ q-1) ((ρ q-1) v)=0
      change ((ρ q-1)^2 : Module.End (ZMod 2) _) v=0
      rw [hsquare']
      exact sub_eq_zero.mpr hv
  apply commutator_le.mpr
  intro q hq v hv
  let qH : F.H := ⟨q,Q_le_H F hq⟩
  let vU : F.U := ⟨v,hv.1⟩
  have hfix : ρ a (s.coordinates vU).toAdd=(s.coordinates vU).toAdd := by
    have hc : ⁅c.Uα,F.U ⊓ centralizer (c.Uα : Set G)⁆ ≤ F.Vi 1 :=
      ((commutator_comm _ _).trans
        (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right)).le.trans bot_le
    exact s.fixed_on_imageSpace_of_commutator_le c.Uα
      (F.U ⊓ centralizer (c.Uα : Set G)) hc a ha _
      ((s.mem_imageSpace_iff _ _).mpr ⟨vU,hv,rfl⟩)
  have hcU : ⁅q,v⁆ ∈ F.U :=
    (le_normalizer_iff_commutator_le_right.mp ((Q_le_H F).trans s.normalized))
      (commutator_mem_commutator hq hv.1)
  apply (s.coordinates_mem_imageSpace_iff_of_kernel_le V (F.le_seed 1) ⟨⁅q,v⁆,hcU⟩).mp
  change (s.coordinates ((⟨q*v*q⁻¹,
    (mem_normalizer_iff.mp (s.normalized qH.property) v).mp vU.property⟩ : F.U)*vU⁻¹)).toAdd ∈ s.imageSpace V
  rw [map_mul,map_inv]
  change (s.coordinates ⟨q*v*q⁻¹,_⟩).toAdd + -(s.coordinates vU).toAdd ∈ s.imageSpace V
  rw [s.equivariant qH vU,←sub_eq_add_neg]
  exact hmove qH hq _ hfix

/-- The original critical point lies in the seed, and an element of L
interchanges the two spans without changing the core Q. -/
theorem extraspecial_critical_interchange
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    c.Zα ≤ V ∧ c.b=3 ∧
      ∃ g ∈ L, F.U.conjBy g=c.Uα ∧ c.Uα.conjBy g=F.U ∧
        (Q T L).conjBy g=Q T L ∧ V.conjBy g=V := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have htwo := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  have hZ : c.Zα ≤ V := by
    rw [←critical_intersection_commutator_of_normal_card_two h hab structural
      (h.flag_escape F previous) hn s c hs htwo]
    exact (commutator_mono inf_le_left le_rfl).trans_eq
      (extraspecial_critical_commutator_eq_seed h hab structural previous faithful ⟨e⟩ c hs)
  obtain ⟨g,hg,hfirst,hsecond,_⟩ := G2Source.critical_span_core_interchange h c hZ
  have hQN : L ≤ normalizer (Q T L : Set G) :=
    (le_sup_left : L ≤ L ⊔ (T : Subgroup G)).trans
      ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))))
  exact ⟨hZ,G2Source.critical_length_three h c hZ,g,hg,hfirst,hsecond,
    mem_normalizer_iff_map_conj_eq.mp (hQN hg),
    mem_normalizer_iff_map_conj_eq.mp (h.chosen.normalizes hg)⟩

/-- The literal reciprocal centralizer is moved by Q only inside V. -/
theorem extraspecial_core_reciprocal_centralizer_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ⁅Q T L,c.Uα ⊓ centralizer (F.U : Set G)⁆ ≤ V := by
  obtain ⟨_,_,g,_,hfirst,hsecond,hQ,hV⟩ :=
    extraspecial_critical_interchange h hab structural previous faithful he c hs
  have hh := map_mono (f := (MulAut.conj g).toMonoidHom)
    (extraspecial_core_critical_centralizer_commutator h hab structural previous faithful he c hs)
  have hcent : (centralizer (c.Uα : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer (c.Uα.conjBy g : Set G) := by
    apply le_antisymm
    · exact map_centralizer_le_centralizer_image _ _
    · intro x hx
      refine ⟨(MulAut.conj g).symm x,?_,(MulAut.conj g).apply_symm_apply x⟩
      intro y hy
      apply (MulAut.conj g).injective
      simpa only [map_mul,MulEquiv.apply_symm_apply] using
        hx ((MulAut.conj g) y) (mem_map_of_mem _ hy)
  rw [map_commutator,map_inf _ _ _ (MulAut.conj g).injective,hcent] at hh
  change ⁅(Q T L).conjBy g,F.U.conjBy g ⊓ centralizer (c.Uα.conjBy g : Set G)⁆ ≤ V.conjBy g at hh
  rwa [hQ,hfirst,hsecond,hV] at hh

open NoncentralChiefRefinement in
/-- Exclude the actual order-sixteen interval with its original quotient map. -/
theorem extraspecial_sixteen_interval_impossible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 16) : False := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  exact extraspecial_sixteen_interval_core_movement h hab structural previous faithful ⟨e⟩
    N B hNB hUN hBC hp hm hc c hs
    ((extraspecial_core_reciprocal_centralizer_commutator h hab structural previous faithful ⟨e⟩ c hs).trans
      ((le_conjugateSpanBy V F.H).trans hUN))

open NoncentralChiefRefinement in
/-- The original centralizer series is K-central or has one faithful six-space.
Both central flanks and the exact action kernel of the surviving interval
are retained; neither the central nor the faithful branch is discarded. -/
theorem extraspecial_centralizer_core_reduction_no_small_intervals
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ((F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2) ∧
      (⁅centralizer (F.U : Set G),K F⁆ ≤ F.U ∨
        ∃ N B : NormalNode F.H, N ⋖ B ∧
          F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
          ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype ∧
          Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U) := by
  rcases extraspecial_centralizer_core_reduction_no_four h hab structural previous faithful he
    with hh | ⟨hp,N,B,hNB,hUN,hBC,hm,hc,_⟩
  · exact hh
  · exact (extraspecial_sixteen_interval_impossible h hab structural previous faithful he
      N B hNB hUN hBC hp hm hc).elim

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
