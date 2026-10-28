module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.M10CoreSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.PGLNineCoreSource
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NormalAtT
public import Theory.GroupTheory.CrossingPairCentralizer
public import Theory.GroupAction.ModelConjugation
public import ABG.ChapterII.Section1.MaximalModels
public import Theory.SpecificGroups.AlternatingSix.NonabelianInvolutionGeneration
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6Source
/-!
# The complete A₆ quotient branch of source 2.5.21

In either nonfull quotient, the proved source core is nonabelian dihedral or
semidihedral. Every core involution centralizer has the original A₆ component.
Quasithinness makes that component normal. The crossing core acts faithfully
on A₆ by the proved core-disjointness identity, and its noncommuting involutions
have fixed subgroups generating A₆. Thus the crossing components normalize
each other and commute. Two commuting A₆ components violate quasithinness.

This eliminates M₁₀ and PGL₂(9), leaving the literal quotient H/O₂(H) ≃ Aut(A₆).
Source: Aschbacher--Smith, 2.5.21, printed pp.565--566.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

omit [Finite G] in
private theorem normalizes_crossing_of_centralizer_generation
    (K C : Subgroup G) (x : G)
    (hnormal : ∀ i ∈ C, orderOf i = 2 → centralizer ({i} : Set G) ≤ normalizer (K : Set G))
    (hgen : K ≤ ⨆ (j : G) (_ : j ∈ C.conjBy x⁻¹) (_ : orderOf j = 2),
      K ⊓ centralizer ({j} : Set G)) :
    K ≤ normalizer (K.conjBy x⁻¹ : Set G) := by
  apply hgen.trans
  refine iSup_le fun j => iSup_le fun hj => iSup_le fun hj2 => ?_
  obtain ⟨i, hi, hij⟩ := hj
  have hi2 : orderOf i = 2 := by
    have he := (MulAut.conj x⁻¹).orderOf_eq i
    change MulAut.conj x⁻¹ i = j at hij
    rw [hij, hj2] at he
    exact he.symm
  have h := CrossingPair.crossing_factor_normalized K i x (hnormal i hi hi2)
  have hij' : x⁻¹ * i * x = j := by simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hij
  rw [hij'] at h
  exact inf_le_right.trans h

private theorem dihedral_noncommuting_involutions {k : ℕ} (hk : 2 ≤ k) :
    ∃ a b : DihedralGroup (2 ^ k), orderOf a = 2 ∧ orderOf b = 2 ∧ ¬ Commute a b := by
  refine ⟨DihedralGroup.sr 0, DihedralGroup.sr 1, DihedralGroup.orderOf_sr _,
    DihedralGroup.orderOf_sr _, ?_⟩
  intro h
  have he : (1 : ZMod (2 ^ k)) = -1 := by
    apply DihedralGroup.r.inj
    simpa only [DihedralGroup.sr_mul_sr, sub_zero, zero_sub] using h.eq
  have hz : (2 : ZMod (2 ^ k)) = 0 := by
    calc
      (2 : ZMod (2 ^ k)) = 1 + 1 := by norm_num
      _ = -1 + 1 := congrArg (fun q : ZMod (2 ^ k) => q + 1) he
      _ = 0 := neg_add_cancel _
  have hd : 2 ^ k ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).mp hz
  have hh : 4 ≤ 2 ^ k := by
    calc
      4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  have hl := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

private theorem involution_pair_map {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f)
    (h : ∃ a b : A, orderOf a = 2 ∧ orderOf b = 2 ∧ ¬ Commute a b) :
    ∃ a b : B, orderOf a = 2 ∧ orderOf b = 2 ∧ ¬ Commute a b := by
  obtain ⟨a,b,ha,hb,hn⟩ := h
  refine ⟨f a, f b, (orderOf_injective f hf a).trans ha,
    (orderOf_injective f hf b).trans hb, ?_⟩
  intro hh
  exact hn (hf (by simpa only [map_mul] using hh.eq))

private theorem semidihedral_noncommuting_involutions :
    ∃ a b : Semidihedral.StandardModel 4 (by decide),
      orderOf a = 2 ∧ orderOf b = 2 ∧ ¬ Commute a b := by
  obtain ⟨_,_,_,_,⟨e⟩,_⟩ := ABG.QuasiDihedral.explicit_subgroup_models (by decide : 4 ≤ 4)
    (Semidihedral.standardRotation 4 (by decide)) (Semidihedral.standardReflection 4 (by decide))
    (Semidihedral.standardModel_card 4 (by decide))
    (Semidihedral.standardRotation_order 4 (by decide))
    (Semidihedral.standardReflection_order 4 (by decide))
    (Semidihedral.standard_conjugation 4 (by decide))
    (Semidihedral.standard_generators 4 (by decide))
  exact involution_pair_map ((Subgroup.subtype _).comp e.symm.toMonoidHom)
    (Subtype.val_injective.comp e.symm.injective)
    (dihedral_noncommuting_involutions (by decide : 2 ≤ 2))

private theorem crossing_centralizer_generation
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (x : G) (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hx2 : x ^ 2 ∈ (S : Subgroup H).map H.subtype)
    (hmodel : ∀ (a : ((twoCore H).conjBy x⁻¹) →* AlternatingSix.ShadowLocal.AutA6),
      Function.Injective a → ∀ N : Subgroup AlternatingSix.ShadowLocal.A6,
      (∀ i : (twoCore H).conjBy x⁻¹, orderOf i = 2 → (a i).fixedSubgroup ≤ N) → N = ⊤) :
    K ≤ ⨆ (j : G) (_ : j ∈ (twoCore H).conjBy x⁻¹) (_ : orderOf j = 2),
      K ⊓ centralizer ({j} : Set G) := by
  let Y := (S : Subgroup H).map H.subtype
  let D := (twoCore H).conjBy x⁻¹
  let W : Subgroup G := ⨆ (j : G) (_ : j ∈ D) (_ : orderOf j = 2),
    K ⊓ centralizer ({j} : Set G)
  have hc := MathieuSourceSetup.core_eq_sylow_centralizer c hgen
  have hCY : twoCore H ≤ Y := hc ▸ inf_le_left
  have hDY : D ≤ Y := by
    have hy : Y.conjBy x⁻¹ = Y :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (Y : Set G)).inv_mem hxN)
    exact (map_mono hCY).trans hy.le
  have hDK : D ≤ normalizer (K : Set G) := hDY.trans ((map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance))
  let a := Theory.GroupAction.ModelConjugation.action D K hDK eK
  have hai : Function.Injective a := by
    apply (injective_iff_map_eq_one a).mpr
    intro d hd
    have hh : d ∈ a.ker := hd
    rw [Theory.GroupAction.ModelConjugation.action_ker] at hh
    have hdC : (d : G) ∈ twoCore H := hc ▸ ⟨hDY d.property, hh⟩
    have hdis := (generated_twoCore_disjoint S (MathieuSourceSetup.sourceTuple c)
      ⟨c.component_le,c.component⟩ hgen hxT hxS hxN hx2).1
    exact Subtype.ext (disjoint_def.mp hdis hdC d.property)
  let f : AlternatingSix.ShadowLocal.A6 →* G := K.subtype.comp eK.symm.toMonoidHom
  have hN : W.comap f = ⊤ := by
    apply hmodel a hai
    intro d hd b hb
    have he : a d b = b := (MulAut.mem_fixedSubgroup _ _).mp hb
    change eK (K.normalizerMonoidHom (inclusion hDK d) (eK.symm b)) = b at he
    have hc' : (d : G) * (eK.symm b : G) * (d : G)⁻¹ = (eK.symm b : G) := by
      have hh := congrArg (fun k : K => (k : G)) (eK.injective (he.trans (eK.apply_symm_apply b).symm))
      exact hh
    have hd2 : orderOf (d : G) = 2 := (orderOf_coe d).trans hd
    have hw : K ⊓ centralizer ({(d : G)} : Set G) ≤ W :=
      le_iSup_of_le (d : G) (le_iSup_of_le d.property (le_iSup_of_le hd2 le_rfl))
    exact hw ⟨(eK.symm b).property, mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp hc').symm⟩
  intro k hk
  have hh : eK ⟨k,hk⟩ ∈ W.comap f := hN ▸ mem_top _
  change (eK.symm (eK ⟨k,hk⟩) : G) ∈ W at hh
  simpa only [eK.symm_apply_apply] using hh

private theorem a6_crossing_false_of_normalizes
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (hC : twoCore H ≠ ⊥)
    (x : G) (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hx2 : x ^ 2 ∈ (S : Subgroup H).map H.subtype)
    (hKN : K ≤ normalizer (K.conjBy x⁻¹ : Set G)) : False := by
  let Y := (S : Subgroup H).map H.subtype
  let L := K.conjBy x⁻¹
  let C := twoCore H
  have hYL : Y ≤ normalizer (K : Set G) := (map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance)
  have hLL : L.conjBy x⁻¹ = K := by
    change (K.conjBy x⁻¹).conjBy x⁻¹ = K
    rw [conjBy_conjBy]
    have hx : x⁻¹ * x⁻¹ ∈ normalizer (K : Set G) := by
      have h : (x ^ 2)⁻¹ ∈ normalizer (K : Set G) := (normalizer (K : Set G)).inv_mem (hYL hx2)
      simpa only [pow_two, mul_inv_rev] using h
    exact mem_normalizer_iff_map_conj_eq.mp hx
  have hLN : L ≤ normalizer (K : Set G) := by
    have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hKN
    rw [map_equiv_normalizer_eq] at hh
    exact hLL ▸ hh
  have hneq : K ≠ L := by
    intro he
    have hc := MathieuSourceSetup.core_eq_sylow_centralizer c hgen
    have hcx : C.conjBy x⁻¹ = C := by
      change (twoCore H).conjBy x⁻¹ = twoCore H
      rw [hc]
      exact (CrossingPair.sylow_centralizer_crossing K Y x hxN).symm.trans
        (by change Y ⊓ centralizer (L : Set G) = Y ⊓ centralizer (K : Set G); rw [←he])
    have hd := (generated_twoCore_disjoint S (MathieuSourceSetup.sourceTuple c)
      ⟨c.component_le,c.component⟩ hgen hxT hxS hxN hx2).1
    rw [hcx] at hd
    exact hC (disjoint_self.mp hd)
  let : IsQuasisimple K := (show IsComponentIn K H from ⟨c.component_le,c.component⟩).quasisimple
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv ((MulAut.conj x⁻¹).subgroupMap K)
  have hKJ : IsComponentIn K (K ⊔ L) := by
    refine ⟨le_sup_left, ?_, IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe le_sup_left).symm⟩
    exact ((normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le K.le_normalizer hLN)).isSubnormal
  have hLJ : IsComponentIn L (K ⊔ L) := by
    refine ⟨le_sup_right, ?_, IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe le_sup_right).symm⟩
    exact ((normal_subgroupOf_iff_le_normalizer le_sup_right).mpr (sup_le hKN L.le_normalizer)).isSubnormal
  have hcomm := hKJ.commutator_eq_bot_of_ne hLJ hneq
  exact alternatingGroup.not_commuting_a6_of_quasithin hG.quasithin K L eK
    (((MulAut.conj x⁻¹).subgroupMap K).symm.trans eK)
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)
private theorem a6_source_false_of_component_centralizers
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (hcomponent : ∀ i ∈ twoCore H, orderOf i = 2 → IsComponentIn K (centralizer ({i} : Set G)))
    (hmodel : ∀ (x : G) (a : ((twoCore H).conjBy x⁻¹) →* AlternatingSix.ShadowLocal.AutA6),
      Function.Injective a → ∀ N : Subgroup AlternatingSix.ShadowLocal.A6,
      (∀ i : (twoCore H).conjBy x⁻¹, orderOf i = 2 → (a i).fixedSubgroup ≤ N) → N = ⊤) : False := by
  obtain ⟨x,hxT,hxS,hxN,hx2⟩ := exists_outside_normalizer_square_mem
    ((S : Subgroup H).map H.subtype) (c.T : Subgroup G) c.T.isPGroup' c.sylow_lt
  have hnormal (i : G) (hi : i ∈ twoCore H) (hi2 : orderOf i = 2) :
      centralizer ({i} : Set G) ≤ normalizer (K : Set G) := by
    have hc := hcomponent i hi hi2
    have hn : (K.subgroupOf (centralizer ({i} : Set G))).Normal :=
      alternatingGroup.normal_of_component_a6_of_quasithin
        (hG.quasithin.subgroup (centralizer ({i} : Set G))) _
        ((subgroupOfEquivOfLe hc.1).trans eK) hc.2
    exact (normal_subgroupOf_iff_le_normalizer hc.1).mp hn
  have hgener := crossing_centralizer_generation c hgen eK x hxT hxS hxN hx2 (hmodel x)
  have hKN := normalizes_crossing_of_centralizer_generation K (twoCore H) x hnormal hgener
  have hC : twoCore H ≠ ⊥ := by
    obtain ⟨t,_,ht,_,htC,_⟩ := MathieuSourceSetup.source_central_marks c hG hempty hgen hb
    intro he
    have ht1 : t = 1 := mem_bot.mp (he ▸ htC)
    simp [ht1] at ht
  exact a6_crossing_false_of_normalizes c hG hgen eK hC x hxT hxS hxN hx2 hKN
private theorem a6_false_of_noncommuting_core
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (hcomponent : ∀ i ∈ twoCore H, orderOf i = 2 → IsComponentIn K (centralizer ({i} : Set G)))
    (hpair : ∃ a b : twoCore H, orderOf a = 2 ∧ orderOf b = 2 ∧ ¬ Commute a b) : False := by
  apply a6_source_false_of_component_centralizers c hG hempty hgen hb eK hcomponent
  intro x f hf N hfixed
  let e := (MulAut.conj x⁻¹).subgroupMap (twoCore H)
  obtain ⟨a,b,ha,hb,hab⟩ := involution_pair_map e.toMonoidHom e.injective hpair
  have hp : IsPGroup 2 ((twoCore H).conjBy x⁻¹) :=
    (isPGroup_pCoreIn 2 H).map (MulAut.conj x⁻¹).toMonoidHom
  exact AlternatingSix.NonabelianInvolutionGeneration.fixed_generation_of_noncommuting_involutions
    hp f hf a b (ha ▸ pow_orderOf_eq_one a) (hb ▸ pow_orderOf_eq_one b)
    (fun he => hab he) N hfixed

/-- The M10 alternative in the original A6 source setup is impossible. -/
theorem MathieuSourceSetup.m10_source_false
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (eQ : (H ⧸ pCore 2 H) ≃* AlternatingSix.M10.extension) : False := by
  let D := K.subgroupOf H
  let eD := (subgroupOfEquivOfLe c.component_le).trans eK
  let : D.Normal := alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.quasithin.subgroup H) D eD c.component
  have hcomponent := MathieuSourceSetup.nonfull_a6_core_involution_component
    c hG hempty hgen hb hstar eK (Or.inl ⟨eQ⟩)
  apply a6_false_of_noncommuting_core c hG hempty hgen hb eK hcomponent
  rcases MathieuSourceSetup.m10_source_twoCore_models c hG hempty hgen hb hstar eK eQ with hm | hm
  · obtain ⟨e⟩ := hm
    exact involution_pair_map e.symm.toMonoidHom e.symm.injective
      (dihedral_noncommuting_involutions (by decide : 2 ≤ 2))
  · obtain ⟨e⟩ := hm
    exact involution_pair_map e.symm.toMonoidHom e.symm.injective semidihedral_noncommuting_involutions

/-- The PGL2(9) alternative in the original A6 source setup is impossible. -/
theorem MathieuSourceSetup.pgl_nine_source_false
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (eQ : (H ⧸ pCore 2 H) ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) : False := by
  let D := K.subgroupOf H
  let eD := (subgroupOfEquivOfLe c.component_le).trans eK
  let : D.Normal := alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.quasithin.subgroup H) D eD c.component
  have hcomponent := MathieuSourceSetup.nonfull_a6_core_involution_component
    c hG hempty hgen hb hstar eK (Or.inr ⟨eQ⟩)
  apply a6_false_of_noncommuting_core c hG hempty hgen hb eK hcomponent
  obtain ⟨k,hk,⟨e⟩⟩ := MathieuSourceSetup.pgl_nine_source_twoCore_model c hG hempty hgen hb hstar eK eQ
  exact involution_pair_map e.symm.toMonoidHom e.symm.injective (dihedral_noncommuting_involutions hk)

/-- The original A6 source setup has the full Aut(A6) quotient of H by its actual two-core. -/
theorem MathieuSourceSetup.alternating_six_full_core_quotient
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6) :
    Nonempty ((H ⧸ pCore 2 H) ≃* AlternatingSix.ShadowLocal.AutA6) := by
  let D := K.subgroupOf H
  let eD := (subgroupOfEquivOfLe c.component_le).trans eK
  let : D.Normal := alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.quasithin.subgroup H) D eD c.component
  rcases MathieuSourceSetup.normal_alternating_six_core_quotient c hG hempty hgen eK with hm | hm | h
  · obtain ⟨eQ⟩ := hm
    exact (MathieuSourceSetup.m10_source_false c hG hempty hgen hb hstar eK eQ).elim
  · obtain ⟨eQ⟩ := hm
    exact (MathieuSourceSetup.pgl_nine_source_false c hG hempty hgen hb hstar eK eQ).elim
  · exact h
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
