module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupBlock
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupKernelFusion
public import Theory.SpecificGroups.SL2.OddSylowCentralizer
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Nonabelian

/-!
# Block exclusion and abelian normalizer spans in odd degree

The actual Cartan centralizer C_T(D_L) covers the Sylow image of H/O₂(H),
which contains a nonabelian Sylow subgroup of the literal PSL₃(4) section.
On the other hand, odd-degree inner action puts C_T(D_L) in O₂(LT).
If O₂(L) were the selected natural module, commutators and C_T(L) = 1
would make O₂(LT) elementary abelian. This gives the required contradiction.

The block axioms, their exact module order and the already proved equality
O₂(L) = [O₂(L),L] reduce a natural block to this excluded core equality.
Separately, the nonabelian G.2.3 span branch forces the same equality when
the original quotient-action kernel is solvable. Thus the full point-normalizer
span is abelian, and every intermediate span is elementary abelian.

Solvability is retained only for that literal kernel, as the consequence of
the independent F.1.12 Suzuki recognition. Full residual-normalizer TI and
final parity assembly remain with qt-d-1222-linear-field-parity.
Source: Aschbacher–Smith 5.1.17, printed pp.640–641 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem local_core_le_T :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
  simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
    pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)

omit [Finite G] in
private theorem local_join_normalizes_core : L ⊔ (T : Subgroup G) ≤
    normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
  (L ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

/-- A collapsed natural core makes the full local core elementary. -/
theorem fundamental_local_core_elementary_of_core_eq
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hCT : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    (he : L.pCoreIn 2 = D.moduleSubgroup) :
    IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let := D.module_elementary
  have hQV : Q ≤ centralizer (D.moduleSubgroup : Set G) := by
    simpa only [Chapter3.Section02.localJoin,componentOrbit_sup] using D.core_centralizes_module
  have hpow (x : Q) : x^2 = 1 := by
    have hfix : (x : G)^2 ∈ centralizer (L : Set G) := by
      intro l hl
      let v := l*(x : G)*l⁻¹*(x : G)⁻¹
      have hvL : v ∈ L := by
        have hc : ⁅L,Q⁆ ≤ L := le_normalizer_iff_commutator_le_left.mp
          ((local_core_le_T (L := L)).trans hTL)
        exact hc (commutator_mem_commutator hl x.property)
      have hvQ : v ∈ Q := by
        have hc := le_normalizer_iff_commutator_le_right.mp
          (show L ≤ normalizer (Q : Set G) from le_sup_left.trans local_join_normalizes_core)
        exact hc (commutator_mem_commutator hl x.property)
      have hv : v ∈ D.moduleSubgroup := he ▸ inf_pCoreIn_le_of_le 2
        (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) ⟨hvL,hvQ⟩
      have hc : Commute v (x : G) := hQV x.property v hv
      have hv2 : v^2=1 := elemPow_eq_one_of_isElementaryAbelian v hv
      have hs : (l*(x : G)*l⁻¹)^2=(x : G)^2 := by
        calc
          _ = (v*(x : G))^2 := by congr 1; dsimp [v]; group
          _ = v^2*(x : G)^2 := hc.mul_pow 2
          _ = _ := by rw [hv2,one_mul]
      calc
        l*(x : G)^2 = (l*(x : G)*l⁻¹)^2*l := by simp only [pow_two]; group
        _ = (x : G)^2*l := by rw [hs]
    exact Subtype.ext (mem_bot.mp (hCT ▸
      (show (x : G)^2 ∈ (T : Subgroup G) ⊓ centralizer (L : Set G) from
        ⟨(T : Subgroup G).pow_mem (local_core_le_T x.property) 2,hfix⟩)))
  exact {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hpow x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }

/-- The odd-degree Cartan centralizer lies in the full local two-core. -/
theorem sylow_cartan_centralizer_le_local_core
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hn : 1 < n) (hodd : Odd n) (c : CartanPair T L H A B) :
    (T : Subgroup G) ⊓ centralizer (A : Set G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hfactor := sylow_factor_of_odd hTL hpsl hodd
  let J := L ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  let π := QuotientGroup.mk' (pCore 2 J)
  have hAL : A ≤ L := c.left_le.trans inf_le_left
  have hAodd : Odd (Nat.card A) := by
    have hh := OddHall.odd_hall_odd c.left_hall
    rwa [Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv] at hh
  have hAne : A ≠ ⊥ := by
    intro hz
    have hh := (c.left_cyclic_and_card hTL hpsl).2
    rw [hz,card_bot] at hh
    have h4 : 4 ≤ 2^n := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn
    omega
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hAne
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let eSL := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  let f : L →* SL(2,F) := eSL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f := eSL.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ eSL.injective,QuotientGroup.ker_mk']
  let aL : L := ⟨a,hAL ha⟩
  have hfa : f aL ≠ 1 := by
    intro hz
    have haQ : a ∈ L.pCoreIn 2 := mem_map_of_mem L.subtype (show aL ∈ pCore 2 L from hk ▸ (show aL ∈ f.ker from hz))
    have hd : Disjoint A (L.pCoreIn 2) := by
      apply disjoint_of_coprime_natCard
      obtain ⟨k,hk⟩ := (isPGroup_pCoreIn 2 L).exists_card_eq
      rw [hk]
      exact hAodd.coprime_two_right.pow_right k
    exact ha1 (disjoint_def.mp hd ha haQ)
  have hfaPow : (f aL)^Nat.card A=1 := by
    rw [←map_pow]
    have he : aL^Nat.card A=1 := Subtype.ext
      (congrArg (fun z : A => (z : G)) (pow_card_eq_one' (x := (⟨a,ha⟩ : A))))
    rw [he,map_one]
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  rintro x ⟨hxT,hxA⟩
  have hxprod : x ∈ (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) * (Q : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _
      (inf_le_right.trans (show L ≤ normalizer (Q : Set G) from
        le_sup_left.trans local_join_normalizes_core)),←hfactor]
    exact hxT
  obtain ⟨s,hs,u,hu,hxu⟩ := hxprod
  change s*u=x at hxu
  let sj : J := ⟨s,mem_sup_left hs.2⟩
  let uj : J := ⟨u,pCoreIn_le 2 J hu⟩
  let aj : J := ⟨a,mem_sup_left (hAL ha)⟩
  have huπ : π uj=1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact (mem_map_iff_mem J.subtype_injective).mp hu
  have hcomm : Commute (π sj) (π aj) := by
    have he : (sj*uj)*aj=aj*(sj*uj) := by
      apply Subtype.ext
      change (s*u)*a=a*(s*u)
      rw [hxu]
      exact (mem_centralizer_iff.mp hxA a ha).symm
    have hh := congrArg π he
    change π sj * π aj = π aj * π sj
    simpa only [map_mul,huπ,mul_one] using hh
  have hsaQ : ⁅s,a⁆ ∈ Q := by
    have he : π ⁅sj,aj⁆=1 := by rw [map_commutatorElement]; exact hcomm.commutator_eq
    exact mem_map_of_mem J.subtype ((QuotientGroup.eq_one_iff _).mp he)
  have hsaL : ⁅s,a⁆ ∈ L := by
    exact L.mul_mem (L.mul_mem (L.mul_mem hs.2 (hAL ha)) (L.inv_mem hs.2)) (L.inv_mem (hAL ha))
  have hsa : ⁅s,a⁆ ∈ L.pCoreIn 2 := inf_pCoreIn_le_of_le 2
    (show L ≤ J from le_sup_left) ⟨hsaL,hsaQ⟩
  let sl : L := ⟨s,hs.2⟩
  have hcommL : Commute (f sl) (f aL) := by
    have hm : ⁅sl,aL⁆ ∈ pCore 2 L := (mem_map_iff_mem L.subtype_injective).mp hsa
    have he : f ⁅sl,aL⁆=1 := show ⁅sl,aL⁆ ∈ f.ker from hk.symm ▸ hm
    rw [map_commutatorElement] at he
    exact commutatorElement_eq_one_iff_commute.mp he
  have hfs : f sl=1 := Matrix.SpecialLinearGroup.eq_one_of_sylow_commutes_nontrivial_odd
    (S.mapSurjective hf) (f sl) (f aL) (mem_map_of_mem f (hS.symm ▸ hs.1)) hfa hAodd hfaPow hcommL
  have hsQ : s ∈ Q := (pCoreIn_mono_of_normalizes
    (show L ≤ J from le_sup_left) (sup_le L.le_normalizer hTL))
      (mem_map_of_mem L.subtype (show sl ∈ pCore 2 L from hk ▸ (show sl ∈ f.ker from hfs)))
  exact hxu ▸ Q.mul_mem hsQ hu


/-- The literal residual quotient forces every Sylow of H/O₂(H) to be nonabelian. -/
theorem residual_quotient_sylow_nonabelian
    (hTH : (T : Subgroup G) ≤ H)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (P : Sylow 2 (H ⧸ pCore 2 H)) : ¬ IsMulCommutative P := by
  intro hp
  let := hp
  let K := generalizedFitting (H ⧸ pCore 2 H)
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_normal K
  let i : S →* P := {
    toFun s := ⟨s.val.val,by
      change (s : K) ∈ (P : Subgroup (H ⧸ pCore 2 H)).subgroupOf K
      rw [←hS]
      exact s.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hi : Function.Injective i := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : P => (z : H ⧸ pCore 2 H)) he
  let : IsMulCommutative S := IsMulCommutative.of_comm fun x y => hi ((i.map_mul x y).trans ((mul_comm (i x) (i y)).trans (i.map_mul y x).symm))
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := residual_coreQuotient_fitting_model hTH hm
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let d : S ≃* R := (S : Subgroup K).equivMapOfInjective e.toMonoidHom e.injective
  have hr : IsMulCommutative R := IsMulCommutative.of_comm fun x y => d.symm.injective ((d.symm.map_mul x y).trans
    ((mul_comm (d.symm x) (d.symm y)).trans (d.symm.map_mul y x).symm))
  exact Matrix.PSL3.LinearThree.sylow_not_isMulCommutative F (n := 2) (by decide) hF R hr

/-- The source Cartan centralizer covers the entire Sylow image of H/O₂(H),
so it cannot be abelian. No solvability premise is needed. -/
theorem sylow_cartan_centralizer_nonabelian
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    ¬ IsMulCommutative ((T : Subgroup G) ⊓ centralizer (A : Set G) : Subgroup G) := by
  intro hab
  let C := (T : Subgroup G) ⊓ centralizer (A : Set G)
  let : IsMulCommutative C := hab
  have hAT := cartan_normalizes_sylow_of_odd c h.sylow_normalizes h.linear hodd
  have hcop : Nat.Coprime (Nat.card A) (Nat.card T) := by
    obtain ⟨k,hk⟩ := T.isPGroup'.exists_card_eq
    rw [hk]
    exact ((cartan_card_coprime_six_of_odd c h.sylow_normalizes h.linear hodd).of_dvd_right
      (by decide : 2 ∣ 6)).pow_right k
  let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
  have hmove := eq_commutator_sup_centralizer_of_solvable_coprime
    (T : Subgroup G) A hAT inferInstance hcop
  let J := H ⊔ A
  let q := QuotientGroup.mk' (pCore 2 J)
  have hTJ : (T : Subgroup G) ≤ J := (show (T : Subgroup G) ≤ H from hH.1.1.2).trans le_sup_left
  have hc := cartan_image_central_of_odd h hH c hodd hK hnf hm
  have hcomm : ⁅(T : Subgroup G),A⁆ ≤ H.pCoreIn 2 := by
    rw [←odd_join_twoCore h hH c hodd hK hnf]
    apply commutator_le.mpr
    intro t ht a ha
    let tj : J := ⟨t,hTJ ht⟩
    let aj : J := ⟨a,mem_sup_right ha⟩
    have hcom : Commute (q tj) (q aj) := mem_center_iff.mp
      (hc (mem_map_of_mem q (show aj ∈ A.subgroupOf J from ha))) (q tj)
    have hk : ⁅tj,aj⁆ ∈ pCore 2 J := (QuotientGroup.eq_one_iff _).mp
      (by change q ⁅tj,aj⁆ = 1; rw [map_commutatorElement]; exact hcom.commutator_eq)
    exact mem_map_of_mem J.subtype hk
  let qH := QuotientGroup.mk' (pCore 2 H)
  let P := (T.subtype hH.1.1.2).mapSurjective (f := qH) (QuotientGroup.mk'_surjective _)
  have hCH : C ≤ H := inf_le_left.trans hH.1.1.2
  let d := subgroupOfEquivOfLe hCH
  let : IsMulCommutative (C.subgroupOf H) := IsMulCommutative.of_comm fun x y => d.injective (by
    simp only [map_mul,mul_comm])
  have hPeq : (P : Subgroup (H ⧸ pCore 2 H)) = (C.subgroupOf H).map qH := by
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      intro t ht
      have hT : (T : Subgroup G) ≤ (((C.subgroupOf H).map qH).comap qH).map H.subtype := by
        rw [hmove]
        apply sup_le
        · intro x hx
          have hxQ := hcomm hx
          let xh : H := ⟨x,pCoreIn_le 2 H hxQ⟩
          refine ⟨xh,?_,rfl⟩
          change qH xh ∈ (C.subgroupOf H).map qH
          have hx1 : qH xh=1 := (QuotientGroup.eq_one_iff _).mpr
            ((mem_map_iff_mem H.subtype_injective).mp hxQ)
          rw [hx1]
          exact one_mem _
        · intro x hx
          exact ⟨⟨x,hCH hx⟩,mem_map_of_mem qH (show (⟨x,hCH hx⟩ : H) ∈ C.subgroupOf H from hx),rfl⟩
      obtain ⟨t',ht',he⟩ := hT ht
      exact (Subtype.ext he : t'=t) ▸ ht'
    · exact map_mono (comap_mono (show C ≤ (T : Subgroup G) from inf_le_left))
  have hp : IsMulCommutative P := by
    rw [hPeq]
    infer_instance
  exact residual_quotient_sylow_nonabelian hH.1.1.2 hm P hp

/-- Exclude precisely the core equality forced by the nonabelian G.2.3 branch. -/
theorem fundamental_core_ne_module
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L) :
    L.pCoreIn 2 ≠ D.moduleSubgroup := by
  intro he
  have hHC : H ≤ omegaCentralizer T :=
    (residual_le_omegaCentralizer_iff hH.1.1.2).mp
      (residual_centralizes_omega_of_nonfaithful h.qtke hH.1.1 hK.1 hnf)
  have hz := h.centralOmega_disjoint_of_outside_centralizes hH hHC
  have hCT := Stellmacher.inf_centralizer_eq_bot_of_omega_center
    (T : Subgroup G) L T.isPGroup' h.sylow_normalizes hz
  let := fundamental_local_core_elementary_of_core_eq D h.sylow_normalizes hCT he
  have hc := sylow_cartan_centralizer_le_local_core h.sylow_normalizes h.linear h.exponent hodd c
  let i := inclusion hc
  have hi := inclusion_injective hc
  exact sylow_cartan_centralizer_nonabelian h hH c hodd hK hnf hm
    (IsMulCommutative.of_comm fun x y => hi (by simp only [map_mul,mul_comm]))

/-- The original full point-normalizer span is abelian under the exact
independent quotient-centralizer solvability input. -/
theorem fundamental_normalizer_span_abelian_of_solvable
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n) :
    IsMulCommutative (normalizerSetup T L D.moduleSubgroup).U := by
  by_contra hnon
  exact fundamental_core_ne_module h hH c hodd hK hnf hm D
    (fundamental_nonabelian_block_of_solvable h hH c hodd hK hnf hm hsolv D hnat hnon).1


/-- Every intermediate source span is elementary abelian, including the
full point normalizer and the original HD_L. -/
theorem fundamental_intermediate_span_elementary_of_solvable
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    (J : Subgroup G) (hJN : J ≤ (normalizerSetup T L D.moduleSubgroup).G₁) :
    IsElementaryAbelian 2 (conjugateSpanBy D.moduleSubgroup J) := by
  let : IsMulCommutative (conjugateSpanBy D.moduleSubgroup
      (normalizerSetup T L D.moduleSubgroup).G₁) :=
    fundamental_normalizer_span_abelian_of_solvable h hH c hodd hK hnf hm hsolv D hnat
  let : IsMulCommutative (conjugateSpanBy D.moduleSubgroup J) :=
    conjugateSpanBy_isMulCommutative_of_le le_rfl hJN
  let := D.module_elementary
  let : IsMulCommutative (closure {x : G | ∃ g ∈ J, ∃ v ∈ D.moduleSubgroup, g*v*g⁻¹=x}) :=
    ‹IsMulCommutative (conjugateSpanBy D.moduleSubgroup J)›
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro _ ⟨g,_,v,hv,rfl⟩
  rw [conj_pow,elemPow_eq_one_of_isElementaryAbelian v hv,mul_one,mul_inv_cancel]

/-- Exclude the original natural block, keeping its actual core and module. -/
theorem fundamental_not_block
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n) : ¬ ChapterC.IsL2EvenBlock L n := by
  intro hb
  have hHC : H ≤ omegaCentralizer T :=
    (residual_le_omegaCentralizer_iff hH.1.1.2).mp
      (residual_centralizes_omega_of_nonfaithful h.qtke hH.1.1 hK.1 hnf)
  have hz := h.centralOmega_disjoint_of_outside_centralizes hH hHC
  have hCT := Stellmacher.inf_centralizer_eq_bot_of_omega_center
    (T : Subgroup G) L T.isPGroup' h.sylow_normalizes hz
  have hcoreT : L.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer h.sylow_normalizes)).trans local_core_le_T
  have hcenter : center L = ⊥ := by
    apply bot_unique
    intro x hx
    have hxQ : x ∈ pCore 2 L := hb.2.1.centralizer_blockU.le ((center_le_centralizer _) hx)
    apply mem_bot.mpr
    apply Subtype.ext
    exact mem_bot.mp (hCT ▸ (show (x : G) ∈ (T : Subgroup G) ⊓ centralizer (L : Set G) from
      ⟨hcoreT (mem_map_of_mem L.subtype hxQ),fun l hl =>
        congrArg Subtype.val (mem_center_iff.mp hx ⟨l,hl⟩)⟩))
  have hu : Nat.card (ChapterC.blockU L) = 2^(n*2) := by
    have hh := hb.module_card
    have hzU : ChapterC.blockFixed L = ⊥ := by simp [ChapterC.blockFixed,hcenter]
    change Nat.card ((ChapterC.blockU L) ⧸ ChapterC.blockFixed L) = _ at hh
    rw [hzU] at hh
    exact (Nat.card_congr QuotientGroup.quotientBot.toEquiv).symm.trans hh
  have heU : (ChapterC.blockU L).map L.subtype = L.pCoreIn 2 := by
    simp only [ChapterC.blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype]
    exact (odd_linear_core_eq_commutator h hodd).symm
  have hc : Nat.card (L.pCoreIn 2) = 2^(n*2) := by
    rw [←heU,card_map_of_injective L.subtype_injective]
    exact hu
  have hOrbit : Chapter3.Section02.localOrbit T L = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl h.sylow_normalizes)
      (le_componentOrbit _ _)
  have hV : D.moduleSubgroup ≤ L.pCoreIn 2 := by
    simpa only [hOrbit] using D.module_le_orbitCore
  exact fundamental_core_ne_module h hH c hodd hK hnf hm D
    (eq_of_le_of_card_ge hV (by rw [hc,hnat.card])).symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
