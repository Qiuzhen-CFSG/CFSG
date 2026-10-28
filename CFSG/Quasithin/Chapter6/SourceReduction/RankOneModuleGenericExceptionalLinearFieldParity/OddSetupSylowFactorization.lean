module
public import Theory.GroupTheory.NormalSylowFactorization
public import Theory.GroupTheory.ConjugateSpanSupplement
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupPrimitiveTI
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupKernelFusion

/-!
# Full quotient-centralizer Sylows in the original parity argument

Solvable Thompson factorization on C_K T restricts to C_K after taking
the two-residual of the normal centralizer factor. Thus C_K is the product
of C_{C_K}(Z₀) and N_{C_K}(Baum(T)), where Z₀ is the actual omega-center
orbit. A Sylow subgroup of the latter factor containing a Cartan Sylow
extends to a Sylow of all of C_K, with the exact centralizer product.
Its Cartan intersection is Sylow in D_L. Normality of the literal action
kernel also gives M⁺ = C_K N_{M⁺}(P). A primitive prime exceeds n, so
every such prime-group in N_G(L) acts by inner automorphisms on L/O₂(L).

The remaining source step is the action of P ∩ N_G(L) on Z₁. The present
product does not assert P = P_L C_P(Z₁), point stability, or residual TI.
These and final parity assembly remain with qt-d-1222-linear-field-parity;
the independent Suzuki source is retained as the literal kernel-solvability
premise. Source: Aschbacher–Smith 5.1.17, printed p.640 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}

theorem residual_kernel_baumann_factorization
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker) :
    let C := (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
      (normalizer (residual H : Set G)).subtype
    let Z₀ := conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) C
    C = (C ⊓ centralizer (Z₀ : Set G)) ⊔
      (C ⊓ normalizer (ChapterB.baumann (T : Subgroup G) : Set G)) := by
  let N := normalizer (residual H : Set G)
  let f := normalizerQuotientAction (residual H) (pCore 2 (residual H))
  let C := f.ker.map N.subtype
  let M := C ⊔ (T : Subgroup G)
  have hTN : (T : Subgroup G) ≤ N := hH.1.1.2.trans (le_normalizer_residual H)
  have hNC : N ≤ normalizer (C : Set G) := by
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using
      f.ker.le_normalizer_map N.subtype
  have hTC := hTN.trans hNC
  have hMN : M ≤ N := sup_le (map_subtype_le _) hTN
  let : Group.IsSolvable f.ker := hsolv
  let : Group.IsSolvable C := Group.isSolvable_of_surjective (N.subtype.subgroupMap_surjective f.ker)
  let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
  have hsolM : Group.IsSolvable M := Group.isSolvable_sup_of_normalizes C (T : Subgroup G) hTC
  have hmax := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hK).normalizer_maximal
  have he : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTN)
      (le_componentOrbit _ _)
  rw [he] at hmax
  have hsq : IsStronglyQuasithin N := (h.qtke.twoLocal_sqtk hmax.1).stronglyQuasithin
  have hcN := h.qtke.evenCharacteristic T N hmax hTN
  have hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M := by
    rw [← generalizedFitting_eq_pCore_of_sylow_overgroup T M N le_sup_right hMN hcN]
    exact centralizer_generalizedFitting_le M
  have h3C : ¬ 3 ∣ Nat.card C := by
    change ¬ 3 ∣ Nat.card (f.ker.map N.subtype)
    rw [card_map_of_injective N.subtype_injective]
    exact Nat.prime_three.coprime_iff_not_dvd.mp
      (CubicEscape.quotientAction_kernel_three_prime (residual H) hsq (linear_residual_quotient hm))
  have h3T : ¬ 3 ∣ Nat.card T := by
    obtain ⟨k,hk⟩ := T.isPGroup'.exists_card_eq
    rw [hk]
    exact Nat.prime_three.coprime_iff_not_dvd.mp ((by decide : Nat.Coprime 3 2).pow_right k)
  have h3M := not_dvd_card_sup_of_normalizes Nat.prime_three C (T : Subgroup G) hTC h3C h3T
  let Ω := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  let : IsElementaryAbelian 2 Ω := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  have hΩT : Ω ≤ (T : Subgroup G) := fun z hz =>
    ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hΩC : Ω ≤ centralizer (T : Set G) := fun z hz =>
    ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2
  have hTΩ : (T : Subgroup G) ≤ normalizer (Ω : Set G) :=
    (le_centralizer_iff.mp hΩC).trans (Subgroup.centralizer_le_normalizer _)
  let U := conjugateSpanBy Ω M
  have hU : U = conjugateSpanBy Ω C :=
    conjugateSpanBy_sup_of_normalizes_seed Ω C (T : Subgroup G) hTΩ hTC
  let F := M ⊓ normalizer (ChapterB.baumann (T : Subgroup G) : Set G)
  let D := M ⊓ centralizer (U : Set G)
  have hTF : (T : Subgroup G) ≤ F := le_inf le_sup_right
    ((T : Subgroup G).le_normalizer.trans (Stellmacher.normalizer_le_normalizer_baumann _))
  have hfactor : C ⊔ (T : Subgroup G) = F ⊔ D := by
    change M = F ⊔ D
    rw [sup_comm F D]
    exact ChapterB.solvable_three_prime_central_seed_factorization T M Ω le_sup_right
      hΩT hΩC hchar hsolM h3M
  have hMD : M ≤ normalizer (D : Set G) :=
    (le_inf M.le_normalizer ((le_normalizer_conjugateSpanBy Ω M).trans
      (normalizer_le_normalizer_centralizer U))).trans inf_normalizer_le_normalizer_inf
  have hf := factorization_in_normal_sylow_supplement T C F D hTC hTF hfactor hMD
  have hCM : C ⊓ M = C := inf_eq_left.mpr le_sup_left
  change C = _
  simpa only [D,F,←inf_assoc,hCM,hU] using hf

/-- The primitive Cartan subgroup extends to a Sylow subgroup of the entire
quotient-centralizer, with the source product and Cartan intersection. -/
theorem residual_kernel_primitive_sylow_factorization
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (c : CartanPair T L H A B) (hodd : Odd n) :
    let C := (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
      (normalizer (residual H : Set G)).subtype
    let Z₀ := conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) C
    ∃ (p : ℕ) (_hp : Fact p.Prime) (E : Subgroup G) (P : Sylow p C) (R : Sylow p A),
      p ≠ 2 ∧ orderOf (2 : ZMod p) = n ∧ E ≤ A ∧ Nat.card E = p ∧
      E ≤ (P : Subgroup C).map C.subtype ∧
      (R : Subgroup A).map A.subtype = (P : Subgroup C).map C.subtype ⊓ A ∧
      (P : Subgroup C).map C.subtype =
        ((P : Subgroup C).map C.subtype ⊓ centralizer (Z₀ : Set G)) ⊔
        ((P : Subgroup C).map C.subtype ⊓ normalizer (L : Set G)) := by
  let N := normalizer (residual H : Set G)
  let f := normalizerQuotientAction (residual H) (pCore 2 (residual H))
  let C := f.ker.map N.subtype
  let Z₀ := conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) C
  let J := C ⊓ normalizer (ChapterB.baumann (T : Subgroup G) : Set G)
  let K := C ⊓ centralizer (Z₀ : Set G)
  have hfactor : C = K ⊔ J := residual_kernel_baumann_factorization h hH hK hm hsolv
  have hAC : A ≤ C := cartan_residual_action_trivial_of_odd h hH c hodd hK hnf hm
  have hAJ : A ≤ J := le_inf hAC
    ((cartan_normalizes_sylow_of_odd c h.sylow_normalizes h.linear hodd).trans
      (Stellmacher.normalizer_le_normalizer_baumann _))
  have hJM : J ≤ normalizer (L : Set G) := inf_le_right.trans
    (baumann_normalizer_le_of_nonfaithful_residual h hH hK hnf)
  let K' := K.subgroupOf C
  let J' := J.subgroupOf C
  let : K'.Normal := normal_subgroupOf_of_le_normalizer
    ((le_inf C.le_normalizer ((le_normalizer_conjugateSpanBy _ C).trans
      (normalizer_le_normalizer_centralizer Z₀))).trans inf_normalizer_le_normalizer_inf)
  have hgen : K' ⊔ J' = ⊤ := by
    rw [←subgroupOf_sup (show K ≤ C from inf_le_left) (show J ≤ C from inf_le_left),
      ←hfactor,subgroupOf_self]
  obtain ⟨p,E,hp,hp2,ho,hEA,hE⟩ :=
    cartan_primitive_prime_subgroup c h.sylow_normalizes h.linear h.exponent hodd
  let hp' : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := IsPGroup.of_card (n := 1) (by simpa using hE)
  obtain ⟨R,hER⟩ := (hEp.comap_subtype (K := A)).exists_le_sylow
  let RA := (R : Subgroup A).map A.subtype
  have hRA : RA ≤ A := map_subtype_le _
  have hER' : E ≤ RA := by
    intro e he
    exact ⟨⟨e,hEA he⟩,hER he,rfl⟩
  let i := C.subtype.comp J'.subtype
  have hi : Function.Injective i := C.subtype_injective.comp J'.subtype_injective
  obtain ⟨Q,hRQ⟩ := ((R.isPGroup'.map A.subtype).comap_of_injective i hi).exists_le_sylow
  have hRQ' : RA ≤ ((Q : Subgroup J').map J'.subtype).map C.subtype := by
    intro r hr
    have hrJ : r ∈ J := hAJ (hRA hr)
    let r' : J' := ⟨⟨r,hrJ.1⟩,hrJ⟩
    exact mem_map_of_mem C.subtype (mem_map_of_mem J'.subtype (hRQ (show r' ∈ RA.comap i from hr)))
  obtain ⟨P,hQP,heP⟩ := Sylow.exists_extension_eq_inf_sup K' J' hgen Q
  let PG := (P : Subgroup C).map C.subtype
  have hQPG : ((Q : Subgroup J').map J'.subtype).map C.subtype ≤ PG := map_mono hQP
  have hRPG : RA ≤ PG := hRQ'.trans hQPG
  have hPRA : PG.subgroupOf A = (R : Subgroup A) :=
    R.is_maximal' (P.isPGroup'.map C.subtype).comap_subtype
      (fun r hr => hRPG (mem_map_of_mem A.subtype hr))
  have hRinf : (R : Subgroup A).map A.subtype = PG ⊓ A := by
    rw [← hPRA,subgroupOf_map_subtype]
  have hQJ : ((Q : Subgroup J').map J'.subtype).map C.subtype ≤ J := by
    rintro _ ⟨x,⟨q,hq,rfl⟩,rfl⟩
    exact q.property
  refine ⟨p,hp',E,P,R,hp2,ho,hEA,hE,hER'.trans hRPG,hRinf,?_⟩
  change PG = (PG ⊓ centralizer (Z₀ : Set G)) ⊔ (PG ⊓ normalizer (L : Set G))
  apply le_antisymm _ (sup_le inf_le_left inf_le_left)
  have he := congrArg (map C.subtype) heP
  rw [Subgroup.map_sup,map_inf _ _ _ C.subtype_injective,
    show K'.map C.subtype = K from map_subgroupOf_eq_of_le inf_le_left] at he
  change PG = PG ⊓ K ⊔ ((Q : Subgroup J').map J'.subtype).map C.subtype at he
  exact he.le.trans (sup_le (le_sup_of_le_left (inf_le_inf_left _ inf_le_right))
    (le_sup_of_le_right (le_inf hQPG (hQJ.trans hJM))))

/-- The literal quotient-action kernel is normal in the residual normalizer,
so every Sylow subgroup of that kernel gives the source Frattini product. -/
theorem residual_normalizer_kernel_sylow_factorization
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p ((normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
      (normalizer (residual H : Set G)).subtype)) :
    let N := normalizer (residual H : Set G)
    let C := (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map N.subtype
    N = C ⊔ (N ⊓ normalizer ((P : Subgroup C).map C.subtype : Set G)) := by
  let N := normalizer (residual H : Set G)
  let f := normalizerQuotientAction (residual H) (pCore 2 (residual H))
  let C := f.ker.map N.subtype
  have hCN : C ≤ N := map_subtype_le _
  have hNC : N ≤ normalizer (C : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      f.ker.le_normalizer_map N.subtype
  let C' := C.subgroupOf N
  let : C'.Normal := normal_subgroupOf_of_le_normalizer hNC
  let e : C ≃* C' := (subgroupOfEquivOfLe hCN).symm
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hm : ((Q : Subgroup C').map C'.subtype).map N.subtype =
      (P : Subgroup C).map C.subtype := by
    change (((P : Subgroup C).map e.toMonoidHom).map C'.subtype).map N.subtype = _
    rw [map_map,map_map]
    rfl
  have hn := ((Q : Subgroup C').map C'.subtype).le_normalizer_map N.subtype
  rw [hm] at hn
  have hf := congrArg (map N.subtype) Q.normalizer_sup_eq_top
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hCN,←MonoidHom.range_eq_map,range_subtype] at hf
  apply le_antisymm _ (sup_le hCN inf_le_left)
  exact hf.ge.trans (sup_le (le_sup_of_le_right (le_inf (map_subtype_le _) hn)) le_sup_left)

omit [Finite G] in
/-- A primitive prime exceeds the field degree, so every such prime-group
in N_G(L) acts by inner automorphisms on the literal L/O₂(L). -/
theorem primitive_prime_actor_inner_on_left
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hn : 1 < n) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (ho : orderOf (2 : ZMod p) = n)
    (P : Subgroup G) (hP : IsPGroup p P)
    (hPN : P ≤ normalizer (L : Set G)) (x : P) :
    normalizerQuotientAction L (pCore 2 L) (inclusion hPN x) ∈
      MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp he
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left (Fact.out : p.Prime).ne_one)
  have hnp : n < p := by
    have hd := ZMod.orderOf_dvd_card_sub_one h2
    rw [ho] at hd
    have hh := Nat.le_of_dvd (show 0 < p-1 by have := (Fact.out : p.Prime).two_le; omega) hd
    omega
  have hpn : ¬ p ∣ n := fun hd => (Nat.le_of_dvd (by omega) hd).not_gt hnp
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let α := (MulAut.congr e).toMonoidHom.comp
    ((normalizerQuotientAction L (pCore 2 L)).comp (inclusion hPN))
  let f := (Theory.PSL2.fieldProjection F).comp α
  have hpr : IsPGroup p f.range := hP.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hz : f.range = ⊥ := by
    rcases hpr.card_eq_or_dvd with hc | hd
    · exact f.range.eq_bot_of_card_eq hc
    · exfalso
      apply hpn
      have hh := hd.trans (card_subgroup_dvd_card f.range)
      rwa [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hF] at hh
  have hx : f x = 1 := by
    have hm : f x ∈ f.range := ⟨x,rfl⟩
    simpa only [hz,mem_bot] using hm
  have hi : α x ∈ MulAut.innerSubgroup PSL(2,F) := by
    change α x ∈ Theory.PSL2.inner F
    rw [←Theory.PSL2.fieldProjection_ker]
    exact hx
  rw [←MulAut.map_innerSubgroup_congr e] at hi
  obtain ⟨a,ha,he⟩ := hi
  exact (MulAut.congr e).injective he ▸ ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
