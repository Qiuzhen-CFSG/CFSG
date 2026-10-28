module
public import Theory.SpecificGroups.PSL2.SylowFixedQuotients
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.PairQuotient
public import Theory.SpecificGroups.PSL2.PrimeFourSolvableBound
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryTriality
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalCubic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowPrimeField
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowPrimeField

/-!
# Normal prime-field containers in the local Cartan escape

The original Cartan pair generates a solvable mixed subgroup containing the
full Sylow subgroup and both Hall factors. For a normal odd-prime PSL₂
container, its action on the literal two-core image contains an inner A₄.
Dickson's classification bounds the full odd action by order three, so the
original right Hall subgroup fills that image and forces normalization of
the residual, contradicting escape.

An initially moved seed would give two independent cubic directions in its
full orbit. Normality puts that orbit in the containing component, whereas
prime-field PSL₂ has three-rank at most one. Thus the argument also covers
the original moved-seed formulation, without assuming an escaping cubic.

The internal import of GlobalPrimeSylowPrimeField reuses its A₅ Sylow
normalizer marking inside the same Cartan proof family; its private boundary
is preserved. Source: Aschbacher--Smith 5.1.12--13, printed pp.635--637.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

private theorem a4_in_solvable
    (e : G ≃* alternatingGroup (Fin 5)) (P : Sylow 2 G)
    (J B : Subgroup G) [Group.IsSolvable J]
    (hPJ : (P : Subgroup G) ≤ J) (hBJ : B ≤ J) (hB : Nat.card B = 3) :
    ∃ a : alternatingGroup (Fin 4) →* G, Function.Injective a ∧ ∀ x, a x ∈ J := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hj : J.map e.toMonoidHom ≠ ⊤ := by
    intro he
    let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    have hs := Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective J)
    rw [he] at hs
    let := hs
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5))
      (Group.isSolvable_of_surjective
        (f := (topEquiv : (⊤ : Subgroup (alternatingGroup (Fin 5))) ≃* _).toMonoidHom) topEquiv.surjective)
  have hJN : J ≤ normalizer (P : Set G) := by
    have hh := Theory.SpecificGroups.Alternating.FiveSylowMaximal.overgroup_le_sylow_normalizer
      Q (J.map e.toMonoidHom) (map_mono hPJ) hj
    change J.map e.toMonoidHom ≤ normalizer ((P : Subgroup G).map e.toMonoidHom) at hh
    rw [←map_equiv_normalizer_eq (P : Subgroup G) e] at hh
    exact (map_le_map_iff_of_injective e.injective).mp hh
  have h12 : 12 ∣ Nat.card J := by
    apply (by decide : Nat.Coprime 4 3).mul_dvd_of_dvd_of_dvd
    · rw [←Theory.PSL2.SylowFixedQuotients.sylow_card_of_equiv_five e P]
      exact card_dvd_of_le hPJ
    · rw [←hB]
      exact card_dvd_of_le hBJ
  have hN : Nat.card (normalizer (P : Set G)) = 12 := by
    rw [←card_map_of_injective (f := e.toMonoidHom) e.injective]
    change Nat.card ((normalizer (P : Subgroup G)).map e.toMonoidHom) = 12
    rw [map_equiv_normalizer_eq]
    exact Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_card Q
  have he : J = normalizer (P : Set G) :=
    eq_of_le_of_card_ge hJN (by rw [hN]; exact Nat.le_of_dvd Nat.card_pos h12)
  obtain ⟨a⟩ := Prime.five_borel_marking e P
  exact ⟨(normalizer (P : Set G)).subtype.comp a.toMonoidHom,
    Subtype.val_injective.comp a.injective,fun x => he.symm ▸ (a x).property⟩

private theorem full_odd_normalizes_prime_section
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 3 < p) (hF : Nat.card F = p)
    (C R J E B : Subgroup G) [C.Normal] [Group.IsSolvable J]
    (eC : C ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (eR : R ≃* alternatingGroup (Fin 5)) (hRC : R ≤ C)
    (S : Sylow 2 G) (hSR : (S : Subgroup G) ≤ normalizer (R : Set G))
    (hSJ : (S : Subgroup G) ≤ J) (hEJ : E ≤ J)
    (hBE : B ≤ E) (hBR : B ≤ R) (hB : Nat.card B = 3)
    (hodd : Odd (Nat.card E)) : E ≤ normalizer (R : Set G) := by
  obtain ⟨P,hP⟩ := exists_sylow_component hSR
  let JR := J.subgroupOf R
  let BR := B.subgroupOf R
  let : Group.IsSolvable JR := Group.isSolvable_of_isSolvable_injective
    (f := R.subtype.subgroupComap J)
    (by
      intro x y hh
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : J => (z : G)) hh)
  have hPJR : (P : Subgroup R) ≤ JR := by
    intro x hx
    have hh : (x : G) ∈ (S : Subgroup G) ⊓ R := hP ▸ mem_map_of_mem R.subtype hx
    exact hSJ hh.1
  obtain ⟨a,ha,haj⟩ := a4_in_solvable eR P JR BR hPJR (comap_mono (hBE.trans hEJ))
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hBR).toEquiv]; exact hB)
  let f : G →* MulAut C := MulAut.conjNormal
  let b : alternatingGroup (Fin 4) →* C := (inclusion hRC).comp a
  let : Group.IsSolvable (J.map f) := Group.isSolvable_of_surjective (f.subgroupMap_surjective J)
  have hsmall : Nat.card (E.map f) ≤ 3 :=
    Theory.PSL2.PrimeFourSolvable.odd_aut_card_le_three ho hp hF eC (J.map f) (E.map f)
      (map_mono hEJ) (hodd.of_dvd_nat (card_map_dvd E f)) b
      ((inclusion_injective hRC).comp ha) (fun x => by
        have he : MulAut.conj (b x) = f (a x : G) := by ext y; rfl
        rw [he]
        exact mem_map_of_mem f (haj x))
  have hz := (Theory.PSL2.primeField_center_outer_of_equiv (Fact.out : p.Prime) ho hF eC).1
  have hfB : Function.Injective (f.comp B.subtype) := by
    intro x y hh
    have he (x : B) : f (x : G) = MulAut.conj (inclusion (hBR.trans hRC) x) := by ext z; rfl
    change f (x : G) = f (y : G) at hh
    rw [he x,he y] at hh
    exact (inclusion_injective (hBR.trans hRC)) (conj_injective_of_center_eq_bot hz hh)
  have hBc : Nat.card (B.map f) = 3 := by
    rw [←range_subtype B,←MonoidHom.range_comp]
    exact (Nat.card_congr (MonoidHom.ofInjective hfB).toEquiv).symm.trans hB
  have he : B.map f = E.map f := eq_of_le_of_card_ge (map_mono hBE) (by rw [hBc]; exact hsmall)
  intro x hx
  obtain ⟨b,hb,hbx⟩ := mem_map.mp (he.symm ▸ mem_map_of_mem f hx)
  have hker : x * b⁻¹ ∈ f.ker := by
    change f (x * b⁻¹) = 1
    rw [map_mul,map_inv,hbx,mul_inv_cancel]
  have hc : x * b⁻¹ ∈ centralizer (C : Set G) := by
    rw [←MulAut.conjNormal_ker_eq_centralizer]
    exact hker
  have hn := (centralizer_le hRC).trans (centralizer_le_normalizer (R : Set G)) hc
  simpa only [inv_mul_cancel_right] using
    (normalizer (R : Set G)).mul_mem hn (R.le_normalizer (hBR hb))

/-- The full original Cartan intersection excludes a normal odd-prime PSL₂
container of the original residual. No escaping cubic is assumed. -/
theorem not_prime_container_of_residual
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hCn : C.Normal)
    (hRC : residual H ≤ C.map Y.subtype) (hp : p.Prime) (ho : Odd p) :
    ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p := by
  intro hm
  have horbit : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
      (hH.1.1.2.trans (le_normalizer_residual H))) (le_componentOrbit _ _)
  have hA5 := (seed_quotient_A5_of_prime_container h.qtke (map_subtype_le _) hH.1.1.2
    hR horbit hY hescape C hC hRC hp ho hm).2
  have hBc := right_hall_card_three_of_residual_A5 h hH hgen c hA5
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hTY := hH.1.1.2.trans hY.2
  have hBY := (c.right_le.trans inf_le_right).trans hY.2
  let q := QuotientGroup.mk' (pCore 2 Y)
  let S := T.subtype hTY
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  let Rbar := ((residual H).subgroupOf Y).map q
  let Cbar := C.map q
  let Abar := (A.subgroupOf Y).map q
  let Bbar := (B.subgroupOf Y).map q
  have hl : (residual H).subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTY hRY).mp ⟨hRY,hR⟩
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  have hlq : Rbar ∈ ChapterA.Section03.localCComponents P :=
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hl
  have hlt := seed_image_lt_container h.qtke (map_subtype_le _) hH.1.1.2
    hR horbit hY hescape C hC hRC
  obtain ⟨hexc,⟨eR⟩⟩ := ChapterA.Section03.SourceEmbeddings.proper_primePSL2_models
    P hlq (hC.map_quotient _) hlt.le hlt.ne hp ho
      (hm.of_mulEquiv (cComponentTwoCoreQuotientEquiv hC).symm)
  have hp3 : 3 < p := by
    have := hp.two_le
    have := ho.not_two_dvd_nat
    have := hexc.2.2.1
    by_contra hh
    have he : p = 3 := by omega
    norm_num [he] at *
  have hBbar : Nat.card Bbar = 3 := by
    have hd : Nat.card Bbar ∣ 3 := by
      have hd := card_map_dvd (B.subgroupOf Y) q
      rwa [Nat.card_congr (subgroupOfEquivOfLe hBY).toEquiv,hBc] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with hb | hb
    · have hz : Bbar = ⊥ := eq_bot_of_card_eq _ hb
      have hle : B.subgroupOf Y ≤ pCore 2 Y := by
        simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
      obtain ⟨k,hk⟩ := (pCore_isPGroup.to_le hle).exists_card_eq
      rw [Nat.card_congr (subgroupOfEquivOfLe hBY).toEquiv,hBc] at hk
      have hh : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow (by rw [←hk])
      norm_num at hh
    · exact hb
  have hBA : Bbar ≤ normalizer (Abar : Set (Y ⧸ pCore 2 Y)) := by
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    intro b hb
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (c.right_normalizes_left hb) (a : G)
  have hoddA : Odd (Nat.card Abar) := by
    have hoA : Odd (Nat.card A) := by
      rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
      exact OddHall.odd_hall_odd c.left_hall
    have hoAY : Odd (Nat.card (A.subgroupOf Y)) := by
      rw [←inf_subgroupOf_right A Y,Nat.card_congr
        (subgroupOfEquivOfLe (show A ⊓ Y ≤ Y from inf_le_right)).toEquiv]
      exact hoA.of_dvd_nat (card_dvd_of_le (show A ⊓ Y ≤ A from inf_le_left))
    exact hoAY.of_dvd_nat (card_map_dvd _ q)
  let E := Abar ⊔ Bbar
  have hoddE : Odd (Nat.card E) := by
    have hh := hoddA.mul (show Odd (Nat.card Bbar) by rw [hBbar]; decide)
    rw [card_mul_eq_card_inf_mul_card_sup_of_normalizes Abar Bbar hBA] at hh
    exact hh.of_dvd_nat (dvd_mul_left _ _)
  have hLH : ¬ L ≤ H := by
    intro hh
    exact hescape (inf_le_left.trans ((c.left_le.trans (inf_le_left.trans hh)).trans
      (le_normalizer_residual H)))
  have prep := cartanPreparation_of_not_le h hH hgen hLH
  let M := normalizer (L : Set G) ⊓ H
  let V := localBorel T L ⊔ M
  let : Group.IsSolvable (localBorel T L) := prep.borel_solvable
  let : Group.IsSolvable M := prep.intersection_solvable
  let : Group.IsSolvable V := Group.isSolvable_sup_of_normalizes _ _ prep.intersection_normalizes
  let JY := (A.subgroupOf Y ⊔ (T : Subgroup G).subgroupOf Y) ⊔ B.subgroupOf Y
  have hJV : JY.map Y.subtype ≤ V := by
    rw [Subgroup.map_sup,Subgroup.map_sup,subgroupOf_map_subtype,map_subgroupOf_eq_of_le hTY,
      map_subgroupOf_eq_of_le hBY]
    exact sup_le (sup_le ((inf_le_left.trans c.left_le).trans le_sup_left)
      ((le_inf h.sylow_normalizes hH.1.1.2).trans le_sup_right))
      (c.right_le.trans le_sup_right)
  let : Group.IsSolvable JY := Group.isSolvable_of_isSolvable_injective
    (f := (inclusion hJV).comp
      (JY.equivMapOfInjective Y.subtype Y.subtype_injective).toMonoidHom)
    ((inclusion_injective hJV).comp (JY.equivMapOfInjective Y.subtype Y.subtype_injective).injective)
  let J := JY.map q
  let : Group.IsSolvable J := Group.isSolvable_of_surjective (q.subgroupMap_surjective JY)
  let := hCn
  let : Cbar.Normal := Subgroup.Normal.map hCn q (QuotientGroup.mk'_surjective _)
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  have hPR : (P : Subgroup (Y ⧸ pCore 2 Y)) ≤ normalizer (Rbar : Set _) := by
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq hRY]
    exact comap_mono (hH.1.1.2.trans (le_normalizer_residual H))
  have hnorm := full_odd_normalizes_prime_section ho hp3 hF Cbar Rbar J E Bbar
    ((cComponentTwoCoreQuotientEquiv hC).symm.trans e) eR hlt.le P hPR
    (map_mono (show (T : Subgroup G).subgroupOf Y ≤ JY from le_sup_right.trans le_sup_left))
    (sup_le (map_mono (le_sup_left.trans le_sup_left)) (map_mono le_sup_right))
    le_sup_right (map_mono (comap_mono (Global.right_cartan_le_residual c))) hBbar hoddE
  exact hescape ((residual_escape_twoCore_iff h.qtke h.sylow_normalizes hH hgen hY.2).mp
    (le_sup_left.trans hnorm))


/-- In a normal odd-prime PSL₂ container the seed cannot be moved: its
full orbit would contribute two independent cubic directions. -/
theorem seed_eq_residual_of_normal_prime_container
    {T : Sylow 2 G} {K H A Y : Subgroup G} {p : ℕ}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hK : (K.subgroupOf H).IsCComponent)
    (hKT : K ⊔ (T : Subgroup G) = H)
    (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hHH : H ∈ Chapter1.H G) (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hCn : C.Normal) (hKC : K ≤ C.map Y.subtype)
    (hp : p.Prime) (_ho : Odd p) (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) :
    K = residual H := by
  by_contra hne
  have hlin := moved_seed_linear_four_of_escape hG hKL hKT horbit hne hY hescape
  obtain ⟨epair⟩ := moved_seed_residual_quotient hG hKH hTH hHH hK horbit hne hlin
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : Fact p.Prime := ⟨hp⟩
  have hpos : 1 ≤ primeRank 3 (alternatingGroup (Fin 5)) := by
    have hn : primeRank 3 (alternatingGroup (Fin 5)) ≠ 0 := by
      intro hz
      have hh := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
      apply hh
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    omega
  let er := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  have hlow : 2 ≤ primeRank 3 (residual H) := by
    rw [←primeRank_equiv 3 er,
      ←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 (pResidual 2 H)) pCore_isPGroup,
      primeRank_equiv 3 epair,primeRank_prod_eq_add]
    omega
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,hF,ZMod.card])
  have hu : primeRank 3 C ≤ 1 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 C) pCore_isPGroup,
      primeRank_equiv 3 (e.trans (GorensteinWalter.psl2RingEquiv eF))]
    exact Theory.PSL2.primeField_odd_rank (by decide)
  have hYn : Y ≤ normalizer (C.map Y.subtype : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le C)).mp
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hCn
  have hRX : residual H ≤ C.map Y.subtype := by
    rw [←horbit]
    exact iSup_conjugates_le_of_le_normalizer _ _ _ hKC (hTH.trans (hY.2.trans hYn))
  have hh := primeRank_mono 3 hRX
  rw [←primeRank_equiv 3 (C.equivMapOfInjective Y.subtype Y.subtype_injective)] at hh
  omega

/-- The full original escape excludes every normal odd-prime PSL₂ container,
including the initially moved-seed branch. -/
theorem not_normal_prime_container
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKT : K ⊔ (T : Subgroup G) = H) (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hCn : C.Normal)
    (hKC : K ≤ C.map Y.subtype) (hp : p.Prime) (ho : Odd p) :
    ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p := by
  intro hm
  have he := seed_eq_residual_of_normal_prime_container h.qtke hKH hH.1.1.2 hK hKT hKL
    horbit hH.1.1.1 hY hescape C hCn hKC hp ho hm
  subst K
  exact not_prime_container_of_residual h hH hgen c hY hescape hKL C hC hCn hKC hp ho hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The original seed and full containing orbit retain all preceding exclusions;
the normal odd-prime linear rows are now excluded without a cubic premise. -/
theorem localCartan_escape_seed_prime_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8) ∧
        (C.Normal → ∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank⟩ :=
    localCartan_escape_seed_rankTwo_reduction h hH hgen c hY hescape
  exact ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,
    fun hCn _ hp ho => LocalSieve.not_normal_prime_container h hH hgen c hKH hK hKT hKL hR
      hY hescape C hC hCn hKC hp ho⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
