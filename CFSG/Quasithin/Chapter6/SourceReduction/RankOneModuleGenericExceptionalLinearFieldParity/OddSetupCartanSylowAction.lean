module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupSylowFactorization
public import Theory.GroupTheory.SylowInnerAction
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# The Cartan factor of the local primitive-prime actor

For an odd prime dividing 2ⁿ−1, the original split Cartan has prime-to-p
index in L. Its Sylow therefore maps to a Sylow of the inner automorphism
group of L/O₂(L). A primitive-prime subgroup of N_G(L) containing this
Cartan Sylow acts through exactly that Sylow, since its field action is
trivial. It is the product of the Cartan Sylow and its literal kernel on
L/O₂(L); these factors are disjoint and commute.

Apply this to the already selected Sylow of the entire residual
quotient-centralizer C_K. Its source factorization now has three factors:
the centralizer of Z₀, the original Cartan Sylow, and its intersection
with C_G(L/O₂(L)). The last subgroup still needs to preserve the actual
point Z₁. Centralization of the Cartan or triviality on L/O₂(L) does not
supply that statement. Residual/global TI and final parity remain with
qt-d-1222-linear-field-parity. The independent Suzuki source remains the
explicit solvability premise for the literal C_K action kernel.

Source: Aschbacher–Smith, proof of 5.1.17, printed p.640
(refs/quasithin.pdf). This is the quotient-action part of the source local
Sylow calculation, before replacing its kernel by the centralizer of Z₁.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H A B : Subgroup G} {n : ℕ}

theorem cartan_index_in_left
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    (A.subgroupOf L).index = Nat.card (pCore 2 L) * 2^n * (2^n+1) := by
  have hA := (c.left_cyclic_and_card hTL hpsl).2
  have hAL : A ≤ L := c.left_le.trans inf_le_left
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let e' := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  have hq : 1 < 2^n := by rw [←hF]; exact Finite.one_lt_card
  have he := (A.subgroupOf L).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv,hA,
    (pCore 2 L).card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr e'.toEquiv,Atlas.card_sl_two,hF] at he
  have hfactor : (2^n)^2-1 = (2^n-1)*(2^n+1) := by
    have hq' : 1 ≤ 2^n := by omega
    nlinarith [Nat.sub_add_cancel hq',Nat.sub_add_cancel (show 1 ≤ (2^n)^2 by nlinarith)]
  rw [hfactor] at he
  apply Nat.mul_right_cancel (show 0 < 2^n-1 by omega)
  calc
    (A.subgroupOf L).index * (2^n-1) = 2^n * ((2^n-1)*(2^n+1)) * Nat.card (pCore 2 L) := he
    _ = _ := by ring

theorem cartan_index_prime_free
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ 2^n-1) :
    ¬ p ∣ (A.subgroupOf L).index := by
  have hp2' : ¬ p ∣ 2 := by
    intro hh
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hh |>.resolve_left hp.ne_one)
  have hq : 1 ≤ 2^n := Nat.one_le_pow _ _ (by decide)
  have hplus : ¬ p ∣ 2^n+1 := by
    intro hh
    have ht := Nat.dvd_sub hh hd
    have he : 2^n+1-(2^n-1) = 2 := by omega
    exact hp2' (he ▸ ht)
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
  rw [cartan_index_in_left c hTL hpsl,hk]
  exact hp.not_dvd_mul (hp.not_dvd_mul
    (fun h => hp2' (hp.dvd_of_dvd_pow h)) (fun h => hp2' (hp.dvd_of_dvd_pow h))) hplus

/-- Every Sylow subgroup of the split Cartan at an odd split prime is Sylow in L. -/
theorem cartan_sylow_in_left
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hd : p ∣ 2^n-1)
    (R : Sylow p A) :
    ∃ S : Sylow p L, (S : Subgroup L).map L.subtype = (R : Subgroup A).map A.subtype := by
  let hAL : A ≤ L := c.left_le.trans inf_le_left
  let e := (subgroupOfEquivOfLe hAL).symm
  let R' := R.mapSurjective (f := e.toMonoidHom) e.surjective
  let Q := (R' : Subgroup (A.subgroupOf L)).map (A.subgroupOf L).subtype
  have hidx : ¬ p ∣ Q.index := by
    rw [index_map_subtype]
    exact (Fact.out : p.Prime).not_dvd_mul R'.not_dvd_index
      (cartan_index_prime_free c hTL hpsl Fact.out hp2 hd)
  refine ⟨(R'.isPGroup'.map _).toSylow hidx,?_⟩
  change (((R : Subgroup A).map e.toMonoidHom).map (A.subgroupOf L).subtype).map L.subtype = _
  rw [map_map,map_map]
  rfl


omit [Finite G] in
private theorem left_quotient_center_eq_bot
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    center (L ⧸ pCore 2 L) = ⊥ := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  apply (center _).eq_bot_iff_forall.mpr
  intro x hx
  apply e.injective
  rw [map_one]
  have hx' : e x ∈ center PSL(2,F) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx y)
  simpa only [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot,mem_bot] using hx'

omit [Finite G] in
private theorem quotientAction_on_left (l : L) :
    normalizerQuotientAction L (pCore 2 L) (inclusion L.le_normalizer l) =
      MulAut.conj (QuotientGroup.mk' (pCore 2 L) l) := by
  ext y
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) y
  simp only [normalizerQuotientAction,MonoidHom.comp_apply,quotientAut_apply_mk]
  change QuotientGroup.mk' (pCore 2 L) (l*y*l⁻¹) = _
  simp only [map_mul,map_inv,MulAut.conj_apply]

/-- An inner primitive-prime actor containing the Cartan Sylow has the same
quotient action as an element of that exact Cartan Sylow. -/
theorem primitive_prime_actor_cartan_representative
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hn : 1 < n) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (ho : orderOf (2 : ZMod p) = n)
    (P : Subgroup G) (hP : IsPGroup p P)
    (hPN : P ≤ normalizer (L : Set G)) (R : Sylow p A)
    (hRP : (R : Subgroup A).map A.subtype ≤ P) (x : P) :
    ∃ a : A, a ∈ R ∧
      normalizerQuotientAction L (pCore 2 L) (inclusion hPN x) =
        normalizerQuotientAction L (pCore 2 L)
          (inclusion ((c.left_le.trans inf_le_left).trans L.le_normalizer) a) := by
  have hd : p ∣ 2^n-1 := by
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by decide)),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
    rw [←ho,pow_orderOf_eq_one,sub_self]
  obtain ⟨S,hS⟩ := cartan_sylow_in_left c hTL hpsl hp2 hd R
  let q := QuotientGroup.mk' (pCore 2 L)
  let Q := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  let α := (normalizerQuotientAction L (pCore 2 L)).comp (inclusion hPN)
  have hα : IsPGroup p α.range := hP.of_surjective α.rangeRestrict α.rangeRestrict_surjective
  have hQα : (Q : Subgroup (L ⧸ pCore 2 L)).map MulAut.conj ≤ α.range := by
    rintro _ ⟨z,⟨l,hl,rfl⟩,rfl⟩
    have hlR : (l : G) ∈ (R : Subgroup A).map A.subtype :=
      hS ▸ mem_map_of_mem L.subtype hl
    let y : P := ⟨l,hRP hlR⟩
    refine ⟨y,?_⟩
    exact quotientAction_on_left l
  obtain ⟨b,hb⟩ := primitive_prime_actor_inner_on_left hpsl hn hp2 ho P hP hPN x
  have hbQ : b ∈ Q := MulAut.inner_mem_image_sylow
    (left_quotient_center_eq_bot hpsl) Q α.range hα hQα
      (hb.symm ▸ (show α x ∈ α.range from ⟨x,rfl⟩))
  obtain ⟨l,hl,hlb⟩ := hbQ
  have hlR : (l : G) ∈ (R : Subgroup A).map A.subtype :=
    hS ▸ mem_map_of_mem L.subtype hl
  obtain ⟨a,ha,he⟩ := hlR
  refine ⟨a,ha,?_⟩
  rw [←hb,←hlb,←quotientAction_on_left l]
  congr 1
  exact Subtype.ext he.symm

/-- The local p-group is the product of its Cartan Sylow and its literal
kernel on L/O₂(L). This does not replace that kernel by C_P(Z₁). -/
theorem primitive_prime_actor_cartan_kernel_factorization
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hn : 1 < n) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (ho : orderOf (2 : ZMod p) = n)
    (P : Subgroup G) (hP : IsPGroup p P)
    (hPN : P ≤ normalizer (L : Set G)) (R : Sylow p A)
    (hRP : (R : Subgroup A).map A.subtype ≤ P) :
    P = (R : Subgroup A).map A.subtype ⊔
      (P ⊓ (normalizerQuotientAction L (pCore 2 L)).ker.map
        (normalizer (L : Set G)).subtype) := by
  let N := normalizer (L : Set G)
  let f := normalizerQuotientAction L (pCore 2 L)
  let C := f.ker.map N.subtype
  apply le_antisymm _ (sup_le hRP inf_le_left)
  intro x hx
  obtain ⟨a,ha,he⟩ := primitive_prime_actor_cartan_representative
    c hTL hpsl hn hp2 ho P hP hPN R hRP ⟨x,hx⟩
  have haP : (a : G) ∈ P := hRP (mem_map_of_mem A.subtype ha)
  let y : N := inclusion hPN ⟨x,hx⟩
  let a' : N := inclusion ((c.left_le.trans inf_le_left).trans L.le_normalizer) a
  have hk : a'⁻¹*y ∈ f.ker := by
    change f (a'⁻¹*y) = 1
    rw [map_mul,map_inv]
    change (f a')⁻¹*f y = 1
    change f y = f a' at he
    rw [he,inv_mul_cancel]
  have hc : (a : G)⁻¹*x ∈ C := mem_map_of_mem N.subtype hk
  have hmem := ((R : Subgroup A).map A.subtype ⊔ (P ⊓ C)).mul_mem
    (mem_sup_left (mem_map_of_mem A.subtype ha))
    (mem_sup_right (show (a : G)⁻¹*x ∈ P ⊓ C from ⟨P.mul_mem (P.inv_mem haP) hx,hc⟩))
  change (a : G)*((a : G)⁻¹*x) ∈ (R : Subgroup A).map A.subtype ⊔ (P ⊓ C) at hmem
  simpa only [mul_inv_cancel_left] using hmem


/-- The Cartan Sylow is exactly the local actor's intersection with L;
relative normality of L therefore makes it normal in that actor. -/
theorem split_prime_actor_intersection_left
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hd : p ∣ 2^n-1)
    (P : Subgroup G) (hP : IsPGroup p P)
    (hPN : P ≤ normalizer (L : Set G)) (R : Sylow p A)
    (hRP : (R : Subgroup A).map A.subtype ≤ P) :
    P ⊓ L = (R : Subgroup A).map A.subtype ∧
      P ≤ normalizer ((R : Subgroup A).map A.subtype : Set G) := by
  obtain ⟨S,hS⟩ := cartan_sylow_in_left c hTL hpsl hp2 hd R
  have hSL : (S : Subgroup L) ≤ P.subgroupOf L := by
    intro l hl
    exact hRP (hS ▸ mem_map_of_mem L.subtype hl)
  have he : P.subgroupOf L = (S : Subgroup L) := S.is_maximal' hP.comap_subtype hSL
  have heG : P ⊓ L = (R : Subgroup A).map A.subtype := by
    rw [←subgroupOf_map_subtype,he,hS]
  refine ⟨heG,?_⟩
  rw [←heG]
  exact (le_inf P.le_normalizer hPN).trans inf_normalizer_le_normalizer_inf

/-- The split Cartan has no kernel on the actual two-core quotient. -/
theorem cartan_disjoint_left_quotient_kernel
    (c : CartanPair T L H A B)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    Disjoint A ((normalizerQuotientAction L (pCore 2 L)).ker.map
      (normalizer (L : Set G)).subtype) := by
  have hAL : A ≤ L := c.left_le.trans inf_le_left
  have ho : Odd (Nat.card A) := by
    have hh := OddHall.odd_hall_odd c.left_hall
    rwa [Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv] at hh
  have hdis : Disjoint A (L.pCoreIn 2) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨k,hk⟩ := (isPGroup_pCoreIn 2 L).exists_card_eq
    rw [hk]
    exact ho.coprime_two_right.pow_right k
  apply disjoint_iff.mpr
  apply _root_.eq_bot_iff.mpr
  rintro x ⟨hxA,y,hy,he⟩
  let l : L := ⟨x,hAL hxA⟩
  have hy' : y = inclusion L.le_normalizer l := Subtype.ext he
  have hconj : MulAut.conj (QuotientGroup.mk' (pCore 2 L) l) = 1 := by
    rw [←quotientAction_on_left l]
    exact hy' ▸ hy
  have hq : QuotientGroup.mk' (pCore 2 L) l = 1 :=
    MulAut.conj_injective_of_center_eq_bot (left_quotient_center_eq_bot hpsl)
      (hconj.trans MulAut.conj.map_one.symm)
  have hl : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp hq
  exact hdis.le_bot ⟨hxA,mem_map_of_mem L.subtype hl⟩

/-- The quotient kernel commutes with the Cartan Sylow in the local p-group.
Both normality assertions are relative to the original actor. -/
theorem split_prime_actor_kernel_centralizes_cartan
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hd : p ∣ 2^n-1)
    (P : Subgroup G) (hP : IsPGroup p P)
    (hPN : P ≤ normalizer (L : Set G)) (R : Sylow p A)
    (hRP : (R : Subgroup A).map A.subtype ≤ P) :
    P ⊓ (normalizerQuotientAction L (pCore 2 L)).ker.map
      (normalizer (L : Set G)).subtype ≤
        centralizer ((R : Subgroup A).map A.subtype : Set G) := by
  let N := normalizer (L : Set G)
  let f := normalizerQuotientAction L (pCore 2 L)
  let C := f.ker.map N.subtype
  let E := (R : Subgroup A).map A.subtype
  have hnE := (split_prime_actor_intersection_left c hTL hpsl hp2 hd P hP hPN R hRP).2
  have hnC : N ≤ normalizer (C : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      f.ker.le_normalizer_map N.subtype
  have hcomm : ⁅P ⊓ C,E⁆ ≤ C ⊓ E := le_inf
    ((commutator_mono inf_le_right le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hRP.trans (hPN.trans hnC))))
    (le_normalizer_iff_commutator_le_right.mp (inf_le_left.trans hnE))
  have hdEC : Disjoint E C := (cartan_disjoint_left_quotient_kernel c hpsl).mono_left
    (map_subtype_le _)
  exact commutator_eq_bot_iff_le_centralizer.mp
    (bot_unique (hcomm.trans hdEC.symm.le_bot))

/-- The selected full-kernel Sylow splits into the source omega-orbit
centralizer, its literal Cartan intersection, and the remaining left
quotient-action kernel. The local actor centralizes the Cartan factor. -/
theorem residual_kernel_sylow_local_factors
    {W : Subgroup G}
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
    let Cₗ := (normalizerQuotientAction L (pCore 2 L)).ker.map
      (normalizer (L : Set G)).subtype
    ∃ (p : ℕ) (_hp : Fact p.Prime) (E : Subgroup G) (P : Sylow p C) (R : Sylow p A),
      p ≠ 2 ∧ orderOf (2 : ZMod p) = n ∧ E ≤ A ∧ Nat.card E = p ∧
      E ≤ (P : Subgroup C).map C.subtype ∧
      (R : Subgroup A).map A.subtype = (P : Subgroup C).map C.subtype ⊓ A ∧
      (P : Subgroup C).map C.subtype ⊓ normalizer (L : Set G) =
        (R : Subgroup A).map A.subtype ⊔ ((P : Subgroup C).map C.subtype ⊓ Cₗ) ∧
      Disjoint ((R : Subgroup A).map A.subtype) ((P : Subgroup C).map C.subtype ⊓ Cₗ) ∧
      (P : Subgroup C).map C.subtype ⊓ normalizer (L : Set G) ≤
        centralizer ((R : Subgroup A).map A.subtype : Set G) ∧
      (P : Subgroup C).map C.subtype =
        ((P : Subgroup C).map C.subtype ⊓ centralizer (Z₀ : Set G)) ⊔
          (R : Subgroup A).map A.subtype ⊔ ((P : Subgroup C).map C.subtype ⊓ Cₗ) := by
  obtain ⟨p,hp,E,P,R,hp2,ho,hEA,hE,hEP,hR,hP⟩ :=
    residual_kernel_primitive_sylow_factorization h hH hK hnf hm hsolv c hodd
  let C := (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
    (normalizer (residual H : Set G)).subtype
  let Cₗ := (normalizerQuotientAction L (pCore 2 L)).ker.map
    (normalizer (L : Set G)).subtype
  let PG := (P : Subgroup C).map C.subtype
  let Q := PG ⊓ normalizer (L : Set G)
  let RA := (R : Subgroup A).map A.subtype
  have hQ : IsPGroup p Q := (P.isPGroup'.map C.subtype).of_injective
    (inclusion inf_le_left) (inclusion_injective inf_le_left)
  have hRQ : RA ≤ Q := le_inf (hR.le.trans inf_le_left)
    ((map_subtype_le _).trans ((c.left_le.trans inf_le_left).trans L.le_normalizer))
  have hQC : Q ⊓ Cₗ = PG ⊓ Cₗ := by
    change (PG ⊓ normalizer (L : Set G)) ⊓ Cₗ = _
    rw [inf_assoc,inf_eq_right.mpr (map_subtype_le _)]
  have hfactor := primitive_prime_actor_cartan_kernel_factorization
    c h.sylow_normalizes h.linear h.exponent hp2 ho Q hQ inf_le_right R hRQ
  change Q = RA ⊔ (Q ⊓ Cₗ) at hfactor
  rw [hQC] at hfactor
  have hdis : Disjoint RA (PG ⊓ Cₗ) :=
    (cartan_disjoint_left_quotient_kernel c h.linear).mono
      (map_subtype_le _) inf_le_right
  have hd : p ∣ 2^n-1 := by
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by decide)),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
    rw [←ho,pow_orderOf_eq_one,sub_self]
  have hcent := split_prime_actor_kernel_centralizes_cartan
    c h.sylow_normalizes h.linear hp2 hd Q hQ inf_le_right R hRQ
  change Q ⊓ Cₗ ≤ centralizer (RA : Set G) at hcent
  rw [hQC] at hcent
  let : IsCyclic A := (c.left_cyclic_and_card h.sylow_normalizes h.linear).1
  have hRA : RA ≤ centralizer (RA : Set G) := (map_subtype_le _).trans
    ((le_centralizer A).trans (centralizer_le (map_subtype_le _)))
  have hQcent : Q ≤ centralizer (RA : Set G) := by
    rw [hfactor]
    exact sup_le hRA hcent
  refine ⟨p,hp,E,P,R,hp2,ho,hEA,hE,hEP,hR,hfactor,hdis,hQcent,?_⟩
  change PG = _ at hP ⊢
  change PG = (PG ⊓ centralizer _ ) ⊔ Q at hP
  simpa only [hfactor,←sup_assoc] using hP

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
