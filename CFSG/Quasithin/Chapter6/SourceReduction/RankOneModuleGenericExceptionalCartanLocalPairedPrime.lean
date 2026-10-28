module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalTwentyFive
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalPaired
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalPrime

/-!
# Paired odd-prime containers in the original local Cartan escape

The moved source seed and its Sylow conjugate give the two actual A₅
images in Y/O₂(Y). The prescribed right Hall subgroup is E₉. Its order
first prevents the two images from coinciding; local component calculus
then makes their product an internal A₅ × A₅. Counting in that product
shows that the Hall plane meets each factor in a cubic subgroup.

An odd subgroup fixes each containing component because its normalizer
has index two. Restrict the original solvable mixed join to this
normalizer. Its intersection with the A₅ factor contains the full Sylow
four-group and the actual Hall cubic, and hence an A₄. The prime-field
solvable-automorphism bound makes the entire odd action have order at most
three; the Hall cubic fills it. Applying this to both factors normalizes
the whole residual image. The original two-core normalizer lift then
contradicts escape.

Together with the previously proved normal case, this excludes every
odd-prime PSL₂ container without a degree-two or escaping-cubic premise.
The Chapter 12 application retains the original module, Sylow, both Hall
conditions, quotient maps and whole containing orbit. A nonnormal
container can now only have the genuine J₁ quotient. Binary triality,
the other remaining containing rows and the placed inverted cubic remain
with the local sieve assembly.

The internal import reuses the checked A₅ Sylow-normalizer marking from
the normal-prime proof without changing that module's public boundary.
Source: Aschbacher--Smith 5.1.12--13, printed pp.635--637, especially the
A₄ wreath-product argument on p.636 (`refs/quasithin.pdf`).
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

private theorem normal_odd_prime_section
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 3 < p) (hF : Nat.card F = p)
    (C R J E B : Subgroup G) [C.Normal] [Group.IsSolvable J]
    (eC : C ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (eR : R ≃* alternatingGroup (Fin 5)) (hRC : R ≤ C)
    (P : Sylow 2 R) (hPJ : (P : Subgroup R).map R.subtype ≤ J) (hEJ : E ≤ J)
    (hBE : B ≤ E) (hBR : B ≤ R) (hB : Nat.card B = 3)
    (hodd : Odd (Nat.card E)) : E ≤ normalizer (R : Set G) := by
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
    exact hPJ (mem_map_of_mem R.subtype hx)
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


omit [Finite G] in
private theorem odd_le_index_two (E N : Subgroup G)
    (ho : Odd (Nat.card E)) (hi : N.index = 2) : E ≤ N := by
  let : N.Normal := N.normal_of_index_eq_two hi
  rw [←relIndex_eq_one]
  apply Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr ho)
  · simpa only [hi] using N.relIndex_dvd_index_of_normal E
  · exact N.relIndex_dvd_card E

private theorem odd_prime_section
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 3 < p) (hF : Nat.card F = p)
    (C R J E B : Subgroup G) [Group.IsSolvable J]
    (eC : C ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (eR : R ≃* alternatingGroup (Fin 5)) (hRC : R ≤ C)
    (P : Sylow 2 R) (hPJ : (P : Subgroup R).map R.subtype ≤ J)
    (hEJ : E ≤ J) (hEN : E ≤ normalizer (C : Set G))
    (hBE : B ≤ E) (hBR : B ≤ R) (hB : Nat.card B = 3)
    (hodd : Odd (Nat.card E)) : E ≤ normalizer (R : Set G) := by
  let N := normalizer (C : Set G)
  have hRN : R ≤ N := hRC.trans C.le_normalizer
  let a := (subgroupOfEquivOfLe hRN).symm
  let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
  let : (C.subgroupOf N).Normal := C.normal_in_normalizer
  let : Group.IsSolvable (J.subgroupOf N) :=
    Group.isSolvable_of_isSolvable_injective
      (f := N.subtype.subgroupComap J) (by
        intro x y he
        exact Subtype.ext (Subtype.ext (congrArg (fun z : J => (z : G)) he)))
  have hQJ : (Q : Subgroup (R.subgroupOf N)).map (R.subgroupOf N).subtype ≤
      J.subgroupOf N := by
    rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    exact hPJ (mem_map_of_mem R.subtype hx)
  have hn := normal_odd_prime_section ho hp hF
    (C.subgroupOf N) (R.subgroupOf N) (J.subgroupOf N) (E.subgroupOf N) (B.subgroupOf N)
    ((subgroupOfEquivOfLe C.le_normalizer).trans eC)
    ((subgroupOfEquivOfLe hRN).trans eR) (comap_mono hRC) Q hQJ
    (comap_mono hEJ) (comap_mono hBE) (comap_mono hBR)
    (by rw [Nat.card_congr (subgroupOfEquivOfLe (hBE.trans hEN)).toEquiv]; exact hB)
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv]; exact hodd)
  rw [←subgroupOf_normalizer_eq hRN] at hn
  intro x hx
  exact hn (show (⟨x,hEN hx⟩ : N) ∈ E.subgroupOf N from hx)

private theorem pair_cubic_intersection (R U B : Subgroup G)
    (hR : Nat.card R = 60) (hU : Nat.card U = 60)
    (hcomm : ⁅R,U⁆ = ⊥) (hdis : Disjoint R U)
    (hB : Nat.card B = 9) (hBP : B ≤ R ⊔ U) : Nat.card (R ⊓ B : Subgroup G) = 3 := by
  have hn : R ⊔ U ≤ normalizer (R : Set G) :=
    sup_le R.le_normalizer ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hP : Nat.card (R ⊔ U : Subgroup G) = 3600 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint R U
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans (Subgroup.centralizer_le_normalizer _)) hdis,
      hR,hU]
  have hd := Nat.dvd_gcd (card_dvd_of_le (show R ⊓ B ≤ R from inf_le_left))
    (card_dvd_of_le (show R ⊓ B ≤ B from inf_le_right))
  rw [hR,hB] at hd
  rw [show Nat.gcd 60 9 = 3 from rfl] at hd
  change Nat.card (R ⊓ B : Subgroup G) ∣ 3 at hd
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with hh | hh
  · have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes R B (hBP.trans hn)
    rw [hR,hB,hh,one_mul] at hc
    have hle : R ⊔ B ≤ R ⊔ U := sup_le le_sup_left hBP
    have hd := card_dvd_of_le hle
    rw [hP,←hc] at hd
    norm_num at hd
  · exact hh

omit [Finite G] in
private theorem local_simple_pair (S : Sylow 2 G) (R : Subgroup G)
    (hr : R ∈ ChapterA.Section03.localCComponents S)
    (e : R ≃* alternatingGroup (Fin 5)) (t : G) (ht : t ∈ S)
    (hne : R ≠ R.conjBy t) :
    ⁅R,R.conjBy t⁆ = ⊥ ∧ Disjoint R (R.conjBy t) := by
  let H := R ⊔ (S : Subgroup G)
  let A := R.subgroupOf H
  let a := (subgroupOfEquivOfLe (show R ≤ H from le_sup_left)).trans e
  let s : H := ⟨t,mem_sup_right ht⟩
  let : IsSimpleGroup A := a.isSimpleGroup
  let : Group.IsPerfect A := hr.perfect
  let : IsSimpleGroup (A.conjBy s) :=
    (A.equivMapOfInjective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective).symm.isSimpleGroup
  have hmap : A.map H.subtype = R := map_subgroupOf_eq_of_le le_sup_left
  have hconj : (A.conjBy s).map H.subtype = R.conjBy t := by
    change (A.map (MulAut.conj s).toMonoidHom).map H.subtype = R.map (MulAut.conj t).toMonoidHom
    rw [map_map,←hmap,map_map]
    rfl
  have hne' : A ≠ A.conjBy s := by
    intro he
    apply hne
    exact hmap.symm.trans ((congrArg (map H.subtype) he).trans hconj)
  have hc := simple_subnormal_commute_of_ne A (A.conjBy s) hr.subnormal
    (hr.map_equiv (MulAut.conj s)).subnormal hne'
  have hcG : ⁅R,R.conjBy t⁆ = ⊥ := by
    rw [←hconj,←hmap,←map_commutator,hc,Subgroup.map_bot]
  refine ⟨hcG,disjoint_def.mpr ?_⟩
  intro x hx hy
  have hz : center R = ⊥ := by
    let : IsSimpleGroup R := e.isSimpleGroup
    let : Group.IsPerfect R := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show R ≤ H from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
    exact (inferInstance : (center R).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative R (center_eq_top_iff.mp he))
  have hxz : (⟨x,hx⟩ : R) ∈ center R := mem_center_iff.mpr fun y =>
    Subtype.ext (((commutator_eq_bot_iff_le_centralizer.mp hcG y.property) x hy).symm)
  exact congrArg (fun z : R => (z : G)) (mem_bot.mp (hz ▸ hxz))

private theorem local_sylow_in (S : Sylow 2 G) (R J : Subgroup G)
    (hr : R ∈ ChapterA.Section03.localCComponents S) (hSJ : (S : Subgroup G) ≤ J) :
    ∃ P : Sylow 2 R, (P : Subgroup R).map R.subtype ≤ J := by
  let H := R ⊔ (S : Subgroup G)
  let A := R.subgroupOf H
  let U := S.subtype (show (S : Subgroup G) ≤ H from le_sup_right)
  obtain ⟨P,hP⟩ := U.exists_subgroupOf_eq_of_subnormal A hr.subnormal
  let e := subgroupOfEquivOfLe (show R ≤ H from le_sup_left)
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
  rw [hP] at hx
  exact hSJ hx

private theorem local_conj (S : Sylow 2 G) (R : Subgroup G)
    (hr : R ∈ ChapterA.Section03.localCComponents S) (t : G) (ht : t ∈ S) :
    R.conjBy t ∈ ChapterA.Section03.localCComponents S := by
  let : Group.IsSolvable (MulAut.conj t).toMonoidHom.ker := by
    rw [(MulAut.conj t).toMonoidHom.ker_eq_bot_iff.mpr (MulAut.conj t).injective]
    infer_instance
  have hs : (S : Subgroup G).map (MulAut.conj t).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp ((S : Subgroup G).le_normalizer ht)
  simpa only [Subgroup.conjBy,hs] using Chapter1.Section02.localCComponents_map_of_solvable_ker
    hr (MulAut.conj t).toMonoidHom

private theorem odd_prime_pair_factor
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 3 < p) (hF : Nat.card F = p)
    (S : Sylow 2 G) (C R U J E B : Subgroup G) [Group.IsSolvable J]
    (eC : C ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hi : (normalizer (C : Set G)).index = 2)
    (eR : R ≃* alternatingGroup (Fin 5)) (hRC : R ≤ C)
    (hr : R ∈ ChapterA.Section03.localCComponents S)
    (hU : Nat.card U = 60) (hc : ⁅R,U⁆ = ⊥) (hd : Disjoint R U)
    (hSJ : (S : Subgroup G) ≤ J) (hEJ : E ≤ J)
    (hBE : B ≤ E) (hBR : B ≤ R ⊔ U) (hB : Nat.card B = 9)
    (hodd : Odd (Nat.card E)) : E ≤ normalizer (R : Set G) := by
  have hR : Nat.card R = 60 := by
    rw [Nat.card_congr eR.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hBc := pair_cubic_intersection R U B hR hU hc hd hB hBR
  obtain ⟨P,hP⟩ := local_sylow_in S R J hr hSJ
  exact odd_prime_section ho hp hF C R J E (R ⊓ B) eC eR hRC P hP hEJ
    (odd_le_index_two E _ hodd hi) (inf_le_right.trans hBE) inf_le_left hBc hodd

private theorem odd_prime_pair
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 3 < p) (hF : Nat.card F = p)
    (S : Sylow 2 G) (C R J E B : Subgroup G) [Group.IsSolvable J]
    (eC : C ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hi : (normalizer (C : Set G)).index = 2)
    (eR : R ≃* alternatingGroup (Fin 5)) (hRC : R ≤ C)
    (hr : R ∈ ChapterA.Section03.localCComponents S)
    (t : G) (ht : t ∈ S) (hne : R ≠ R.conjBy t)
    (hSJ : (S : Subgroup G) ≤ J) (hEJ : E ≤ J)
    (hBE : B ≤ E) (hBR : B ≤ R ⊔ R.conjBy t) (hB : Nat.card B = 9)
    (hodd : Odd (Nat.card E)) : E ≤ normalizer ((R ⊔ R.conjBy t : Subgroup G) : Set G) := by
  let eU : R.conjBy t ≃* alternatingGroup (Fin 5) :=
    (R.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).symm.trans eR
  have hR : Nat.card R = 60 := by
    rw [Nat.card_congr eR.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hU : Nat.card (R.conjBy t) = 60 := by
    rw [Nat.card_congr eU.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  obtain ⟨hc,hd⟩ := local_simple_pair S R hr eR t ht hne
  have hfix := odd_prime_pair_factor ho hp hF S C R (R.conjBy t) J E B
    eC hi eR hRC hr hU hc hd hSJ hEJ hBE hBR hB hodd
  have hi' : (normalizer (C.conjBy t : Set G)).index = 2 := by
    change (normalizer ((C.map (MulAut.conj t).toMonoidHom) : Set G)).index = 2
    rw [←map_equiv_normalizer_eq C (MulAut.conj t),
      index_map_of_bijective (MulAut.conj t).bijective]
    exact hi
  have hfix' := odd_prime_pair_factor ho hp hF S (C.conjBy t) (R.conjBy t) R J E B
    ((C.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).symm.trans eC)
    hi' eU (map_mono hRC) (local_conj S R hr t ht) hR
    (by rw [commutator_comm]; exact hc) hd.symm hSJ hEJ hBE (by rwa [sup_comm]) hB hodd
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_sup,mem_normalizer_iff_map_conj_eq.mp (hfix hx),
    mem_normalizer_iff_map_conj_eq.mp (hfix' hx)]

/-- In a nonnormal odd-prime PSL₂ container, the original right Hall plane
controls both factor actions. The whole original residual is normalized. -/
theorem not_nonnormal_prime_container
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (hKT : K ⊔ (T : Subgroup G) = H) (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hCn : ¬ C.Normal)
    (hKC : K ≤ C.map Y.subtype) (hp : p.Prime) (ho : Odd p) :
    ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p := by
  intro hm
  have hmoved := nonnormal_container_seed_moved h.qtke hKH hH.1.1.2 hKL hY C hC hKC hCn
  have hlin := moved_seed_linear_four_of_escape h.qtke hKL hKT horbit hmoved hY hescape
  obtain ⟨hB,hBc⟩ := moved_seed_right_hall_plane h hH hgen c hKH hK hqs hKT horbit hmoved hlin
  obtain ⟨t,ht,_,hpair,_,_⟩ := moved_seed_pair h.qtke hKH hH.1.1.2 hH.1.1.1 hK horbit hmoved
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hTY := hH.1.1.2.trans hY.2
  have hKY := hKH.trans hY.2
  have hBY := (c.right_le.trans inf_le_right).trans hY.2
  let q := QuotientGroup.mk' (pCore 2 Y)
  let S := T.subtype hTY
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  let Rbar := (K.subgroupOf Y).map q
  let Kbar := ((residual H).subgroupOf Y).map q
  let Cbar := C.map q
  let Abar := (A.subgroupOf Y).map q
  let Bbar := (B.subgroupOf Y).map q
  let ty : Y := ⟨t,hTY ht⟩
  have hlocal : K.subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTY hKY).mp ⟨hKY,hKL⟩
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  have hlq : Rbar ∈ ChapterA.Section03.localCComponents P :=
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hlocal
  have hlt := seed_image_lt_container h.qtke hKH hH.1.1.2 hKL horbit hY hescape C hC hKC
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
  have hi : (normalizer (Cbar : Set (Y ⧸ pCore 2 Y))).index = 2 := by
    rw [cComponent_normalizer_index_quotient hC]
    exact (nonnormal_container_models h.qtke hKH hH.1.1.2 hKL horbit hY hescape C hC hKC hCn).1
  have hmapconj : ((K.subgroupOf Y).conjBy ty).map Y.subtype = K.conjBy t := by
    change ((K.subgroupOf Y).map (MulAut.conj ty).toMonoidHom).map Y.subtype =
      K.map (MulAut.conj t).toMonoidHom
    calc
      _ = ((K.subgroupOf Y).map Y.subtype).map (MulAut.conj t).toMonoidHom := by
        rw [map_map,map_map]
        rfl
      _ = _ := by rw [map_subgroupOf_eq_of_le hKY]
  have hpairY : (residual H).subgroupOf Y =
      K.subgroupOf Y ⊔ (K.subgroupOf Y).conjBy ty := by
    apply map_injective Y.subtype_injective
    rw [Subgroup.map_sup,hmapconj,map_subgroupOf_eq_of_le hKY,map_subgroupOf_eq_of_le hRY]
    exact hpair
  have hpairq : Kbar = Rbar ⊔ Rbar.conjBy (q ty) := by
    dsimp only [Kbar,Rbar]
    rw [hpairY,Subgroup.map_sup]
    congr 1
    change ((K.subgroupOf Y).map (MulAut.conj ty).toMonoidHom).map q =
      ((K.subgroupOf Y).map q).map (MulAut.conj (q ty)).toMonoidHom
    rw [map_map,map_map]
    congr 1
  have hBR : Bbar ≤ Kbar := map_mono (comap_mono (Global.right_cartan_le_residual c))
  have hBbar : Nat.card Bbar = 9 := by
    let := hB
    have hd : Disjoint (pCore 2 Y) (B.subgroupOf Y) :=
      IsPGroup.disjoint_of_ne 2 3 (by decide) _ _ pCore_isPGroup
        (IsElementaryAbelian.isPGroup 3 B).comap_subtype
    have hi : Function.Injective (q.comp (B.subgroupOf Y).subtype) := by
      apply (q.comp (B.subgroupOf Y).subtype).ker_eq_bot_iff.mp
      rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
      apply eq_bot_iff.mpr
      intro x hx
      exact Subtype.ext (disjoint_def.mp hd hx x.property)
    rw [show Bbar = (q.comp (B.subgroupOf Y).subtype).range by
      rw [MonoidHom.range_comp,range_subtype]]
    rw [←Nat.card_congr (MonoidHom.ofInjective hi).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hBY).toEquiv]
    exact hBc
  have hne : Rbar ≠ Rbar.conjBy (q ty) := by
    intro he
    have hh : Bbar ≤ Rbar := by simpa only [hpairq,←he,sup_idem] using hBR
    have hd := card_dvd_of_le hh
    rw [hBbar,Nat.card_congr eR.toEquiv,nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd
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
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  have hn := odd_prime_pair ho hp3 hF P Cbar Rbar J E Bbar
    ((cComponentTwoCoreQuotientEquiv hC).symm.trans e) hi eR hlt.le hlq (q ty)
    (mem_map_of_mem q ht) hne
    (map_mono (show (T : Subgroup G).subgroupOf Y ≤ JY from le_sup_right.trans le_sup_left))
    (sup_le (map_mono (le_sup_left.trans le_sup_left)) (map_mono le_sup_right))
    le_sup_right (hBR.trans_eq hpairq) hBbar hoddE
  rw [←hpairq] at hn
  exact hescape ((residual_escape_twoCore_iff h.qtke h.sylow_normalizes hH hgen hY.2).mp
    (le_sup_left.trans hn))

/-- Every odd-prime PSL₂ containing row is excluded, including the
nonnormal paired row. Both original Hall subgroups are retained. -/
theorem not_prime_container
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (hKT : K ⊔ (T : Subgroup G) = H) (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hp : p.Prime) (ho : Odd p) : ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p := by
  by_cases hn : C.Normal
  · exact not_normal_prime_container h hH hgen c hKH hK hKT hKL horbit hY hescape C hC hn hKC hp ho
  · exact not_nonnormal_prime_container h hH hgen c hKH hK hqs hKT hKL horbit hY hescape C hC hn hKC hp ho

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The original seed and full containing orbit retain all preceding exclusions.
Every odd-prime PSL₂ container is excluded; a nonnormal container must be J₁. -/
theorem localCartan_escape_seed_pairedPrime_reduction
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
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        (C.Normal ∨ ((normalizer (C : Set Y)).index = 2 ∧
          K < residual H ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∧
          IsElementaryAbelian 3 B ∧ Nat.card B = 9 ∧
          Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model))) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,_,h25⟩ :=
    localCartan_escape_seed_twentyFive_reduction h hH hgen c hY hescape
  have hprime := fun p hp ho => LocalSieve.not_prime_container h hH hgen c hKH hK hqs hKT hKL
    hR hY hescape C hC hKC (p := p) hp ho
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,?_⟩
  by_cases hCn : C.Normal
  · exact Or.inl hCn
  have hmoved := LocalSieve.nonnormal_container_seed_moved h.qtke hKH hH.1.1.2 hKL hY C hC hKC hCn
  have hlin := LocalSieve.moved_seed_linear_four_of_escape h.qtke hKL hKT hR hmoved hY hescape
  obtain ⟨hB,hBc⟩ := LocalSieve.moved_seed_right_hall_plane h hH hgen c hKH hK hqs hKT hR hmoved hlin
  obtain ⟨hi,hm⟩ := LocalSieve.nonnormal_container_models h.qtke hKH hH.1.1.2 hKL hR
    hY hescape C hC hKC hCn
  refine Or.inr ⟨hi,lt_of_le_of_ne ((le_componentOrbit K _).trans_eq hR) hmoved,hlin,hB,hBc,?_⟩
  rcases hm with hj | ⟨p,hp,hm,_⟩
  · exact hj
  · exact (hprime p hp.1 hp.2.1 hm).elim

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
