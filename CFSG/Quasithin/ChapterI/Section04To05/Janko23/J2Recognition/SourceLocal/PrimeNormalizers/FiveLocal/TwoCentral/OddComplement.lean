module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.Preparation
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.LocalData
public import Theory.GroupTheory.CyclicSylowTwoComplement
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.GroupTheory.FixedInvertedFactorization
public import Theory.GroupTheory.SpecificGroups.CyclicInvertedDihedral
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The two-central five-normalizer from its odd complement

For the marked local data of Aschbacher, *Sporadic Groups* (1994), 47.2
(printed p.261, PDF p.136), put C = C_G(Y). Its centralizer of z has
order ten, so the normalizer of the involution subgroup proves that
⟨z⟩ is Sylow two in C. Burnside transfer supplies the normal odd core K
as a complement, and the index-two quotient puts P inside K.

Fixed/inverted factorization shows that conjugation by z induces inversion
on the literal quotient K/Y. Thus K/Y is abelian and K is nilpotent.
This alone does not imply that K is abelian: the available self-centralizing
Sylow subgroup P is essential. Every other Sylow subgroup of K centralizes
P and therefore lies in P, forcing K = P. In particular K is abelian and
C = P⟨z⟩, with no additional odd-complement assumption.

Frattini's argument in N_G(Y), using the normal subgroup C, identifies the
whole normalizer as P⟨z,t⟩. The independent inversion actions give actual
commuting D₁₀ factors with trivial intersection, hence D₁₀ × D₁₀.
The final theorem has exactly the `hglobal` contract of
`FiveLocal.twoCentralFiveFamily_of_local_calculation`; construction of
`LocalData` remains with that source-theorem assembly.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.OddComplement

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem nilpotent_eq_selfcentralizing_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (K : Subgroup G) (hPK : (P : Subgroup G) ≤ K)
    [Group.IsNilpotent K] (hC : centralizer (P : Set G) = (P : Subgroup G)) :
    K = (P : Subgroup G) := by
  have hKp : IsPGroup p K := by
    rw [IsPGroup.iff_card]
    refine ⟨(Nat.primeFactorsList (Nat.card K)).length, ?_⟩
    apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    intro q hq hqcard
    by_contra hqp
    let : Fact q.Prime := ⟨hq⟩
    let Q : Sylow q K := default
    let R := P.subtype hPK
    have hdis : Disjoint (Q : Subgroup K) (R : Subgroup K) :=
      IsPGroup.disjoint_of_ne q p hqp _ _ Q.isPGroup' R.isPGroup'
    have hQP : (Q : Subgroup K) ≤ R := by
      intro x hx
      change (x : G) ∈ (P : Subgroup G)
      rw [← hC]
      intro y hy
      have hcomm := commute_of_normal_of_disjoint (Q : Subgroup K) (R : Subgroup K)
        inferInstance inferInstance hdis x ⟨y, hPK hy⟩ hx hy
      exact (congrArg Subtype.val hcomm.eq).symm
    have hQbot : (Q : Subgroup K) = ⊥ :=
      le_bot_iff.mp (fun x hx => hdis.le_bot ⟨hx, hQP hx⟩)
    exact Q.ne_bot_of_dvd_card hqcard hQbot
  exact P.is_maximal' hKp hPK

variable {G : Type*} [Group G] [Finite G] {E Y : Subgroup G} {P : Sylow 5 G} {z : G}
variable (L : LocalData E Y P z)
include L

omit [Finite G] in
private theorem inverter_mem_centralizer : z ∈ centralizer (Y : Set G) := by
  intro y hy
  exact mem_centralizer_singleton_iff.mp (L.centralizes_Y hy)

omit [Finite G] in
private theorem local_centralizer_join_card : Nat.card (Y ⊔ zpowers z : Subgroup G) = 10 := by
  have hznot : z ∉ Y := by
    intro hz
    have hd := orderOf_dvd_natCard (⟨z, hz⟩ : Y)
    rw [orderOf_mk, L.involution_z, L.card_Y] at hd
    norm_num at hd
  rw [card_sup_zpowers_of_normalizing_involution Y z
    (L.involution_z ▸ pow_orderOf_eq_one z) hznot
    (centralizer_le_normalizer _ (inverter_mem_centralizer L)), L.card_Y]

omit [Finite G] in
private theorem centralizer_inverter_card :
    Nat.card (centralizer ({(⟨z, inverter_mem_centralizer L⟩ : centralizer (Y : Set G))} :
      Set (centralizer (Y : Set G)))) = 10 := by
  let C := centralizer (Y : Set G)
  let zC : C := ⟨z, inverter_mem_centralizer L⟩
  have hm : (centralizer ({zC} : Set C)).map C.subtype =
      involutionCentralizer z ⊓ C := by
    ext x
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx)), x.property⟩
    · intro hx
      exact ⟨⟨x, hx.2⟩, mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hx.1)), rfl⟩
  change Nat.card (centralizer ({zC} : Set C)) = 10
  rw [← card_map_of_injective C.subtype_injective, hm, L.local_centralizer]
  exact local_centralizer_join_card L

private theorem exists_sylow_two_eq_zpowers : ∃ S : Sylow 2 (centralizer (Y : Set G)),
    (S : Subgroup (centralizer (Y : Set G))) = zpowers ⟨z, inverter_mem_centralizer L⟩ := by
  let C := centralizer (Y : Set G)
  let zC : C := ⟨z, inverter_mem_centralizer L⟩
  have ho : orderOf zC = 2 := (orderOf_mk _ _).trans L.involution_z
  have hc : Nat.card (zpowers zC) = 2 ^ 1 := by rw [Nat.card_zpowers, ho, pow_one]
  have hn4 : ¬ 2 ^ 2 ∣ Nat.card C := by
    intro hd
    have hn := Sylow.prime_pow_dvd_card_normalizer (p := 2) (n := 1) hd hc
    rw [normalizer_zpowers_eq_centralizer_of_order_two zC ho,
      centralizer_inverter_card L] at hn
    norm_num at hn
  have hi : ¬ 2 ∣ (zpowers zC).index := by
    intro hi
    apply hn4
    rw [← card_mul_index (zpowers zC), hc]
    exact Nat.mul_dvd_mul (dvd_refl 2) hi
  exact ⟨(IsPGroup.of_card hc).toSylow hi, rfl⟩

private theorem oddCore_isComplement :
    (zpowers (⟨z, inverter_mem_centralizer L⟩ : centralizer (Y : Set G))).IsComplement'
      (pPrimeCore 2 (centralizer (Y : Set G))) := by
  obtain ⟨S, hS⟩ := exists_sylow_two_eq_zpowers L
  have hcy : IsCyclic S := by rw [hS]; infer_instance
  have heven : 2 ∣ Nat.card (centralizer (Y : Set G)) := by
    have hd := card_subgroup_dvd_card (zpowers (⟨z, inverter_mem_centralizer L⟩ : centralizer (Y : Set G)))
    rwa [Nat.card_zpowers, orderOf_mk, L.involution_z] at hd
  simpa only [hS] using S.isComplement'_pPrimeCore_of_isCyclic hcy heven

omit [Finite G] in
private theorem sylow_le_centralizer (hP : IsElementaryAbelian 5 P) :
    (P : Subgroup G) ≤ centralizer (Y : Set G) := by
  let : IsMulCommutative P := hP.toIsMulCommutative
  exact (le_centralizer (P : Subgroup G)).trans
    (centralizer_le (show Y ≤ (P : Subgroup G) from L.product ▸ le_sup_right))

private theorem sylow_subgroupOf_le_oddCore (hP : IsElementaryAbelian 5 P) :
    (P : Subgroup G).subgroupOf (centralizer (Y : Set G)) ≤
      pPrimeCore 2 (centralizer (Y : Set G)) := by
  let C := centralizer (Y : Set G)
  let K := pPrimeCore 2 C
  have hi : K.index = 2 := by
    rw [(oddCore_isComplement L).index_eq_card, Nat.card_zpowers, orderOf_mk, L.involution_z]
  rw [← relIndex_eq_one]
  apply Nat.eq_one_of_dvd_coprimes (show Nat.Coprime 2 (Nat.card
    ((P : Subgroup G).subgroupOf C)) from ?_)
    (by simpa only [hi] using K.relIndex_dvd_index_of_normal ((P : Subgroup G).subgroupOf C))
    (K.relIndex_dvd_card _)
  obtain ⟨n, hn⟩ := (P.isPGroup'.of_equiv (subgroupOfEquivOfLe (sylow_le_centralizer L hP)).symm).exists_card_eq
  rw [hn]
  exact (show Nat.Coprime 2 5 from by decide).pow_right n

omit L in
private theorem nilpotent_of_odd_fixed_le_center
    {H : Type*} [Group H] [Finite H] (Z : Subgroup H) [Z.Normal]
    (hZ : Z ≤ center H) (hodd : Odd (Nat.card H))
    (φ : MulAut H) (hφ : Function.Involutive φ)
    (hfix : ∀ x, φ x = x → x ∈ Z) : Group.IsNilpotent H := by
  let q := QuotientGroup.mk' Z
  have hinv (x : H) : q (φ x) = (q x)⁻¹ := by
    obtain ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, _⟩ :=
      Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card hodd φ hφ x
    have haq : q a = 1 := (QuotientGroup.eq_one_iff _).mpr (hfix a ha)
    rw [← hab]
    simp only [map_mul, ha, hb, map_inv, haq, one_mul]
  let : IsMulCommutative (H ⧸ Z) := ⟨⟨by
    intro x y
    obtain ⟨a, rfl⟩ := (QuotientGroup.mk'_surjective Z) x
    obtain ⟨b, rfl⟩ := (QuotientGroup.mk'_surjective Z) y
    have h := congrArg q (φ.map_mul a b)
    rw [hinv, map_mul, map_mul, hinv, hinv, mul_inv_rev] at h
    exact inv_injective (by simpa only [q, mul_inv_rev] using h)⟩⟩
  let : CommGroup (H ⧸ Z) := IsMulCommutative.instCommGroup
  exact Subgroup.isNilpotent_of_ker_le_center q (by simpa only [q, QuotientGroup.ker_mk'] using hZ)

private theorem oddCore_nilpotent (hP : IsElementaryAbelian 5 P) :
    Group.IsNilpotent (pPrimeCore 2 (centralizer (Y : Set G))) := by
  let C := centralizer (Y : Set G)
  let K := pPrimeCore 2 C
  let zC : C := ⟨z, inverter_mem_centralizer L⟩
  let YC := Y.subgroupOf C
  have hYP : Y ≤ (P : Subgroup G) := L.product ▸ le_sup_right
  have hYC : Y ≤ C := hYP.trans (sylow_le_centralizer L hP)
  have hYK : YC ≤ K := (subgroupOf_mono C hYP).trans (sylow_subgroupOf_le_oddCore L hP)
  have hzYC : zC ∈ centralizer (YC : Set C) := by
    intro y hy
    exact Subtype.ext (inverter_mem_centralizer L y hy)
  have hc : centralizer ({zC} : Set C) = YC ⊔ zpowers zC := by
    apply (map_injective C.subtype_injective)
    have hm : (centralizer ({zC} : Set C)).map C.subtype =
        involutionCentralizer z ⊓ C := by
      ext x
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx)), x.property⟩
      · intro hx
        exact ⟨⟨x, hx.2⟩, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hx.1)), rfl⟩
    rw [hm, L.local_centralizer, Subgroup.map_sup, MonoidHom.map_zpowers,
      subgroupOf_map_subtype, inf_of_le_left hYC]
    rfl
  let Z := YC.subgroupOf K
  have hZ : Z ≤ center K := by
    intro a ha
    apply mem_center_iff.mpr
    intro b
    apply Subtype.ext
    apply Subtype.ext
    exact (b.val.property a.val.val ha).symm
  let : Z.Normal := ⟨fun x hx g => by
    have hg := mem_center_iff.mp (hZ hx) g
    simpa only [hg, mul_assoc, mul_inv_cancel, mul_one] using hx⟩
  let φ : MulAut K := MulAut.conjNormal zC
  have hφ : Function.Involutive φ := by
    intro x
    have hzz : zC * zC = 1 := by
      apply Subtype.ext
      exact (pow_two z).symm.trans (L.involution_z ▸ pow_orderOf_eq_one z)
    apply Subtype.ext
    change zC * (zC * (x : C) * zC⁻¹) * zC⁻¹ = x
    calc
      _ = (zC * zC) * (x : C) * (zC * zC)⁻¹ := by group
      _ = x := by simp only [hzz, one_mul, inv_one, mul_one]
  have hfix (x : K) (hx : φ x = x) : x ∈ Z := by
    have hxC : (x : C) ∈ centralizer ({zC} : Set C) := by
      apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg Subtype.val hx
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    rw [hc] at hxC
    have hprod : (x : C) ∈ (YC : Set C) * (zpowers zC : Set C) := by
      rw [← coe_mul_of_right_le_normalizer_left YC (zpowers zC)
        (zpowers_le.mpr (centralizer_le_normalizer _ hzYC))]
      exact hxC
    obtain ⟨y, hy, w, hw, hyw⟩ := hprod
    have hwK : w ∈ K := by
      have hh := K.mul_mem (K.inv_mem (hYK hy)) x.property
      rwa [← hyw, inv_mul_cancel_left] at hh
    have hw1 : w = 1 := (disjoint_def.mp (oddCore_isComplement L).disjoint) hw hwK
    change (x : C) ∈ YC
    have hyx : y = (x : C) := by simpa only [hw1, mul_one] using hyw
    exact hyx ▸ hy
  exact nilpotent_of_odd_fixed_le_center Z hZ
    (by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact Nat.prime_two.coprime_iff_not_dvd.mp (pPrimeCore_coprime_card (p := 2) (G := C))) φ hφ hfix

/-- The literal ambient centralizer is generated by P and the marked involution. -/
theorem centralizer_eq (hP : IsElementaryAbelian 5 P)
    (hCP : centralizer (P : Set G) = (P : Subgroup G)) :
    centralizer (Y : Set G) = (P : Subgroup G) ⊔ zpowers z := by
  let C := centralizer (Y : Set G)
  let K := pPrimeCore 2 C
  let A := K.map C.subtype
  have hPA : (P : Subgroup G) ≤ A := by
    intro x hx
    exact ⟨⟨x, sylow_le_centralizer L hP hx⟩, sylow_subgroupOf_le_oddCore L hP hx, rfl⟩
  let : Group.IsNilpotent K := oddCore_nilpotent L hP
  let : Group.IsNilpotent A := Group.nilpotent_of_mulEquiv
    (K.equivMapOfInjective C.subtype C.subtype_injective)
  have hA : A = (P : Subgroup G) := nilpotent_eq_selfcentralizing_sylow P A hPA hCP
  have hs := congrArg (fun H : Subgroup C => H.map C.subtype) (oddCore_isComplement L).sup_eq_top
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
    C.range_subtype] at hs
  change zpowers z ⊔ A = C at hs
  rw [hA, sup_comm] at hs
  exact hs.symm

/-- Frattini's argument gives the whole normalizer from the local normalizer identity. -/
theorem normalizer_eq (hP : IsElementaryAbelian 5 P)
    (hCP : centralizer (P : Set G) = (P : Subgroup G)) :
    normalizer (Y : Set G) = (P : Subgroup G) ⊔ (zpowers z ⊔ zpowers L.t) := by
  let C := centralizer (Y : Set G)
  let N := normalizer (Y : Set G)
  let CN := C.subgroupOf N
  have hCN : C ≤ N := centralizer_le_normalizer _
  let zC : C := ⟨z, inverter_mem_centralizer L⟩
  let zN : N := ⟨z, hCN (inverter_mem_centralizer L)⟩
  let e : C ≃* CN := (subgroupOfEquivOfLe hCN).symm
  obtain ⟨S, hS⟩ := exists_sylow_two_eq_zpowers L
  let T : Sylow 2 CN := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hi : (T : Subgroup CN).map CN.subtype = zpowers zN := by
    change ((S : Subgroup C).map e.toMonoidHom).map CN.subtype = zpowers zN
    rw [hS, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hf := T.normalizer_sup_eq_top
  change normalizer ((T : Subgroup CN).map CN.subtype : Set N) ⊔ CN = ⊤ at hf
  rw [hi, normalizer_zpowers_eq_centralizer_of_order_two zN
    ((orderOf_mk _ _).trans L.involution_z)] at hf
  have hm : (centralizer ({zN} : Set N)).map N.subtype =
      involutionCentralizer z ⊓ N := by
    ext x
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx)), x.property⟩
    · intro hx
      exact ⟨⟨x, hx.2⟩, mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hx.1)), rfl⟩
  have hh := congrArg (fun H : Subgroup N => H.map N.subtype) hf
  rw [Subgroup.map_sup, hm, ← MonoidHom.range_eq_map, N.range_subtype] at hh
  change (involutionCentralizer z ⊓ normalizer (Y : Set G)) ⊔
    (C.subgroupOf N).map N.subtype = N at hh
  rw [L.local_normalizer, subgroupOf_map_subtype, inf_of_le_left hCN] at hh
  change Y ⊔ (zpowers z ⊔ zpowers L.t) ⊔ centralizer (Y : Set G) = N at hh
  rw [centralizer_eq L hP hCP] at hh
  have hYP : Y ≤ (P : Subgroup G) := L.product ▸ le_sup_right
  have hj : Y ⊔ (zpowers z ⊔ zpowers L.t) ⊔ ((P : Subgroup G) ⊔ zpowers z) =
      (P : Subgroup G) ⊔ (zpowers z ⊔ zpowers L.t) := by
    apply le_antisymm
    · exact sup_le (sup_le (hYP.trans le_sup_left) le_sup_right)
        (sup_le le_sup_left (le_sup_left.trans le_sup_right))
    · exact sup_le (le_sup_left.trans le_sup_right) (le_sup_right.trans le_sup_left)
  rw [hj] at hh
  exact hh.symm

private theorem generated_equiv_dihedral_prod (hP : IsElementaryAbelian 5 P) :
    Nonempty (↥((P : Subgroup G) ⊔ (zpowers z ⊔ zpowers L.t)) ≃*
      (DihedralGroup 5 × DihedralGroup 5)) := by
  let A := E ⊔ zpowers z
  let B := Y ⊔ zpowers L.t
  have hEcyclic : IsCyclic E := isCyclic_of_prime_card L.card_E
  have hYcyclic : IsCyclic Y := isCyclic_of_prime_card L.card_Y
  have hznot : z ∉ E := by
    intro hz
    have hd := orderOf_dvd_natCard (⟨z, hz⟩ : E)
    rw [orderOf_mk, L.involution_z, L.card_E] at hd
    norm_num at hd
  have htnot : L.t ∉ Y := by
    intro ht
    have hd := orderOf_dvd_natCard (⟨L.t, ht⟩ : Y)
    rw [orderOf_mk, L.involution_t, L.card_Y] at hd
    norm_num at hd
  have hA := E.nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted z hEcyclic
    (L.involution_z ▸ pow_orderOf_eq_one z) hznot L.inverts_E
  have hB := Y.nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted L.t hYcyclic
    (L.involution_t ▸ pow_orderOf_eq_one L.t) htnot L.inverts_Y
  rw [L.card_E] at hA
  rw [L.card_Y] at hB
  obtain ⟨eA⟩ := hA
  obtain ⟨eB⟩ := hB
  have hAt : A ≤ centralizer ({L.t} : Set G) :=
    sup_le L.centralizes_E (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr L.commutes.eq))
  have hAY : A ≤ centralizer (Y : Set G) :=
    sup_le ((show E ≤ (P : Subgroup G) from L.product ▸ le_sup_left).trans (sylow_le_centralizer L hP))
      (zpowers_le.mpr (inverter_mem_centralizer L))
  have hBA : B ≤ centralizer (A : Set G) :=
    sup_le (le_centralizer_iff.mp hAY) (zpowers_le.mpr (fun x hx =>
      mem_centralizer_singleton_iff.mp (hAt hx)))
  have hcomm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hBA b.property a a.property
  have hdisj : Disjoint A B := by
    apply Subgroup.disjoint_def.mpr
    intro x hxA hxB
    let a : A := ⟨x, hxA⟩
    have ha : a ∈ Subgroup.center A := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcomm y ⟨x, hxB⟩).eq
    have hea : eA a ∈ Subgroup.center (DihedralGroup 5) := by
      rw [Subgroup.mem_center_iff]
      intro d
      obtain ⟨y, rfl⟩ := eA.surjective d
      simpa only [map_mul] using congrArg eA (Subgroup.mem_center_iff.mp ha y)
    rw [DihedralGroup.center_eq_bot_of_odd_ne_one (by decide) (by decide)] at hea
    have he : eA a = 1 := hea
    have ha1 : a = 1 := eA.injective (he.trans eA.map_one.symm)
    exact congrArg Subtype.val ha1
  let f : A × B →* G := A.subtype.noncommCoprod B.subtype hcomm
  have hfinj : Function.Injective f := by
    apply (MonoidHom.noncommCoprod_injective A.subtype B.subtype hcomm).mpr
    exact ⟨Subtype.coe_injective, Subtype.coe_injective,
      by simpa only [Subgroup.subtype_range] using hdisj⟩
  let e : f.range ≃* (DihedralGroup 5 × DihedralGroup 5) :=
    (MulEquiv.ofBijective f.rangeRestrict
      ⟨fun x y h => hfinj (congrArg Subtype.val h), f.rangeRestrict_surjective⟩).symm.trans
        (eA.prodCongr eB)
  have heq : f.range = (P : Subgroup G) ⊔ (zpowers z ⊔ zpowers L.t) := by
    change (A.subtype.noncommCoprod B.subtype hcomm).range = _
    rw [MonoidHom.noncommCoprod_range, Subgroup.subtype_range, Subgroup.subtype_range,
      ← L.product]
    dsimp only [A, B]
    ac_rfl
  exact ⟨(MulEquiv.subgroupCongr heq).symm.trans e⟩

omit L in
/-- The exact conditional implication consumed by the two-central assembly. -/
theorem normalizer_equiv (E Y : Subgroup G) (P : Sylow 5 G) (z : G)
    (L : LocalData E Y P z) (hP : IsElementaryAbelian 5 P)
    (hCP : centralizer (P : Set G) = (P : Subgroup G)) :
    Nonempty (normalizer (Y : Set G) ≃* (DihedralGroup 5 × DihedralGroup 5)) := by
  obtain ⟨e⟩ := generated_equiv_dihedral_prod L hP
  exact ⟨(MulEquiv.subgroupCongr (normalizer_eq L hP hCP)).trans e⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral.OddComplement
