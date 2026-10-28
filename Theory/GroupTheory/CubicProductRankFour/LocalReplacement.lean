module
public import Theory.GroupTheory.CubicProductRankFour
public import Theory.Quasithin.LocalRank

/-!
# The cubic local replacement in a central product

Let two commuting factors meet in their common center of order three. A cyclic
order-nine subgroup in the first factor and an abelian order-27 subgroup in the
second, both containing that center and with cubes in it, generate an abelian
group of order 81. Its cube map has image of order at most three, so its
elementary kernel has order at least 27.

If the cyclic group normalizes a nontrivial two-subgroup of its factor, the
whole replacement product lies in the normalizer of the original embedded
two-subgroup. The resulting local rank three contradicts quasithinness. Together
with the extraction theorem this bounds the central product's three-rank by
three, retaining the single-factor cyclic-nine localization as an explicit
independent input, produced by `qt-a02-su3-central-cube-localization`.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
A.2.12(II), printed p.37, manuscript of 1 March 2004.
-/
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CubicProductRankFour

private theorem cube_mem_center_of_card_nine
    {A : Type*} [Group A] [Finite A] (C : Subgroup A)
    (hC : Nat.card C = 9) (hZ : Nat.card (center A) = 3)
    (hZC : center A ≤ C) (c : C) : (c : A)^3 ∈ center A := by
  let q := (QuotientGroup.mk' (center A)).comp C.subtype
  have hk : q.ker = (center A).subgroupOf C := by
    ext x
    exact QuotientGroup.eq_one_iff _
  have hkc : Nat.card q.ker = 3 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe hZC).toEquiv, hZ]
  have hcard := q.ker.card_mul_index
  rw [index_ker,hkc,hC] at hcard
  have hr : Nat.card q.range = 3 := by omega
  have hcub : (q c)^3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by
    simpa only [hr] using q.range.orderOf_dvd_natCard (show q c ∈ q.range from ⟨c,rfl⟩))
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' (center A)) ((c : A)^3) = 1
  rw [map_pow]
  exact hcub

/-- The replacement product forces rank three in the literal ambient normalizer. -/
public theorem local_replacement_rank_three
    {H : Type*} [Group H] [Finite H] (A B : Subgroup H)
    (hc : A ≤ centralizer (B : Set H))
    (hcenters : (center A).map A.subtype = (center B).map B.subtype)
    (hinter : A ⊓ B = (center A).map A.subtype)
    (hAc : Nat.card (center A) = 3)
    (C : Subgroup A) [IsCyclic C] (hC : Nat.card C = 9) (hZC : center A ≤ C)
    (P : Subgroup B) [IsMulCommutative P] (hP : Nat.card P = 27)
    (hZP : center B ≤ P) (hPcube : ∀ b ∈ P, b ^ 3 ∈ center B)
    (Q : Subgroup A) (hCN : C ≤ normalizer (Q : Set A)) :
    3 ≤ primeRank 3 (normalizer (Q.map A.subtype : Set H)) := by
  let C' := C.map A.subtype
  let P' := P.map B.subtype
  let Z := (center A).map A.subtype
  let D := C' ⊔ P'
  have hCA : C' ≤ A := map_subtype_le C
  have hPB : P' ≤ B := map_subtype_le P
  have hcc : C' ≤ centralizer (P' : Set H) := by
    intro c hc' p hp
    exact hc (hCA hc') p (hPB hp)
  have hZC' : Z ≤ C' := map_mono hZC
  have hZP' : Z ≤ P' := by rw [show Z = (center B).map B.subtype from hcenters]; exact map_mono hZP
  have hCP : C' ⊓ P' = Z :=
    le_antisymm ((inf_le_inf hCA hPB).trans hinter.le) (le_inf hZC' hZP')
  have hcardZ : Nat.card Z = 3 := (card_map_of_injective A.subtype_injective).trans hAc
  have hcardC : Nat.card C' = 9 := (card_map_of_injective A.subtype_injective).trans hC
  have hcardP : Nat.card P' = 27 := (card_map_of_injective B.subtype_injective).trans hP
  have hcardD : Nat.card D = 81 := by
    have ht := card_mul_eq_card_inf_mul_card_sup_of_normalizes C' P'
      ((le_centralizer_iff.mp hcc).trans (centralizer_le_normalizer _))
    rw [hcardC,hcardP,hCP,hcardZ] at ht
    change Nat.card (C' ⊔ P' : Subgroup H) = 81
    omega
  let : IsMulCommutative C' := map_isMulCommutative _ _
  let : IsMulCommutative P' := map_isMulCommutative _ _
  let : IsMulCommutative D := by
    apply le_centralizer_iff_isMulCommutative.mp
    exact sup_le
      (le_centralizer_iff.mpr (sup_le C'.le_centralizer (le_centralizer_iff.mp hcc)))
      (le_centralizer_iff.mpr (sup_le hcc P'.le_centralizer))
  let : CommGroup D := IsMulCommutative.instCommGroup
  have hZD : Z ≤ D := hZC'.trans le_sup_left
  have hcubeD (d : D) : (d : H)^3 ∈ Z := by
    have hcomm (c : C') (p : P') : Commute (c : H) (p : H) := (hcc c.property p p.property).symm
    let f : C' × P' →* H := C'.subtype.noncommCoprod P'.subtype hcomm
    have hfrange : f.range = D := by
      exact (MonoidHom.noncommCoprod_range _ _ _).trans (by rw [C'.range_subtype,P'.range_subtype])
    have hdmem : (d : H) ∈ f.range := by rw [hfrange]; exact d.property
    obtain ⟨⟨c,p⟩,hdeq⟩ := hdmem
    change (c : H) * (p : H) = (d : H) at hdeq
    obtain ⟨a,ha,haeq⟩ := c.property
    obtain ⟨b,hb,hbeq⟩ := p.property
    rw [← hdeq,(hcomm c p).mul_pow]
    apply Z.mul_mem
    · rw [← haeq]
      exact mem_map.mpr ⟨a^3,cube_mem_center_of_card_nine C hC hAc hZC ⟨a,ha⟩,rfl⟩
    · rw [show Z = (center B).map B.subtype from hcenters, ← hbeq]
      exact mem_map.mpr ⟨b^3,hPcube b hb,rfl⟩
  let cube : D →* D := powMonoidHom 3
  have himage : cube.range ≤ Z.subgroupOf D := by
    rintro d ⟨a,rfl⟩
    exact hcubeD a
  have himagecard : Nat.card cube.range ≤ 3 := by
    have h := card_le_of_le himage
    rwa [Nat.card_congr (subgroupOfEquivOfLe hZD).toEquiv,hcardZ] at h
  let : IsElementaryAbelian 3 cube.ker :=
    { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => Subtype.ext x.property) }
  have hkernel : 27 ≤ Nat.card cube.ker := by
    have hm := cube.ker.card_mul_index
    rw [index_ker,hcardD] at hm
    nlinarith
  have hrD : 3 ≤ primeRank 3 D := by
    by_contra! hr
    have hsmall := (primeRank_le_iff_elementary_card_le D).mp (show primeRank 3 D ≤ 2 by omega)
      cube.ker inferInstance
    change Nat.card cube.ker ≤ 9 at hsmall
    omega
  have hCN' : C' ≤ normalizer (Q.map A.subtype : Set H) :=
    (map_mono hCN).trans (le_normalizer_map A.subtype)
  have hPN' : P' ≤ normalizer (Q.map A.subtype : Set H) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro p hp q hq
    exact (hc (map_subtype_le Q hq) p (hPB hp)).symm
  exact hrD.trans (primeRank_le_of_injective 3 (inclusion (sup_le hCN' hPN'))
    (inclusion_injective (sup_le hCN' hPN')))

/-- A nontrivial two-subgroup makes the constructed rank-three normalizer a two-local. -/
public theorem not_quasithin_of_local_replacement
    {H : Type*} [Group H] [Finite H] (A B : Subgroup H)
    (hc : A ≤ centralizer (B : Set H))
    (hcenters : (center A).map A.subtype = (center B).map B.subtype)
    (hinter : A ⊓ B = (center A).map A.subtype)
    (hAc : Nat.card (center A) = 3)
    (C : Subgroup A) [IsCyclic C] (hC : Nat.card C = 9) (hZC : center A ≤ C)
    (P : Subgroup B) [IsMulCommutative P] (hP : Nat.card P = 27)
    (hZP : center B ≤ P) (hPcube : ∀ b ∈ P, b ^ 3 ∈ center B)
    (Q : Subgroup A) (hQ : IsPGroup 2 Q) (hQne : Q ≠ ⊥)
    (hCN : C ≤ normalizer (Q : Set A)) : ¬ IsQuasithin H := by
  intro hH
  have hQne' : Q.map A.subtype ≠ ⊥ :=
    fun h => hQne ((map_eq_bot_iff_of_injective Q A.subtype_injective).mp h)
  have hu := isQuasithin_iff_twoLocal.mp hH (normalizer (Q.map A.subtype : Set H))
    ⟨Q.map A.subtype,hQne',hQ.map A.subtype,rfl⟩ 3 Nat.prime_three (by decide)
  have hl := local_replacement_rank_three A B hc hcenters hinter hAc C hC hZC
    P hP hZP hPcube Q hCN
  omega

/-- The central-product upper bound from the independent single-factor localization. -/
public theorem primeRank_le_three_of_cubic_localization
    {H : Type*} [Group H] [Finite H] (A B : Subgroup H)
    (hc : A ≤ centralizer (B : Set H))
    (hprod : ∀ h : H, ∃ a : A, ∃ b : B, (a : H) * b = h)
    (hcenters : (center A).map A.subtype = (center B).map B.subtype)
    (hinter : A ⊓ B = (center A).map A.subtype)
    (hAc : Nat.card (center A) = 3) (hBc : Nat.card (center B) = 3)
    (hA : primeRank 3 A ≤ 2) (hB : primeRank 3 B ≤ 2)
    (hAq : primeRank 3 (A ⧸ center A) ≤ 2)
    (hBq : primeRank 3 (B ⧸ center B) ≤ 2)
    (hlocal : ∀ (z x : A), z ∈ center A → z ≠ 1 → x^3=z →
      ∃ (Q C : Subgroup A), IsPGroup 2 Q ∧ Q ≠ ⊥ ∧ IsCyclic C ∧
        Nat.card C = 9 ∧ center A ≤ C ∧ C ≤ normalizer (Q : Set A))
    (hH : IsQuasithin H) : primeRank 3 H ≤ 3 := by
  by_contra! hr
  obtain ⟨z,x,P,y,hzne,hz,hx,hPc,hP,hZP,hPcube,_⟩ :=
    exists_matching_cube_roots_of_rank_four A B hc hprod hcenters hAc hBc hA hB hAq hBq (by omega)
  obtain ⟨za,hza,hzaeq⟩ := hz
  have hzan : za ≠ 1 := by intro h; apply hzne; rw [← hzaeq,h]; rfl
  have hxza : x^3=za := Subtype.ext (hx.trans hzaeq.symm)
  obtain ⟨Q,C,hQ,hQne,hCc,hC,hZC,hCN⟩ := hlocal za x hza hzan hxza
  let : IsCyclic C := hCc
  let : IsMulCommutative P := hPc
  exact not_quasithin_of_local_replacement A B hc hcenters hinter hAc C hC hZC
    P hP hZP hPcube Q hQ hQne hCN hH

end CubicProductRankFour
