module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.BothAbelian
public import Theory.GroupTheory.AbelianIndexTwoCenter
public import Theory.GroupTheory.IndexThreeCenterBound.Quarter
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.CharacteristicTwoIndexTwoRestriction

/-!
# The original source bound with one abelian local core

The two actual cores have a common subgroup of index two. It is abelian
and cannot be normal in the opposite vertex: its centralizer would be a
normal two-group containing the first core. A conjugate distinct from it
therefore forces the opposite core center to have index at most four.
That center centralizes the common Sylow, hence is central in the opposite
vertex. The first vertex center lies in it; source faithfulness kills the
first center. The index-three center estimate now gives |O₂(A)| ≤ 16 and
|A∩B| ≤ 32. The literal residual F.6.5 branch has |S| = 32 exactly.

Source: Aschbacher–Smith F.1.12/F.6.5, printed pp.262–263 and 305.
No universal depth bound or marked classification is assumed. The remaining
order-thirty-two marking and the two-nonabelian-core depth cases are separate.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.SourceAssembly.OneAbelian
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
private abbrev Q (A : Subgroup G) := (pCore 2 A).map A.subtype
private abbrev Z (A : Subgroup G) := (center A).map A.subtype

private theorem two_mul_core_card (h : IsGoldschmidtTriple A B) :
    2 * Nat.card (Q A) = Nat.card (A ⊓ B : Subgroup G) := by
  let K := (Q A).subgroupOf (A ⊓ B)
  have hh := K.index_mul_card
  have hK : Nat.card K = Nat.card (Q A) := by
    exact Nat.card_congr (subgroupOfEquivOfLe h.local_twoCore_le_intersection).toEquiv
  have hiK : K.index = 2 := h.left_core_index
  rw [hiK, hK] at hh
  exact hh

private theorem center_le_core (h : IsGoldschmidtTriple A B)
    (hA : generalizedFitting A=pCore 2 A) : Z A ≤ Q A :=
  map_mono ((center_le_centralizer _).trans (h.local_core_selfCentralizing hA))

omit [Finite G] in
private theorem center_centralizes (A : Subgroup G) : Z A ≤ centralizer (A : Set G) := by
  rintro _ ⟨a,ha,rfl⟩
  rw [mem_centralizer_iff]
  intro b hb
  exact congrArg Subtype.val ((mem_center_iff.mp ha) ⟨b,hb⟩)

private theorem center_le_other_core (h : IsGoldschmidtTriple A B)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B) :
    Z A ≤ Q B := by
  intro x hx
  have hxB : x ∈ B := (h.local_twoCore_le_intersection (center_le_core h hA hx)).2
  have hxc : (⟨x,hxB⟩ : B) ∈ centralizer (pCore 2 B : Set B) := by
    rw [mem_centralizer_iff]
    intro b hb
    apply Subtype.ext
    exact mem_centralizer_iff.mp (center_centralizes A hx) b
      ((h.symm.local_twoCore_le_intersection (mem_map_of_mem B.subtype hb)).2)
  exact mem_map_of_mem B.subtype (h.symm.local_core_selfCentralizing hB hxc)

private theorem center_intersection (h : IsGoldschmidtTriple A B)
    (hcore : pCore 2 G=⊥) (hA : generalizedFitting A=pCore 2 A) :
    Z A ⊓ Z B = ⊥ := by
  have hle : Z A ⊓ Z B ≤ A ⊓ B :=
    inf_le_left.trans ((center_le_core h hA).trans h.local_twoCore_le_intersection)
  apply h.common_normal_eq_bot hcore _ hle
  · apply (normal_subgroupOf_iff_le_normalizer (hle.trans inf_le_left)).mpr
    exact ((le_centralizer_iff.mp (inf_le_left.trans (center_centralizes A))).trans
      (Subgroup.centralizer_le_normalizer _))
  · apply (normal_subgroupOf_iff_le_normalizer (hle.trans inf_le_right)).mpr
    exact ((le_centralizer_iff.mp (inf_le_right.trans (center_centralizes B))).trans
      (Subgroup.centralizer_le_normalizer _))

private theorem cores_generate_of_large (h : IsGoldschmidtTriple A B)
    (hcore : pCore 2 G=⊥) (hbig : 16 < Nat.card (A⊓B : Subgroup G)) :
    Q A ⊔ Q B = A⊓B := by
  have hqa := two_mul_core_card h
  have hqb := two_mul_core_card h.symm
  rw [inf_comm B A] at hqb
  have hout : ¬ Q B ≤ Q A := by
    intro hle
    have he : Q B=Q A := eq_of_le_of_card_ge hle (by omega)
    have hnA : ((Q A).subgroupOf A).Normal :=
      (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mpr h.left_core_normalized
    have hnB : ((Q A).subgroupOf B).Normal := by
      rw [←he]
      exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mpr h.symm.left_core_normalized
    have hh := h.common_normal_eq_bot hcore (Q A) h.local_twoCore_le_intersection hnA hnB
    rw [hh,card_bot] at hqa
    omega
  have hQT : Q A ≤ A⊓B := h.local_twoCore_le_intersection
  have hRT : Q B ≤ A⊓B := by simpa only [inf_comm B A] using h.symm.local_twoCore_le_intersection
  have hidx := relIndex_mul_relIndex (Q A) (Q A⊔Q B) (A⊓B) le_sup_left (sup_le hQT hRT)
  rw [h.left_core_index] at hidx
  have hdiv : (Q A).relIndex (Q A⊔Q B) ∣ 2 := ⟨_,hidx.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h1 | h2
  · exact (hout (le_sup_right.trans (relIndex_eq_one.mp h1))).elim
  · rw [h2] at hidx
    exact le_antisymm (sup_le hQT hRT) (relIndex_eq_one.mp (by omega))


private theorem core_intersection_card (h : IsGoldschmidtTriple A B)
    (hcore : pCore 2 G=⊥) (hbig : 16 < Nat.card (A⊓B : Subgroup G)) :
    2 * Nat.card (Q A⊓Q B : Subgroup G) = Nat.card (Q A) := by
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes (Q A) (Q B)
    ((h.symm.local_twoCore_le_intersection.trans inf_le_right).trans h.left_core_normalized)
  rw [cores_generate_of_large h hcore hbig] at hh
  have hqa := two_mul_core_card h
  have hqb := two_mul_core_card h.symm
  rw [inf_comm B A] at hqb
  have hp := Nat.card_pos (α := Q A)
  nlinarith

private theorem local_sylow_data (h : IsGoldschmidtTriple A B) :
    ((A⊓B).subgroupOf A).index=3 ∧ ¬ ((A⊓B).subgroupOf A).Normal := by
  let T := (A⊓B).subgroupOf A
  have hTc : Nat.card T = Nat.card (A⊓B : Subgroup G) :=
    Nat.card_congr (subgroupOfEquivOfLe (show A⊓B≤A from inf_le_left)).toEquiv
  have hQc : Nat.card (Q A) = Nat.card (pCore 2 A) := card_map_of_injective A.subtype_injective
  constructor
  · have hh := T.index_mul_card
    rw [hTc,h.local_card_eq_three_mul_intersection] at hh
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := (A⊓B : Subgroup G))) hh
  · intro hn
    let := hn
    obtain ⟨S,hS⟩ := h.intersection_sylow
    let eT : T ≃* (A⊓B : Subgroup G) := subgroupOfEquivOfLe inf_le_left
    have hp : IsPGroup 2 T := IsPGroup.of_injective
      (S.isPGroup'.to_le (show A⊓B≤(S : Subgroup G) from hS.le))
      eT.toMonoidHom eT.injective
    have hle : T≤pCore 2 A := le_sSup ⟨hn,hp⟩
    have hc := card_le_of_le hle
    have hh := two_mul_core_card h
    rw [hTc,←hQc] at hc
    have hpos := Nat.card_pos (α := Q A)
    omega

private theorem one_abelian_center_data (h : IsGoldschmidtTriple A B)
    (hcore : pCore 2 G=⊥) (hA : generalizedFitting A=pCore 2 A)
    (hB : generalizedFitting B=pCore 2 B)
    (hbig : 16<Nat.card (A⊓B : Subgroup G)) [IsMulCommutative (pCore 2 A)]
    (hnb : ¬ IsMulCommutative (pCore 2 B)) :
    ∃ E : Subgroup G, E≤Q A ∧ E≤centralizer ((A⊓B : Subgroup G) : Set G) ∧
      Nat.card (Q A) ≤ 4*Nat.card E ∧ Z A≤E ∧ E≤Z B := by
  let R := pCore 2 B
  let D := (Q A).subgroupOf B
  let W := D.subgroupOf R
  let J := W.map R.subtype
  let E₀ := (center R).map R.subtype
  let E := E₀.map B.subtype
  have hQAB : Q A≤B := h.local_twoCore_le_intersection.trans inf_le_right
  have hDmap : D.map B.subtype=Q A := map_subgroupOf_eq_of_le hQAB
  have hWmap : J.map B.subtype=Q A⊓Q B := by
    ext x
    constructor
    · rintro ⟨b,⟨r,hr,rfl⟩,rfl⟩
      exact ⟨hr,mem_map_of_mem B.subtype r.property⟩
    · rintro ⟨hx,⟨b,hb,rfl⟩⟩
      exact ⟨b,⟨⟨b,hb⟩,hx,rfl⟩,rfl⟩
  have hWc : Nat.card W=Nat.card (Q A⊓Q B : Subgroup G) := by
    rw [←hWmap,card_map_of_injective B.subtype_injective,
      card_map_of_injective R.subtype_injective]
  have hRc : Nat.card R=Nat.card (Q A) := by
    have hr : Nat.card (Q B)=Nat.card R := card_map_of_injective B.subtype_injective
    have ha := two_mul_core_card h
    have hb := two_mul_core_card h.symm
    rw [inf_comm B A] at hb
    omega
  have hi : W.index=2 := by
    have hh := W.index_mul_card
    have hw := core_intersection_card h hcore hbig
    rw [hWc,hRc] at hh
    have hp := Nat.card_pos (α := (Q A⊓Q B : Subgroup G))
    nlinarith
  have hnJ : ¬ J.Normal := by
    intro hn
    let := hn
    have hJle : J≤R := map_subtype_le _
    have hJindex : (J.subgroupOf R).index=2 := by
      have he : J.subgroupOf R=W := comap_map_eq_self_of_injective R.subtype_injective W
      rw [he]
      exact hi
    have hp : IsPGroup 2 (centralizer (J : Set B)) :=
      centralizer_isPGroup_of_index_two_in_core (h.symm.local_core_selfCentralizing hB) J hJindex
    have hc : centralizer (J : Set B)≤R := le_sSup ⟨inferInstance,hp⟩
    have hDJ : D≤centralizer (J : Set B) := by
      apply D.le_centralizer.trans
      apply centralizer_le
      rintro _ ⟨r,hr,rfl⟩
      exact hr
    have hQR : Q A≤Q B := by
      rw [←hDmap]
      exact map_mono (hDJ.trans hc)
    have hgen := cores_generate_of_large h hcore hbig
    rw [sup_eq_right.mpr hQR] at hgen
    have hb := two_mul_core_card h.symm
    rw [inf_comm B A,←hgen] at hb
    have hp := Nat.card_pos (α := Q B)
    omega
  have hZRle : center R≤W := center_le_abelian_index_two W hi hnb
  have hEQ : E≤Q A := by
    have he : E≤J.map B.subtype := map_mono (map_mono hZRle)
    rw [hWmap] at he
    exact he.trans inf_le_left
  have hER : E≤Q B := map_mono (map_subtype_le _)
  have hERc : E≤centralizer (Q B : Set G) := by
    rintro _ ⟨b,⟨z,hz,rfl⟩,rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨r,hr,rfl⟩
    exact congrArg (fun y : R => (y : B).val) ((mem_center_iff.mp hz) ⟨r,hr⟩)
  have hET : E≤centralizer ((A⊓B : Subgroup G) : Set G) := by
    rw [le_centralizer_iff,←cores_generate_of_large h hcore hbig]
    exact sup_le ((Q A).le_centralizer.trans (centralizer_le hEQ))
      (le_centralizer_iff.mp hERc)
  have hBE : E≤Z B := by
    let : E₀.Normal := ConjAct.normal_of_characteristic_of_normal
    let C := centralizer (E₀ : Set B)
    let T := (A⊓B).subgroupOf B
    have hTC : T≤C := by
      intro t ht
      rw [mem_centralizer_iff]
      intro e he
      apply Subtype.ext
      exact ((mem_centralizer_iff.mp
        (hET (mem_map_of_mem B.subtype he))) t ht).symm
    have hTd : T.index=3 ∧ ¬T.Normal := by
      simpa only [inf_comm B A] using local_sylow_data h.symm
    have hc : C=⊤ := by
      rcases (isCoatom_of_index_three T hTd.1).le_iff.mp hTC with hc | hc
      · exact hc
      · exact (hTd.2 (hc ▸ (inferInstance : C.Normal))).elim
    exact map_mono (centralizer_eq_top_iff_subset.mp hc)
  have hEc : Nat.card E=Nat.card (center R) := by
    rw [card_map_of_injective B.subtype_injective,card_map_of_injective R.subtype_injective]
  have hbound : Nat.card (Q A)≤4*Nat.card E := by
    rw [hEc,←hRc]
    exact center_card_bound_of_moving_abelian_index_two R W hi hnJ
  have hZAE : Z A≤E := by
    intro x hx
    obtain ⟨b,hb,hbx⟩ := center_le_other_core h hA hB hx
    refine ⟨b,?_,hbx⟩
    refine ⟨⟨b,hb⟩,?_,rfl⟩
    change (⟨b,hb⟩ : R) ∈ center R
    rw [mem_center_iff]
    intro r
    apply Subtype.ext
    apply Subtype.ext
    change (r : B).val * B.subtype b = B.subtype b * (r : B).val
    rw [hbx]
    exact mem_centralizer_iff.mp (center_centralizes A hx) r
      ((h.symm.local_twoCore_le_intersection (mem_map_of_mem B.subtype r.property)).2)
  exact ⟨E,hEQ,hET,hbound,hZAE,hBE⟩

/-- One abelian local core bounds the common Sylow group by thirty-two. -/
theorem intersection_card_le_thirty_two (h : IsGoldschmidtTriple A B)
    (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    [IsMulCommutative (pCore 2 A)] : Nat.card (A⊓B : Subgroup G)≤32 := by
  by_contra! hbig
  have h16 : 16<Nat.card (A⊓B : Subgroup G) := by omega
  by_cases hb : IsMulCommutative (pCore 2 B)
  · let := hb
    have hh := BothAbelian.intersection_card_le_sixteen h hcore hA hB
    omega
  obtain ⟨E,hEQ,hET,hcard,hZA,hEB⟩ := one_abelian_center_data h hcore hA hB h16 hb
  have hz : Z A=⊥ := le_bot_iff.mp ((center_intersection h hcore hA) ▸
    (le_inf le_rfl (hZA.trans hEB)))
  have hzc : Nat.card (center A)=1 := by
    have hc : Nat.card (Z A)=Nat.card (center A) := card_map_of_injective A.subtype_injective
    rw [←hc,hz,card_bot]
  let T := (A⊓B).subgroupOf A
  let W := E.subgroupOf A
  have hEA : E≤A := hEQ.trans (map_subtype_le _)
  have hWc : Nat.card W=Nat.card E := Nat.card_congr (subgroupOfEquivOfLe hEA).toEquiv
  have hQc : Nat.card (Q A)=Nat.card (pCore 2 A) := card_map_of_injective A.subtype_injective
  have hWQ : W≤pCore 2 A := by
    rintro x hx
    obtain ⟨a,ha,he⟩ := hEQ hx
    exact (Subtype.ext he : a=x) ▸ ha
  have hWT : W≤centralizer (T : Set A) := by
    intro w hw
    rw [mem_centralizer_iff]
    intro t ht
    apply Subtype.ext
    exact mem_centralizer_iff.mp (hET hw) t ht
  have hw : Nat.card (pCore 2 A)≤4*Nat.card W := by
    rwa [hWc,←hQc]
  have ht := local_sylow_data h
  have hbound := center_card_bound_of_quarter_subgroup (pCore 2 A) T W ht.1 ht.2 hWQ hWT hw
  rw [hzc,←hQc] at hbound
  have horder := two_mul_core_card h
  omega

/-- In the literal remaining F.6.5 branch an abelian local core forces
common Sylow order exactly thirty-two. No earlier size bound is assumed. -/
theorem remaining_source_card_thirty_two
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    [IsMulCommutative (pCore 2 A)]
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G)) (hlarge : 8<Nat.card S)
    (hns : ¬ Nonempty (S≃*Multiplicative (ZMod 2)×DihedralGroup 4)) : Nat.card S=32 := by
  have hu := intersection_card_le_thirty_two h hcore hA hB
  rw [hS] at hu
  have h16 := BothSixteen.common_sylow_card_ne_sixteen h hcore hA hB S hS hns
  obtain ⟨n,hn⟩ := S.isPGroup'.exists_card_eq
  rw [hn] at hu hlarge h16 ⊢
  have hn6 : n<6 := by
    by_contra! hge
    have hp := Nat.pow_le_pow_right (by decide : 1≤2) hge
    norm_num at hp
    omega
  interval_cases n <;> norm_num at *

/-- Above overlap order sixteen the abelian-core vertex is center-free. -/
theorem vertex_center_eq_bot_of_large (h : IsGoldschmidtTriple A B)
    (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    [IsMulCommutative (pCore 2 A)] (hlarge : 16<Nat.card (A⊓B : Subgroup G)) :
    center A=⊥ := by
  have hb : ¬ IsMulCommutative (pCore 2 B) := by
    intro hb
    let := hb
    have hh := BothAbelian.intersection_card_le_sixteen h hcore hA hB
    omega
  obtain ⟨E,_,_,_,hZA,hEB⟩ := one_abelian_center_data h hcore hA hB hlarge hb
  have hz : Z A=⊥ := le_bot_iff.mp ((center_intersection h hcore hA) ▸
    (le_inf le_rfl (hZA.trans hEB)))
  apply map_injective A.subtype_injective
  simpa only [Subgroup.map_bot] using hz

end CFSG.Quasithin.ChapterF.SourceAssembly.OneAbelian
