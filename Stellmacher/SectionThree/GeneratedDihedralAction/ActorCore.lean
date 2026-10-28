module

public import Stellmacher.SectionThree.GeneratedDihedralAction.Image

/-!
# The actor coatom is the actor's two-core intersection

The central actor image is a normal two-subgroup of the generated quotient
image, so its full preimage is a normal two-subgroup as well. Conversely,
the two-core image centralizes the normal odd rotation subgroup; it cannot
contain the distinguished reflection. The index-two actor coatom therefore
equals the intersection of the actor with the generated group's two-core.
This is the core identification in Stellmacher (7.8)(a), p. 36.
-/

open scoped IsMulCommutative

namespace Stellmacher.SectionThree

private theorem eq_inf_of_index_two_of_le_of_not_mem
    {G : Type*} [Group G] [Finite G]
    (A A₀ K : Subgroup G) (hA₀A : A₀ ≤ A) (hA₀K : A₀ ≤ K)
    (hindex : Nat.card A = 2 * Nat.card A₀)
    (a : G) (ha : a ∈ A) (haK : a ∉ K) : A₀ = A ⊓ K := by
  let B := A ⊓ K
  have hBne : B ≠ A := by
    intro heq
    exact haK ((heq.symm ▸ ha : a ∈ B).2)
  have hcardB : Nat.card B < Nat.card A := by
    apply lt_of_le_of_ne (Subgroup.card_le_of_le (show B ≤ A from inf_le_left))
    intro heq
    exact hBne (Subgroup.eq_of_le_of_card_ge inf_le_left heq.symm.le)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (show B ≤ A from inf_le_left)
  have hk2 : 2 ≤ k := by
    have hBpos : 0 < Nat.card B := Nat.card_pos
    by_contra hk2
    interval_cases k <;> simp_all
  have hcard : Nat.card B ≤ Nat.card A₀ := by nlinarith
  exact Subgroup.eq_of_le_of_card_ge (le_inf hA₀A hA₀K) hcard

public theorem extracted_actor_eq_core_intersection
    {G : Type*} [Group G] [Finite G]
    (P T A : Subgroup G) (hAP : A ≤ P) (a : G) (haA : a ∈ A)
    (d : PrimitiveDihedralExtractionData P T A hAP a haA)
    (hAelem : IsElementaryAbelian 2
      ((A.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)))) :
    d.A₀ = A ⊓ twoCoreAmbient (A ⊔ A.conjBy (d.x : G)) := by
  classical
  let q := QuotientGroup.mk' (pCore 2 P)
  let AP := A.subgroupOf P
  let LP := AP ⊔ AP.conjBy d.x
  let L := LP.map P.subtype
  have hLgen : L = A ⊔ A.conjBy (d.x : G) :=
    (generated_inside_and_quotient_image P A hAP d.x).1
  have hLP : L ≤ P := Subgroup.map_subtype_le LP
  have hAL : A ≤ L := by rw [hLgen]; exact le_sup_left
  let f₀ : L →* P ⧸ pCore 2 P := q.comp (Subgroup.inclusion hLP)
  let J := f₀.range
  let f : L →* J := f₀.rangeRestrict
  have hf : Function.Surjective f := f₀.rangeRestrict_surjective
  have hJ : J = (L.subgroupOf P).map q := by
    ext z
    constructor
    · rintro ⟨l, rfl⟩
      exact Subgroup.mem_map_of_mem q l.property
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨(l : G), hl⟩, rfl⟩
  let R := (d.F₀.subgroupOf P).map q
  let Ab := AP.map q
  let C := (d.A₀.subgroupOf P).map q
  have hgen : J = R ⊔ Ab := by
    rw [hJ, subgroupOf_map_subtype_eq]
    exact extracted_generated_quotient_image P T A hAP a haA d hAelem
  have hF : d.F₀ = twoResidualAmbient L := by
    rw [hLgen]
    exact d.residual_generated
  have hRdata : R ≤ J ∧ (R.subgroupOf J).Normal := by
    rw [hJ]
    simpa only [R, hF] using residual_image_normal P L hLP
  have hCAb : C ≤ Ab := Subgroup.map_mono (Subgroup.subgroupOf_mono P d.A₀_le)
  have hCJ : C ≤ J := by rw [hgen]; exact hCAb.trans le_sup_right
  have hAcomm (x y : P ⧸ pCore 2 P) (hx : x ∈ Ab) (hy : y ∈ Ab) :
      x * y = y * x := by
    let _ : IsElementaryAbelian 2 Ab := hAelem
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : Ab) ⟨y, hy⟩)
  have hJcentral : J ≤ Subgroup.centralizer (C : Set (P ⧸ pCore 2 P)) := by
    rw [hgen]
    apply sup_le
    · intro r hr
      apply Subgroup.mem_centralizer_iff.mpr
      rintro c ⟨b, hb, rfl⟩
      exact d.A₀_centralizes_rotation b hb r hr
    · intro b hb
      exact Subgroup.mem_centralizer_iff.mpr (fun c hc => hAcomm c b (hCAb hc) hb)
  let Cj := C.subgroupOf J
  have hCjnormal : Cj.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCJ).mpr
      (hJcentral.trans (Subgroup.centralizer_le_normalizer _))
  let _ : Cj.Normal := hCjnormal
  have hC2 : IsPGroup 2 C := by
    let _ : IsElementaryAbelian 2 Ab := hAelem
    exact IsPGroup.to_le (IsElementaryAbelian.isPGroup 2 Ab) hCAb
  have hker2 : IsPGroup 2 f.ker := by
    let I := (pCore 2 P).comap (Subgroup.inclusion hLP)
    have hI2 : IsPGroup 2 I := pCore_isPGroup.comap_of_injective
      (Subgroup.inclusion hLP) (Subgroup.inclusion_injective hLP)
    apply IsPGroup.to_le hI2
    intro k hk
    exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hLP k)).mp
      (congrArg Subtype.val (MonoidHom.mem_ker.mp hk))
  have hN2 : IsPGroup 2 (Cj.comap f) := hC2.comap_subtype.comap_of_ker_isPGroup f hker2
  have hNcore : Cj.comap f ≤ pCore 2 L :=
    le_sSup ⟨inferInstance, hN2⟩
  have hA₀core : d.A₀ ≤ twoCoreAmbient L := by
    intro b hb
    let bL : L := ⟨b, hAL (d.A₀_le hb)⟩
    have hbN : bL ∈ Cj.comap f :=
      Subgroup.mem_map_of_mem q (show (⟨b, hLP bL.property⟩ : P) ∈
        d.A₀.subgroupOf P from hb)
    exact Subgroup.mem_map_of_mem L.subtype (hNcore hbN)
  have haCore : a ∉ twoCoreAmbient L := by
    intro haCore
    let aL : L := ⟨a, hAL haA⟩
    have haLcore : aL ∈ pCore 2 L := by
      obtain ⟨b, hb, hba⟩ := haCore
      have heq : b = aL := Subtype.ext hba
      exact heq ▸ hb
    let D := (pCore 2 L).map f
    have hDn : D.Normal := pCore_normal.map f hf
    have hD2 : IsPGroup 2 D := pCore_isPGroup.map f
    let Rj := R.subgroupOf J
    have hRjp : IsPGroup d.p Rj := (IsPGroup.of_card d.rotation_card).comap_subtype
    have hdis : Disjoint D Rj :=
      hD2.disjoint_of_coprime hRjp d.odd_p.coprime_two_right.symm
    have hrot : q d.x ∈ R := by rw [show R = Subgroup.zpowers (q d.x) from d.rotation_eq]; exact Subgroup.mem_zpowers _
    let zJ : J := ⟨q d.x, hRdata.1 hrot⟩
    have hcommJ := Subgroup.commute_of_normal_of_disjoint D Rj hDn hRdata.2 hdis
      (f aL) zJ (Subgroup.mem_map_of_mem f haLcore) hrot
    have hcomm : q (⟨a, hAP haA⟩ : P) * q d.x = q d.x * q ⟨a, hAP haA⟩ :=
      congrArg Subtype.val hcommJ.eq
    have hinv := d.reflected (q d.x) hrot
    have hzInv : q d.x = (q d.x)⁻¹ := by
      calc
        q d.x = q ⟨a, hAP haA⟩ * q d.x * (q ⟨a, hAP haA⟩)⁻¹ := by rw [hcomm]; simp
        _ = (q d.x)⁻¹ := hinv
    have hzsq : (q d.x) ^ 2 = 1 := by
      simpa [pow_two] using congrArg (fun t => q d.x * t) hzInv
    have hzOne : q d.x = 1 := by
      let zR : R := ⟨q d.x, hrot⟩
      have hzR : zR ^ 2 = 1 := Subtype.ext hzsq
      have hRp : IsPGroup d.p R := IsPGroup.of_card d.rotation_card
      have heq : zR = 1 := (hRp.powEquiv d.odd_p.coprime_two_right).injective
        (by simpa using hzR)
      exact congrArg Subtype.val heq
    have hRbot : R = ⊥ := by rw [show R = Subgroup.zpowers (q d.x) from d.rotation_eq, hzOne]; simp
    have hcard : Nat.card R = 1 := by rw [hRbot]; exact Subgroup.card_bot
    have hgt : 1 < Nat.card R := by
      rw [show Nat.card R = d.p ^ d.n from d.rotation_card]
      exact Nat.one_lt_pow (Nat.ne_of_gt d.n_pos) d.prime_p.one_lt
    omega
  rw [← hLgen]
  exact eq_inf_of_index_two_of_le_of_not_mem A d.A₀ (twoCoreAmbient L)
    d.A₀_le hA₀core d.A₀_index_two a haA haCore

end Stellmacher.SectionThree
