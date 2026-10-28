module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.OrderTwo.Lift
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryPair

/-!
# The largest elementary family in the contrary order-two branch

Source: Aschbacher--Smith, proof of Lemma 2.5.24, printed p.568.  The
faithful action on `S ∩ K` identifies the two inner Klein four-groups, while
the kernel on `S` is the central subgroup `S_C` of order two.  The elementary
rank bound in the actual `Aut(A₆)` Sylow image therefore gives the complete
order-sixteen family.  The relative centralizer of either inner four-group is
the corresponding lifted sixteen-group.
-/

@[expose] public section

open Subgroup AlternatingSix.ShadowLocal
open CFSG.Quasithin.Chapter2.A6Shadow.Frattini
open CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore
open scoped Pointwise

namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.OrderTwo
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

namespace ModelFacts

open AlternatingSix.ShadowLocal.Holomorph

private theorem zero_eq_transposition_sup_klein :
    Holomorph.ElementaryPair.zero = transpositionSubgroup ⊔ kleinZero := by
  apply le_antisymm
  · rintro x ⟨i, rfl⟩
    exact mul_mem_sup
      ((mem_transpositionSubgroup _).mpr ⟨i.1, rfl⟩)
      ((mem_kleinZero _).mpr ⟨i.2, rfl⟩)
  · apply sup_le
    · rintro x hx
      obtain ⟨i, hi⟩ := (mem_transpositionSubgroup x).mp hx
      rw [← hi]
      exact ⟨(i, 1), by
        change transpositionEmbedding i * kleinZeroEmbedding 1 = _
        simp⟩
    · change kleinZero ≤ Holomorph.ElementaryPair.zero
      rintro x hx
      obtain ⟨i, hi⟩ := (mem_kleinZero x).mp hx
      rw [← hi]
      exact ⟨(1, i), by
        change transpositionEmbedding 1 * kleinZeroEmbedding i = _
        simp⟩

private theorem one_eq_transposition_sup_klein :
    Holomorph.ElementaryPair.one = transpositionSubgroup ⊔ kleinOne := by
  apply le_antisymm
  · rintro x ⟨i, rfl⟩
    exact mul_mem_sup
      ((mem_transpositionSubgroup _).mpr ⟨i.1, rfl⟩)
      ((mem_kleinOne _).mpr ⟨i.2, rfl⟩)
  · apply sup_le
    · rintro x hx
      obtain ⟨i, hi⟩ := (mem_transpositionSubgroup x).mp hx
      rw [← hi]
      exact ⟨(i, 1), by
        change transpositionEmbedding i * kleinOneEmbedding 1 = _
        simp⟩
    · change kleinOne ≤ Holomorph.ElementaryPair.one
      rintro x hx
      obtain ⟨i, hi⟩ := (mem_kleinOne x).mp hx
      rw [← hi]
      exact ⟨(1, i), by
        change transpositionEmbedding 1 * kleinOneEmbedding i = _
        simp⟩

theorem zero_eq_transposition_sup_klein_public :
    Holomorph.ElementaryPair.zero = transpositionSubgroup ⊔ kleinZero :=
  zero_eq_transposition_sup_klein

theorem one_eq_transposition_sup_klein_public :
    Holomorph.ElementaryPair.one = transpositionSubgroup ⊔ kleinOne :=
  one_eq_transposition_sup_klein

theorem centralizer_zero :
    centralizer (kleinZero : Set Holomorph.Model) = Holomorph.ElementaryPair.zero := by
  rw [Holomorph.ElementaryPair.zero]
  ext x
  simp only [mem_centralizer_iff, SetLike.mem_coe, MonoidHom.mem_range, mem_kleinZero]
  revert x
  decide +kernel

theorem centralizer_one :
    centralizer (kleinOne : Set Holomorph.Model) = Holomorph.ElementaryPair.one := by
  rw [Holomorph.ElementaryPair.one]
  ext x
  simp only [mem_centralizer_iff, SetLike.mem_coe, MonoidHom.mem_range, mem_kleinOne]
  revert x
  decide +kernel

end ModelFacts

private theorem map_centralizer_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (U : Subgroup A) :
    (centralizer (U : Set A)).map e.toMonoidHom =
      centralizer (U.map e.toMonoidHom : Set B) := by
  ext x
  obtain ⟨x, rfl⟩ := e.surjective x
  simp only [mem_map_equiv, MulEquiv.symm_apply_apply, mem_centralizer_iff,
    SetLike.mem_coe]
  constructor
  · intro hx y hy
    obtain ⟨y, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (hx y (by simpa using hy))
  · intro hx y hy
    apply e.injective
    simpa only [map_mul] using hx (e y) (by simpa using hy)

private theorem transposition_card (P : Sylow 2 AutA6) :
    Nat.card (SylowGeometry.transpositionSubgroup P) = 2 := by
  change Nat.card (Holomorph.transpositionSubgroup.map
    (Identification.sylowEquiv P).toMonoidHom) = 2
  rw [card_map_of_injective (Identification.sylowEquiv P).injective,
    Holomorph.transpositionSubgroup, Nat.card_zpowers]
  apply orderOf_eq_prime (p := 2)
  · exact Holomorph.transposition_sq
  · decide +kernel

private theorem centralizer_kleinZero_card (P : Sylow 2 AutA6) :
    Nat.card (centralizer (SylowGeometry.kleinZero P : Set P)) = 8 := by
  have h := map_centralizer_equiv (Identification.sylowEquiv P)
    Holomorph.kleinZero
  rw [ModelFacts.centralizer_zero] at h
  change Holomorph.ElementaryPair.zero.map
      (Identification.sylowEquiv P).toMonoidHom =
      centralizer (SylowGeometry.kleinZero P : Set P) at h
  rw [← h, card_map_of_injective (Identification.sylowEquiv P).injective,
    Holomorph.ElementaryPair.card_zero]

private theorem centralizer_kleinOne_card (P : Sylow 2 AutA6) :
    Nat.card (centralizer (SylowGeometry.kleinOne P : Set P)) = 8 := by
  have h := map_centralizer_equiv (Identification.sylowEquiv P)
    Holomorph.kleinOne
  rw [ModelFacts.centralizer_one] at h
  change Holomorph.ElementaryPair.one.map
      (Identification.sylowEquiv P).toMonoidHom =
      centralizer (SylowGeometry.kleinOne P : Set P) at h
  rw [← h, card_map_of_injective (Identification.sylowEquiv P).injective,
    Holomorph.ElementaryPair.card_one]

private theorem toImage_mem_inner (d : EarlierSetup κ G) (a : G)
    (haS : a ∈ d.S) (haK : a ∈ d.K) :
    d.toImageSylow ⟨a, haS⟩ ∈ sylowInner d.imageSylow := by
  change d.action ⟨a, d.s_le_h haS⟩ ∈ AlternatingSix.ShadowLocal.inner
  rw [d.action_on_K ⟨a, haK⟩]
  exact ⟨_, rfl⟩

private theorem toImage_eq_innerEquiv (d : EarlierSetup κ G)
    (a : (d.S ⊓ d.K : Subgroup G)) :
    d.toImageSylow ⟨a, a.property.1⟩ = innerEquiv d a := rfl

private theorem toImage_map_eq_imageInner (d : EarlierSetup κ G)
    (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) :
    (E.subgroupOf d.S).map d.toImageSylow = imageInner d E := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    let aI : (d.S ⊓ d.K : Subgroup G) :=
      ⟨(a : G), ⟨a.property, (hE ha).2⟩⟩
    change d.toImageSylow a ∈
      ((E.subgroupOf (d.S ⊓ d.K)).map (innerEquiv d).toMonoidHom).map
        (sylowInner d.imageSylow).subtype
    have haeq : d.toImageSylow a =
        (sylowInner d.imageSylow).subtype (innerEquiv d aI) := by
      exact toImage_eq_innerEquiv d aI
    rw [haeq]
    apply mem_map_of_mem (sylowInner d.imageSylow).subtype
    apply mem_map_of_mem (innerEquiv d).toMonoidHom
    exact ha
  · rintro ⟨a, ha, rfl⟩
    rcases ha with ⟨b, hb, rfl⟩
    exact ⟨⟨b, b.property.1⟩, hb, toImage_eq_innerEquiv d b⟩

private theorem model_transposition_mem_of_centralizer
    (u : Holomorph.Model) (huC : u ∈ centralizer (Holomorph.innerD : Set Holomorph.Model))
    : u ∈ Holomorph.centralTwo ⊔ Holomorph.transpositionSubgroup := by
  rw [← Holomorph.centralizer_innerD]
  exact huC

private def vImage (d : EarlierSetup κ G) (v : CentralizingInvolution d) :
    d.imageSylow := d.toImageSylow ⟨v.element, v.mem_s⟩

private theorem vImage_centralizes_inner (d : EarlierSetup κ G)
    (v : CentralizingInvolution d) :
    vImage d v ∈ centralizer (sylowInner d.imageSylow : Set d.imageSylow) := by
  intro a ha
  let aI : sylowInner d.imageSylow := ⟨a, ha⟩
  obtain ⟨k, hk⟩ := innerAction_surjective d aI
  have hkg : (k : G) ∈ d.S ⊓ d.K := k.property
  have hcomm : (k : G) * v.element = v.element * (k : G) :=
    v.centralizes (k : G) hkg
  have hcomm' :
      (⟨k, k.property.1⟩ : d.S) * ⟨v.element, v.mem_s⟩ =
        ⟨v.element, v.mem_s⟩ * ⟨k, k.property.1⟩ := by
    exact Subtype.ext (by simpa using hcomm)
  have hmap := congrArg d.toImageSylow hcomm'
  have hka : d.toImageSylow ⟨k, k.property.1⟩ = a := congrArg Subtype.val hk
  simpa only [vImage, hka, map_mul] using hmap

private theorem vImage_not_inner (d : EarlierSetup κ G)
    (v : CentralizingInvolution d) :
    vImage d v ∉ sylowInner d.imageSylow := by
  intro hu
  obtain ⟨k, hk⟩ := innerAction_surjective d ⟨vImage d v, hu⟩
  have hEq : d.toImageSylow ⟨k, k.property.1⟩ = vImage d v :=
    congrArg Subtype.val hk
  have hker :
      (⟨v.element, v.mem_s⟩ : d.S) * ⟨k, k.property.1⟩⁻¹ ∈
        d.toImageSylow.ker := by
    rw [MonoidHom.mem_ker]
    have hm : d.toImageSylow ⟨v.element, v.mem_s⟩ *
        (d.toImageSylow ⟨k, k.property.1⟩)⁻¹ = 1 := by
      rw [hEq]
      exact mul_inv_cancel _
    simpa only [map_mul, map_inv] using hm
  rw [d.toImageSylow_kernel] at hker
  have hSC : v.element * (k : G)⁻¹ ∈ d.SC := hker
  have hprod : (v.element * (k : G)⁻¹) * (k : G) ∈ d.SC ⊔ d.K :=
    (d.SC ⊔ d.K).mul_mem
      ((le_sup_left : d.SC ≤ d.SC ⊔ d.K) hSC)
      ((le_sup_right : d.K ≤ d.SC ⊔ d.K) k.property.2)
  apply v.outside
  simpa only [sup_comm, mul_assoc, inv_mul_cancel, mul_one] using hprod

private theorem vImage_mem_center_sup_transposition (d : EarlierSetup κ G)
    (v : CentralizingInvolution d) :
    vImage d v ∈ center d.imageSylow ⊔
      SylowGeometry.transpositionSubgroup d.imageSylow := by
  let e := Identification.sylowEquiv d.imageSylow
  have huC : e.symm (vImage d v) ∈
      centralizer (Holomorph.innerD : Set Holomorph.Model) := by
    have hmap := map_centralizer_equiv e Holomorph.innerD
    rw [Identification.sylowEquiv_innerD] at hmap
    have h := vImage_centralizes_inner d v
    rw [← hmap] at h
    exact (mem_map_equiv.mp h)
  have ht := model_transposition_mem_of_centralizer (e.symm (vImage d v)) huC
  have hm := mem_map_of_mem e.toMonoidHom ht
  have hcenter : Holomorph.centralTwo.map e.toMonoidHom = center d.imageSylow := by
    rw [Holomorph.centralTwo, MonoidHom.map_zpowers]
    change zpowers (e (Holomorph.rotation ^ 4)) = center d.imageSylow
    exact (SylowGeometry.center_eq d.imageSylow).symm
  rw [Subgroup.map_sup, hcenter] at hm
  change vImage d v ∈ center d.imageSylow ⊔
    Holomorph.transpositionSubgroup.map e.toMonoidHom
  have heq : e.toMonoidHom (e.symm (vImage d v)) = vImage d v :=
    e.apply_symm_apply _
  rw [heq] at hm
  exact hm

private theorem relativeCentralizer_card_le (d : EarlierSetup κ G)
    (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) (hcard : Nat.card d.SC = 2)
    [IsKleinFour E] :
    Nat.card (d.S ⊓ centralizer (E : Set G) : Subgroup G) ≤ 16 := by
  let C : Subgroup G := d.S ⊓ centralizer (E : Set G)
  let CS : Subgroup d.S := C.subgroupOf d.S
  have hCS : CS ≤ centralizer ((E.subgroupOf d.S : Subgroup d.S) : Set d.S) := by
    intro a ha b hb
    exact Subtype.ext (ha.2 (b : G) hb)
  have hmap : CS.map d.toImageSylow ≤
      centralizer ((E.subgroupOf d.S).map d.toImageSylow : Set d.imageSylow) := by
    exact (map_mono hCS).trans (map_centralizer_le_centralizer_image
      (E.subgroupOf d.S : Set d.S) d.toImageSylow)
  have himage : (E.subgroupOf d.S).map d.toImageSylow = imageInner d E :=
    toImage_map_eq_imageInner d E hE
  have hcardmap : Nat.card (CS.map d.toImageSylow) ≤ 8 := by
    rw [himage] at hmap
    have hfour : E = fourZero d ∨ E = fourOne d :=
      four_subgroups d E hE
    rcases hfour with rfl | rfl
    · rw [fourZero, imageInner_liftInner d _
        (SylowGeometry.kleinZero_le_inner d.imageSylow)] at hmap
      exact (card_le_of_le hmap).trans_eq (centralizer_kleinZero_card d.imageSylow)
    · rw [fourOne, imageInner_liftInner d _
        (SylowGeometry.kleinOne_le_inner d.imageSylow)] at hmap
      exact (card_le_of_le hmap).trans_eq (centralizer_kleinOne_card d.imageSylow)
  have hker : d.toImageSylow.ker ≤ CS := by
    rw [d.toImageSylow_kernel]
    intro a ha
    have hSC : d.SC ≤ centralizer (E : Set G) :=
      (d.centralizer_K ▸ inf_le_right).trans
        (centralizer_le (hE.trans inf_le_right))
    exact ⟨a.property, hSC ha⟩
  have hmul := (d.toImageSylow.ker.subgroupOf CS).index_mul_card
  have hker_card : Nat.card (d.toImageSylow.ker.subgroupOf CS) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hker).toEquiv]
    rw [d.toImageSylow_kernel]
    rw [Nat.card_congr (subgroupOfEquivOfLe d.sc_le_s).toEquiv]
    exact hcard
  change d.toImageSylow.ker.relIndex CS *
      Nat.card (d.toImageSylow.ker.subgroupOf CS) = Nat.card CS at hmul
  rw [relIndex_ker, hker_card] at hmul
  have hCS_card : Nat.card CS ≤ 16 := by omega
  have hcongr : Nat.card CS = Nat.card C :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← hcongr]
  exact hCS_card

theorem localCore_eq_liftedFour (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) (hcard : Nat.card d.SC = 2)
    (hcore : ∀ E : Subgroup G, E ≤ d.S ⊓ d.K → IsKleinFour E →
      localCore d E = d.S ⊓ centralizer (E : Set G))
    (v : CentralizingInvolution d) (E : Subgroup G)
    (hE : E ≤ d.S ⊓ d.K) [IsKleinFour E] :
    localCore d E = liftedFour d v E := by
  rw [hcore E hE inferInstance]
  have hle : liftedFour d v E ≤ d.S ⊓ centralizer (E : Set G) :=
    liftedFour_le_relativeCentralizer d v E hE
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [(liftedFour_elementary_card d hEA hcard v E hE).2]
  exact relativeCentralizer_card_le d E hE hcard

private theorem elementary_card_le_sixteen (d : EarlierSetup κ G)
    (F : Subgroup G) (hF : F ≤ d.S) (hcard : Nat.card d.SC = 2)
    [IsElementaryAbelian 2 F] : Nat.card F ≤ 16 := by
  let FS : Subgroup d.S := F.subgroupOf d.S
  let g : FS →* d.imageSylow := d.toImageSylow.comp FS.subtype
  let : IsElementaryAbelian 2 FS := IsElementaryAbelian.subgroupOf hF
  let : IsElementaryAbelian 2 (⊤ : Subgroup FS) :=
    by
      rw [← Subgroup.subgroupOf_self FS]
      exact IsElementaryAbelian.subgroupOf (p := 2) (H := FS) (K := FS) le_rfl
  let I : Subgroup d.imageSylow := (⊤ : Subgroup FS).map g
  let : IsElementaryAbelian 2 I := IsElementaryAbelian.map g
  let J : Subgroup AutA6 := I.map (d.imageSylow : Subgroup AutA6).subtype
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.map _
  have hmapJ : Nat.card J ≤ 8 :=
    AlternatingSix.ShadowLocal.elementary_card_le_eight J
  have hmap : Nat.card I ≤ 8 := by
    rw [card_map_of_injective (d.imageSylow : Subgroup AutA6).subtype_injective] at hmapJ
    exact hmapJ
  have hker_map : g.ker.map (d.S.subtype.comp FS.subtype) ≤ d.SC := by
    rintro x ⟨a, ha, rfl⟩
    have ha' : d.toImageSylow (FS.subtype a) = 1 := by
      rw [← MonoidHom.mem_ker]
      exact ha
    rw [← MonoidHom.mem_ker, d.toImageSylow_kernel] at ha'
    exact ha'
  have hker_card : Nat.card g.ker ≤ 2 := by
    calc
      Nat.card g.ker = Nat.card (g.ker.map (d.S.subtype.comp FS.subtype)) :=
        (card_map_of_injective (f := d.S.subtype.comp FS.subtype)
          (d.S.subtype_injective.comp FS.subtype_injective)).symm
      _ ≤ Nat.card d.SC := card_le_of_le hker_map
      _ = 2 := hcard
  have hmul := g.ker.index_mul_card
  rw [← relIndex_top_right] at hmul
  rw [relIndex_ker] at hmul
  change Nat.card I * Nat.card g.ker = Nat.card FS at hmul
  have hprod : Nat.card I * Nat.card g.ker ≤ 8 * 2 :=
    Nat.mul_le_mul hmap hker_card
  have hFS_card : Nat.card FS ≤ 16 := by
    rw [← hmul]
    calc
      Nat.card I * Nat.card g.ker ≤ 8 * 2 := hprod
      _ = 16 := by norm_num
  rw [← Nat.card_congr (subgroupOfEquivOfLe hF).toEquiv]
  exact hFS_card

private theorem sImage_card_le_eight (d : EarlierSetup κ G)
    (F : Subgroup G) (hF : F ≤ d.S)
    [IsElementaryAbelian 2 F] :
    Nat.card ((F.subgroupOf d.S).map d.toImageSylow) ≤ 8 := by
  let FS : Subgroup d.S := F.subgroupOf d.S
  let g : FS →* d.imageSylow := d.toImageSylow.comp FS.subtype
  let : IsElementaryAbelian 2 FS := IsElementaryAbelian.subgroupOf hF
  let : IsElementaryAbelian 2 (⊤ : Subgroup FS) := by
    rw [← Subgroup.subgroupOf_self FS]
    exact IsElementaryAbelian.subgroupOf (p := 2) (H := FS) (K := FS) le_rfl
  let I : Subgroup d.imageSylow := (⊤ : Subgroup FS).map g
  let : IsElementaryAbelian 2 I := IsElementaryAbelian.map g
  let J : Subgroup AutA6 := I.map (d.imageSylow : Subgroup AutA6).subtype
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.map _
  have hmapJ : Nat.card J ≤ 8 :=
    AlternatingSix.ShadowLocal.elementary_card_le_eight J
  have hmap : Nat.card I ≤ 8 := by
    rw [card_map_of_injective (d.imageSylow : Subgroup AutA6).subtype_injective] at hmapJ
    exact hmapJ
  simpa [I, FS, g] using hmap

private theorem centralizer_eq_elementaryPair_zero (d : EarlierSetup κ G) :
    centralizer (SylowGeometry.kleinZero d.imageSylow : Set d.imageSylow) =
      AlternatingSix.ShadowLocal.ElementaryPair.zero d.imageSylow := by
  have h := map_centralizer_equiv (Identification.sylowEquiv d.imageSylow)
    Holomorph.kleinZero
  rw [ModelFacts.centralizer_zero] at h
  change Holomorph.ElementaryPair.zero.map
      (Identification.sylowEquiv d.imageSylow).toMonoidHom =
      centralizer (SylowGeometry.kleinZero d.imageSylow : Set d.imageSylow) at h
  exact h.symm

private theorem centralizer_eq_elementaryPair_one (d : EarlierSetup κ G) :
    centralizer (SylowGeometry.kleinOne d.imageSylow : Set d.imageSylow) =
      AlternatingSix.ShadowLocal.ElementaryPair.one d.imageSylow := by
  have h := map_centralizer_equiv (Identification.sylowEquiv d.imageSylow)
    Holomorph.kleinOne
  rw [ModelFacts.centralizer_one] at h
  change Holomorph.ElementaryPair.one.map
      (Identification.sylowEquiv d.imageSylow).toMonoidHom =
      centralizer (SylowGeometry.kleinOne d.imageSylow : Set d.imageSylow) at h
  exact h.symm

private theorem sImage_card_of_sixteen (d : EarlierSetup κ G)
    (A : Subgroup G) (hA : A ≤ d.S) (hSC : d.SC ≤ A)
    (hAc : Nat.card A = 16) (hcard : Nat.card d.SC = 2) :
    Nat.card ((A.subgroupOf d.S).map d.toImageSylow) = 8 := by
  let AS : Subgroup d.S := A.subgroupOf d.S
  have hAS : Nat.card AS = 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv]
    exact hAc
  have hSCAS : (d.SC.subgroupOf d.S).subgroupOf AS =
      d.toImageSylow.ker.subgroupOf AS := by
    rw [d.toImageSylow_kernel]
  have hker : Nat.card (d.toImageSylow.ker.subgroupOf AS) = 2 := by
    rw [← hSCAS]
    calc
      Nat.card ((d.SC.subgroupOf d.S).subgroupOf AS) =
          Nat.card (d.SC.subgroupOf d.S) :=
        Nat.card_congr (subgroupOfEquivOfLe (by
          intro x hx
          exact hSC hx)).toEquiv
      _ = 2 := by
        rw [Nat.card_congr (subgroupOfEquivOfLe d.sc_le_s).toEquiv]
        exact hcard
  have hmul := (d.toImageSylow.ker.subgroupOf AS).index_mul_card
  change d.toImageSylow.ker.relIndex AS *
      Nat.card (d.toImageSylow.ker.subgroupOf AS) = Nat.card AS at hmul
  rw [relIndex_ker, hker, hAS] at hmul
  norm_num [Nat.mul_comm] at hmul
  have hraw : Nat.card {x : d.imageSylow //
      ∃ a, ∃ b : a ∈ d.S, ⟨a, b⟩ ∈ AS ∧ d.toImageSylow ⟨a, b⟩ = x} = 8 := by
    apply Nat.eq_of_mul_eq_mul_left (n := 2) (m := _)
      (k := 8) (by norm_num)
    calc
      2 * Nat.card {x : d.imageSylow //
          ∃ a, ∃ b : a ∈ d.S, ⟨a, b⟩ ∈ AS ∧ d.toImageSylow ⟨a, b⟩ = x} = 16 := hmul
      _ = 2 * 8 := by norm_num
  have hset : (AS.map d.toImageSylow : Set d.imageSylow) =
      {x | ∃ a, ∃ b : a ∈ d.S, ⟨a, b⟩ ∈ AS ∧ d.toImageSylow ⟨a, b⟩ = x} := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, a.property, ha, rfl⟩
    · rintro ⟨a, b, ha, rfl⟩
      exact ⟨⟨a, b⟩, ha, rfl⟩
  change Nat.card {x : d.imageSylow // x ∈ (AS.map d.toImageSylow : Set d.imageSylow)} = 8
  rw [hset]
  exact hraw

private theorem sImage_le_centralizer (d : EarlierSetup κ G)
    (A E : Subgroup G) (_hA : A ≤ d.S)
    (_hE : E ≤ d.S ⊓ d.K)
    (hAE : A ≤ centralizer (E : Set G)) :
    (A.subgroupOf d.S).map d.toImageSylow ≤
      centralizer ((E.subgroupOf d.S).map d.toImageSylow : Set d.imageSylow) := by
  rintro y ⟨a, ha, rfl⟩ z hz
  rcases hz with ⟨b, hb, rfl⟩
  have haA : (a : G) ∈ A := ha
  have hbE : (b : G) ∈ E := hb
  have hab : (b : G) * (a : G) = (a : G) * (b : G) :=
    (hAE haA) (b : G) hbE
  simpa only [map_mul] using
    congrArg d.toImageSylow (show b * a = a * b by exact Subtype.ext hab)

private theorem sImage_eq_pair_zero (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) (hcard : Nat.card d.SC = 2)
    (v : CentralizingInvolution d) :
    Nat.card (((liftedFour d v (fourZero d)).subgroupOf d.S).map d.toImageSylow) = 8 := by
  apply sImage_card_of_sixteen d _ (liftedFour_le_s d v _ (fourZero_le d))
    le_sup_left
  · exact (liftedFour_elementary_card d hEA hcard v _ (fourZero_le d)).2
  · exact hcard

private theorem sImage_eq_pair_one (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) (hcard : Nat.card d.SC = 2)
    (v : CentralizingInvolution d) :
    Nat.card (((liftedFour d v (fourOne d)).subgroupOf d.S).map d.toImageSylow) = 8 := by
  apply sImage_card_of_sixteen d _ (liftedFour_le_s d v _ (fourOne_le d))
    le_sup_left
  · exact (liftedFour_elementary_card d hEA hcard v _ (fourOne_le d)).2
  · exact hcard

private theorem sImage_liftedFour_eq_pair_zero (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) (hcard : Nat.card d.SC = 2)
    (v : CentralizingInvolution d) :
    ((liftedFour d v (fourZero d)).subgroupOf d.S).map d.toImageSylow =
      AlternatingSix.ShadowLocal.ElementaryPair.zero d.imageSylow := by
  have hle := sImage_le_centralizer d (liftedFour d v (fourZero d))
    (fourZero d) (liftedFour_le_s d v _ (fourZero_le d)) (fourZero_le d)
    ((liftedFour_le_relativeCentralizer d v _ (fourZero_le d)).trans inf_le_right)
  have hE : ((fourZero d).subgroupOf d.S).map d.toImageSylow =
      SylowGeometry.kleinZero d.imageSylow := by
    rw [toImage_map_eq_imageInner d _ (fourZero_le d)]
    change imageInner d (liftInner d (SylowGeometry.kleinZero d.imageSylow)) = _
    rw [imageInner_liftInner d _ (SylowGeometry.kleinZero_le_inner d.imageSylow)]
  rw [hE] at hle
  rw [centralizer_eq_elementaryPair_zero d] at hle
  apply eq_of_le_of_card_ge hle
  rw [AlternatingSix.ShadowLocal.ElementaryPair.card_zero d.imageSylow]
  exact le_of_eq (sImage_eq_pair_zero d hEA hcard v).symm

private theorem sImage_liftedFour_eq_pair_one (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) (hcard : Nat.card d.SC = 2)
    (v : CentralizingInvolution d) :
    ((liftedFour d v (fourOne d)).subgroupOf d.S).map d.toImageSylow =
      AlternatingSix.ShadowLocal.ElementaryPair.one d.imageSylow := by
  have hle := sImage_le_centralizer d (liftedFour d v (fourOne d))
    (fourOne d) (liftedFour_le_s d v _ (fourOne_le d)) (fourOne_le d)
    ((liftedFour_le_relativeCentralizer d v _ (fourOne_le d)).trans inf_le_right)
  have hE : ((fourOne d).subgroupOf d.S).map d.toImageSylow =
      SylowGeometry.kleinOne d.imageSylow := by
    rw [toImage_map_eq_imageInner d _ (fourOne_le d)]
    change imageInner d (liftInner d (SylowGeometry.kleinOne d.imageSylow)) = _
    rw [imageInner_liftInner d _ (SylowGeometry.kleinOne_le_inner d.imageSylow)]
  rw [hE] at hle
  rw [centralizer_eq_elementaryPair_one d] at hle
  apply eq_of_le_of_card_ge hle
  rw [AlternatingSix.ShadowLocal.ElementaryPair.card_one d.imageSylow]
  exact le_of_eq (sImage_eq_pair_one d hEA hcard v).symm

private theorem le_of_sImage_eq (d : EarlierSetup κ G)
    (A B : Subgroup G) (hA : A ≤ d.S) (_hB : B ≤ d.S)
    (hSCB : d.SC ≤ B)
    (him : (A.subgroupOf d.S).map d.toImageSylow =
      (B.subgroupOf d.S).map d.toImageSylow) : A ≤ B := by
  intro a ha
  let aS : d.S := ⟨a, hA ha⟩
  have haI : aS ∈ A.subgroupOf d.S := ha
  have haimg : d.toImageSylow aS ∈ (A.subgroupOf d.S).map d.toImageSylow :=
    ⟨aS, haI, rfl⟩
  rw [him] at haimg
  rcases haimg with ⟨b, hb, hba⟩
  let c : d.S := aS * b⁻¹
  have hcK : (c : G) ∈ d.SC := by
    have hc0 : d.toImageSylow c = 1 := by
      dsimp [c]
      rw [map_mul, map_inv, hba]
      simp
    rw [← MonoidHom.mem_ker, d.toImageSylow_kernel] at hc0
    exact hc0
  have hcB : (c : G) ∈ B := hSCB hcK
  have hbB : (b : G) ∈ B := hb
  have hac : (a : G) = (c : G) * (b : G) := by
    dsimp [c, aS]
    simp
  rw [hac]
  exact B.mul_mem hcB hbB

theorem largestElementary_eq_liftedFour_pair (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) (hcard : Nat.card d.SC = 2)
    (v : CentralizingInvolution d) :
    largestElementary d.S =
      {liftedFour d v (fourZero d), liftedFour d v (fourOne d)} := by
  let L0 := liftedFour d v (fourZero d)
  let L1 := liftedFour d v (fourOne d)
  have hL0card : Nat.card L0 = 16 := by
    exact (liftedFour_elementary_card d hEA hcard v _ (fourZero_le d)).2
  have hL1card : Nat.card L1 = 16 := by
    exact (liftedFour_elementary_card d hEA hcard v _ (fourOne_le d)).2
  have hL0mem : L0 ∈ largestElementary d.S := by
    refine ⟨liftedFour_le_s d v _ (fourZero_le d),
      (liftedFour_elementary_card d hEA hcard v _ (fourZero_le d)).1, ?_⟩
    intro F hF hFelem
    rw [hL0card]
    exact elementary_card_le_sixteen d F hF hcard
  have hL1mem : L1 ∈ largestElementary d.S := by
    refine ⟨liftedFour_le_s d v _ (fourOne_le d),
      (liftedFour_elementary_card d hEA hcard v _ (fourOne_le d)).1, ?_⟩
    intro F hF hFelem
    rw [hL1card]
    exact elementary_card_le_sixteen d F hF hcard
  have hcases (F : Subgroup G) (hF : F ∈ largestElementary d.S) :
      F = L0 ∨ F = L1 := by
    let : IsElementaryAbelian 2 F := hF.2.1
    let FS : Subgroup d.S := F.subgroupOf d.S
    let g : FS →* d.imageSylow := d.toImageSylow.comp FS.subtype
    let : IsElementaryAbelian 2 FS := IsElementaryAbelian.subgroupOf hF.1
    let : IsElementaryAbelian 2 (⊤ : Subgroup FS) := by
      rw [← Subgroup.subgroupOf_self FS]
      exact IsElementaryAbelian.subgroupOf (p := 2) (H := FS) (K := FS) le_rfl
    let I : Subgroup d.imageSylow := (⊤ : Subgroup FS).map g
    let : IsElementaryAbelian 2 I := IsElementaryAbelian.map g
    have hIle : Nat.card I ≤ 8 := by
      let J : Subgroup AutA6 := I.map (d.imageSylow : Subgroup AutA6).subtype
      let : IsElementaryAbelian 2 J := IsElementaryAbelian.map _
      have hJ : Nat.card J ≤ 8 :=
        AlternatingSix.ShadowLocal.elementary_card_le_eight J
      rw [card_map_of_injective (d.imageSylow : Subgroup AutA6).subtype_injective] at hJ
      exact hJ
    have hFcard : Nat.card F = 16 := by
      have hlower : 16 ≤ Nat.card F := by
        calc
          16 = Nat.card L0 := hL0card.symm
          _ ≤ Nat.card F := hF.2.2 L0 hL0mem.1 hL0mem.2.1
      have hupper : Nat.card F ≤ 16 := elementary_card_le_sixteen d F hF.1 hcard
      apply le_antisymm
      · exact hupper
      · exact hlower
    have hker_map : g.ker.map (d.S.subtype.comp FS.subtype) ≤ d.SC := by
      rintro x ⟨a, ha, rfl⟩
      have ha' : d.toImageSylow (FS.subtype a) = 1 := by
        rw [← MonoidHom.mem_ker]
        exact ha
      rw [← MonoidHom.mem_ker, d.toImageSylow_kernel] at ha'
      exact ha'
    have hker_card : Nat.card g.ker ≤ 2 := by
      calc
        Nat.card g.ker = Nat.card (g.ker.map (d.S.subtype.comp FS.subtype)) :=
          (card_map_of_injective (f := d.S.subtype.comp FS.subtype)
            (d.S.subtype_injective.comp FS.subtype_injective)).symm
        _ ≤ Nat.card d.SC := card_le_of_le hker_map
        _ = 2 := hcard
    have hmul := g.ker.index_mul_card
    rw [← relIndex_top_right] at hmul
    rw [relIndex_ker] at hmul
    change Nat.card I * Nat.card g.ker = Nat.card FS at hmul
    have hFScard : Nat.card FS = 16 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hF.1).toEquiv]
      exact hFcard
    rw [hFScard] at hmul
    have hker_pos : 0 < Nat.card g.ker := Nat.card_pos
    have hker_cases : Nat.card g.ker = 1 ∨ Nat.card g.ker = 2 := by omega
    have hIcard : Nat.card I = 8 := by
      rcases hker_cases with hk | hk
      · rw [hk, mul_one] at hmul
        omega
      · rw [hk] at hmul
        omega
    have himageF : (F.subgroupOf d.S).map d.toImageSylow = I := by
      ext y
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, Subgroup.mem_top _, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨FS.subtype a, a.property, rfl⟩
    rcases AlternatingSix.ShadowLocal.ElementaryPair.elementary_eight_cases
      d.imageSylow I hIcard with hI0 | hI1
    · left
      have hleF : F ≤ L0 := by
        apply le_of_sImage_eq d F L0 hF.1 (liftedFour_le_s d v _ (fourZero_le d))
            le_sup_left
        rw [himageF, hI0, sImage_liftedFour_eq_pair_zero d hEA hcard v]
      exact eq_of_le_of_card_ge hleF (by rw [hL0card, hFcard])
    · right
      have hleF : F ≤ L1 := by
        apply le_of_sImage_eq d F L1 hF.1 (liftedFour_le_s d v _ (fourOne_le d))
            le_sup_left
        rw [himageF, hI1, sImage_liftedFour_eq_pair_one d hEA hcard v]
      exact eq_of_le_of_card_ge hleF (by rw [hL1card, hFcard])
  ext F
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hF
    exact hcases F hF
  · rintro (rfl | rfl)
    · exact hL0mem
    · exact hL1mem

theorem largestElementary_eq_localCores (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) (hcard : Nat.card d.SC = 2)
    (hcore : ∀ E : Subgroup G, E ≤ d.S ⊓ d.K → IsKleinFour E →
      localCore d E = d.S ⊓ centralizer (E : Set G))
    (v : CentralizingInvolution d) :
    largestElementary d.S =
      {localCore d (fourZero d), localCore d (fourOne d)} := by
  have h0 := localCore_eq_liftedFour d hEA hcard hcore v
    (fourZero d) (fourZero_le d)
  have h1 := localCore_eq_liftedFour d hEA hcard hcore v
    (fourOne d) (fourOne_le d)
  rw [h0, h1]
  exact largestElementary_eq_liftedFour_pair d hEA hcard v

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.OrderTwo
