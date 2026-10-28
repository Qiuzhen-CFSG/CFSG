module

public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.Quotient.Abelian.Geometry
public import Stellmacher.Recognition.Parrott.LocalNormalizer.ElementaryFusion
public import Stellmacher.Recognition.Parrott.DerivedLocalCenters

/-!
# Elementary-point centralizers in the actual transfer Sylow

For W=Ω₁(O₂(N_G(F))) and k in F outside Z(W), C_W(k) has order at most
64 and contains an involution outside F. To see this first choose k in E∩F:
Z(W)⟨k⟩ has order 16, and its centralizer in the original two-core bounds
C_W(k). The elementary subgroup E supplies the outside involution. The
normalizer orbit on F−Z(W) transports both assertions to every such k.

Now F≤C_Y(k)≤C_W(k), where Y is the literal second-transfer Sylow image.
A strict enlargement of the order-32 subgroup F would give C_Y(k)=C_W(k),
putting the outside involution in Y and contradicting Ω₁(Y)=F. Thus C_Y(k)=F,
which supplies the remaining premise of the quotient small-abelian calculation.

Source: Parrott (1972), Lemma 8, printed pp.682–683, observation (ii).
-/

open Subgroup
open scoped IsMulCommutative
namespace Stellmacher.Recognition.ParrottSecondTransferData
variable {G : Type*} [Group G] [Finite G] {z : G}
  {d : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData d}
  (t : ParrottSecondTransferData n)

private theorem omega_elementary_point_geometry
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    {k : G} (hkF : k ∈ d.F) (hkZ : k ∉ t.sylowCenter) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    Nat.card (W ⊓ centralizer ({k} : Set G) : Subgroup G) ≤ 64 ∧
      ∃ b ∈ W ⊓ centralizer ({k} : Set G), b ^ 2 = 1 ∧ b ∉ d.F := by
  intro N K W
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let L := J.map H.subtype
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let U := omega₁ K (p := 2)
  let i := N.subtype.comp K.subtype
  let Z := t.sylowCenter
  have hZdef : Z = (center U).map (i.comp U.subtype) := t.sylowCenter_eq_omega_center
  have hZE : Z ≤ E := hZdef ▸ n.omega_center_le_inf.trans inf_le_left
  have hZcard : Nat.card Z = 8 := t.sylowCenter_card
  have hzZ : z ∈ Z := by
    rw [hZdef, n.omega_center_eq]
    exact mem_sup_left (mem_sup_left (mem_zpowers z))
  have hEW : E ≤ W := le_sup_left.trans
    (d.elementary_join_le_normalizer_core_omega_of_local_inputs h hlocal n.sylow_lt_normalizer)
  have hWT : W ≤ (d.sylow : Subgroup G) := n.omega_le_core.trans n.core_le_sylow
  have hWC : W ≤ centralizer (Z : Set G) := by
    rw [hZdef]
    exact n.omega_eq_centralizer.le.trans inf_le_right
  have hnot : ¬ E ⊓ d.F ≤ Z := by
    intro hh
    have hc := card_le_of_le hh
    rw [show Nat.card (E ⊓ d.F : Subgroup G) = 16 from d.inf_card, hZcard] at hc
    omega
  obtain ⟨w, hw, hwZ⟩ := SetLike.not_le_iff_exists.mp hnot
  have hwZ' : w ∉ (center U).map (i.comp U.subtype) := hZdef ▸ hwZ
  have hkZ' : k ∉ (center U).map (i.comp U.subtype) := hZdef ▸ hkZ
  obtain ⟨g, hg⟩ :=
    d.normalizer_elementary_outside_omega_center_fusion_of_centralizer_card_of_local_inputs
      h hlocal n.sylow_lt_normalizer w hw.2 hwZ'
      (d.normalizer_elementary_outside_omega_center_centralizer_card_of_local_inputs
        h hlocal n.sylow_lt_normalizer w hw hwZ') k hkF hkZ'
  let B := W ⊓ centralizer ({w} : Set G)
  let S := Z ⊔ zpowers w
  let : IsElementaryAbelian 2 (commutator J) :=
    (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  have hSE : S ≤ E := sup_le hZE (zpowers_le.mpr hw.1)
  have hScard : Nat.card S = 16 := by
    rw [show S = Z ⊔ zpowers w from rfl,
      card_sup_zpowers_of_normalizing_involution Z w
        (elemPow_eq_one_of_isElementaryAbelian w hw.1) hwZ
        (Subgroup.centralizer_le_normalizer _ (hWC (hEW hw.1))), hZcard]
  have hBL : B ≤ L := by
    intro a ha
    by_contra haL
    exact hwZ' (d.sylow_outer_derived_fixed_le_omega_center_of_local_inputs
      h hlocal n.sylow_lt_normalizer a (hWT ha.1) haL
      ⟨hw.1, mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp ha.2).symm⟩)
  have hBS : B ≤ L ⊓ centralizer (S : Set G) := by
    intro a ha
    refine ⟨hBL ha, ?_⟩
    have hs : S ≤ centralizer ({a} : Set G) := sup_le
      (fun b hb => mem_centralizer_singleton_iff.mpr (hWC ha.1 b hb))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp ha.2).symm))
    intro b hb
    exact mem_centralizer_singleton_iff.mp (hs hb)
  have hBcard : Nat.card B ≤ 64 := by
    have hc := parrott_core_inf_centralizer_card z h S
      ((zpowers_le.mpr hzZ).trans le_sup_left) hSE
    change Nat.card S * Nat.card (L ⊓ centralizer (S : Set G) : Subgroup G) = 1024 at hc
    rw [hScard] at hc
    have hb := card_le_of_le hBS
    omega
  have hEB : E ≤ B := le_inf hEW
    (fun a ha => mem_centralizer_singleton_iff.mpr (setLike_mul_comm ha hw.1))
  have hEnot : ¬ E ≤ d.F := by
    intro he
    have hc := d.inf_card
    change Nat.card (E ⊓ d.F : Subgroup G) = 16 at hc
    rw [inf_eq_left.mpr he] at hc
    have hEcard : Nat.card E = 32 :=
      (card_map_of_injective (K := commutator J) (f := H.subtype.comp J.subtype)
        (H.subtype_injective.comp J.subtype_injective)).trans
        (parrott_centralizer_structure z h).2.2.2.2.2.2.1
    omega
  obtain ⟨b, hbE, hbF⟩ := SetLike.not_le_iff_exists.mp hEnot
  let V := U.map K.subtype
  let : U.Characteristic := omega₁_characteristic K
  let : V.Normal := ConjAct.normal_of_characteristic_of_normal
  have hNW : N ≤ normalizer (W : Set G) := by
    have hh := le_normalizer_map (H := V) N.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype, V, W, map_map] using hh
  let f := MulAut.conj (g : G)
  have hfk : f w = k := hg
  have hWmap : W.map f.toMonoidHom = W :=
    mem_normalizer_iff_map_conj_eq.mp (hNW g.property)
  have hBmap : B.map f.toMonoidHom = W ⊓ centralizer ({k} : Set G) := by
    rw [map_inf _ _ _ f.injective, hWmap]
    congr 1
    apply le_antisymm
    · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom, hfk] using
        map_centralizer_le_centralizer_image ({w} : Set G) f.toMonoidHom
    · intro a ha
      refine ⟨f.symm a, mem_centralizer_singleton_iff.mpr ?_, f.apply_symm_apply a⟩
      apply f.injective
      simpa only [map_mul, f.apply_symm_apply, hfk] using
        mem_centralizer_singleton_iff.mp ha
  refine ⟨?_, f b, ?_, ?_, ?_⟩
  · rw [← hBmap, card_map_of_injective f.injective]
    exact hBcard
  · rw [← hBmap]
    exact mem_map_of_mem f.toMonoidHom (hEB hbE)
  · rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian b hbE, map_one]
  · exact fun hb => hbF ((mem_normalizer_iff.mp g.property b).mpr hb)

/-- The ordinary centralizer in the actual transfer Sylow of a point of
F outside its center is exactly F. -/
public theorem sylowImage_elementary_point_centralizer
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    {k : G} (hkF : k ∈ d.F) (hkZ : k ∉ t.sylowCenter) :
    t.sylowImage ⊓ centralizer ({k} : Set G) = d.F := by
  let N := normalizer (d.F : Set G)
  let K := pCore 2 N
  let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
  let B := W ⊓ centralizer ({k} : Set G)
  let D := t.sylowImage ⊓ centralizer ({k} : Set G)
  let : IsElementaryAbelian 2 d.F := d.elementary
  have hFD : d.F ≤ D := le_inf t.elementary_le_sylow_image
    (fun a ha => mem_centralizer_singleton_iff.mpr (setLike_mul_comm ha hkF))
  have hDB : D ≤ B := inf_le_inf_right _ t.sylow_image_le_omega
  obtain ⟨hBcard, b, hb, hb2, hbF⟩ := t.omega_elementary_point_geometry h hlocal hkF hkZ
  change Nat.card B ≤ 64 at hBcard
  change b ∈ B at hb
  by_contra hne
  have hlt : d.F < D := lt_of_le_of_ne hFD (Ne.symm hne)
  have hDgt : Nat.card d.F < Nat.card D :=
    lt_of_not_ge (fun hc => hlt.ne (eq_of_le_of_card_ge hFD hc))
  rw [d.card] at hDgt
  have hdiv := card_dvd_of_le hFD
  rw [d.card] at hdiv
  obtain ⟨m, hm⟩ := hdiv
  have hDge : 64 ≤ Nat.card D := by omega
  have hDBEq : D = B := eq_of_le_of_card_ge hDB (hBcard.trans hDge)
  have hbY : b ∈ t.sylowImage := (hDBEq.symm ▸ hb).1
  have hOmega : (omega₁ t.sylowImage (p := 2)).map t.sylowImage.subtype = d.F := by
    change (omega₁ ((t.S : Subgroup t.L).map t.embedding) (p := 2)).map
      ((t.S : Subgroup t.L).map t.embedding).subtype = d.F
    rw [show (t.S : Subgroup t.L).map t.embedding = _ from t.S_image]
    exact t.Y_omega
  apply hbF
  rw [← hOmega]
  refine ⟨⟨b, hbY⟩, Subgroup.subset_closure ?_, rfl⟩
  exact Subtype.ext hb2

end Stellmacher.Recognition.ParrottSecondTransferData
