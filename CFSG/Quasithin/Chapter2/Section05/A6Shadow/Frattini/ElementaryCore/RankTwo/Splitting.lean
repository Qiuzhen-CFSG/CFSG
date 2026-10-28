module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.RankTwo.Action
public import Theory.ElementaryAbelian.Join

/-!
# Splitting the rank-two elementary centralizers

A normal elementary subgroup of the cyclic-eight holomorph centralizes
its inner dihedral subgroup. The crossed core has order four and acts
faithfully, so its image is the whole four-element centralizer. In
particular it contains the genuine marked transposition. Compatibility
then proves that the crossed core centralizes S ∩ K upstairs. The two
relative four-group centralizers are the joins S_C S_C^x E_i and are
elementary abelian.

Source: Aschbacher–Smith, proof of 2.5.24, printed p.568. This argument
uses only elementary abelianness and order four of S_C from that branch;
it does not require the later involution or Frattini identities.
-/

@[expose] public section

open Subgroup AlternatingSix.ShadowLocal
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable (d : EarlierSetup κ G)

noncomputable def image (U : Subgroup G) : Subgroup d.imageSylow :=
  (U.subgroupOf d.S).map d.toImageSylow

theorem mem_image (U : Subgroup G) (hU : U ≤ d.S) (a : d.imageSylow) :
    a ∈ image d U ↔ ∃ u : U, d.toImageSylow ⟨u, hU u.property⟩ = a := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨⟨u, hU u.property⟩, u.property, rfl⟩

theorem image_inner (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) :
    image d E = imageInner d E := by
  ext a
  rw [mem_image d E (hE.trans inf_le_left), mem_imageInner d E hE]

theorem preimage_image (U : Subgroup G) (hU : U ≤ d.S) :
    preimage d (image d U) = U ⊔ d.SC := by
  rw [preimage, image, comap_map_eq, Subgroup.map_sup, d.toImageSylow_kernel,
    map_subgroupOf_eq_of_le hU, map_subgroupOf_eq_of_le d.sc_le_s]

theorem preimage_sup (U V : Subgroup d.imageSylow) :
    preimage d (U ⊔ V) = preimage d U ⊔ preimage d V := by
  rw [preimage, ← comap_sup_eq _ _ _ (toImageSylow_surjective d), Subgroup.map_sup]
  rfl

private theorem model_normal_elementary_le (R : Subgroup Holomorph.Model)
    [R.Normal] [IsElementaryAbelian 2 R] :
    R ≤ centralizer (Holomorph.innerD : Set Holomorph.Model) := by
  rw [Holomorph.centralizer_innerD]
  intro x hx
  have hc := (inferInstance : R.Normal).conj_mem x hx Holomorph.rotation
  have hcomm : x * (Holomorph.rotation * x * Holomorph.rotation⁻¹) =
      (Holomorph.rotation * x * Holomorph.rotation⁻¹) * x :=
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : R) ⟨_, hc⟩)
  have table : ∀ x : Holomorph.Model, x ^ 2 = 1 →
      x * (Holomorph.rotation * x * Holomorph.rotation⁻¹) =
        (Holomorph.rotation * x * Holomorph.rotation⁻¹) * x →
      ∃ i, Holomorph.centralTranspositionEmbedding i = x := by decide +kernel
  exact (Holomorph.mem_centralTwo_sup_transposition x).mpr
    (table x (elemPow_eq_one_of_isElementaryAbelian x hx) hcomm)

private theorem normal_elementary_le (P : Sylow 2 AutA6) (R : Subgroup P)
    [R.Normal] [IsElementaryAbelian 2 R] : R ≤ centralizer (sylowInner P : Set P) := by
  let e := Identification.sylowEquiv P
  let W := R.map e.symm.toMonoidHom
  let : W.Normal := (inferInstance : R.Normal).map _ e.symm.surjective
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hW := model_normal_elementary_le W
  intro r hr a ha
  have hrW : e.symm r ∈ W := mem_map_of_mem _ hr
  have haD : e.symm a ∈ Holomorph.innerD := by
    rw [← Identification.sylowEquiv_innerD P] at ha
    change a ∈ Holomorph.innerD.map e.toMonoidHom at ha
    exact mem_map_equiv.mp ha
  apply e.symm.injective
  simpa only [map_mul] using hW hrW _ haD

theorem crossing_image (hEA : IsElementaryAbelian 2 d.SC) (hcard : Nat.card d.SC = 4) :
    image d (rightConjugate d.x d.SC) = centralizer (sylowInner d.imageSylow : Set d.imageSylow) := by
  let U := rightConjugate d.x d.SC
  have hU : U ≤ d.S := d.rightConjugate_le d.sc_le_s
  let : IsElementaryAbelian 2 U := rightConjugate_elementary d.x d.SC hEA
  let : IsElementaryAbelian 2 (U.subgroupOf d.S) := IsElementaryAbelian.subgroupOf hU
  let : IsElementaryAbelian 2 (image d U) := IsElementaryAbelian.map _
  let : (U.subgroupOf d.S).Normal := d.rightConjugate_normal d.sc_le_s d.normal_sc
  let : (image d U).Normal := Subgroup.Normal.map inferInstance _ (toImageSylow_surjective d)
  apply eq_of_le_of_card_ge (normal_elementary_le _ _)
  have hrange : (d.toImageSylow.comp (inclusion hU)).range = image d U := by
    ext a
    exact (mem_image d U hU a).symm
  have hc : Nat.card (image d U) = 4 := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective d.crossing_action_injective).toEquiv]
    exact (rightConjugate_card d.x d.SC).trans hcard
  rw [hc, Nat.card_congr (SylowGeometry.centralizerInnerEquiv d.imageSylow).toEquiv]
  simp [Holomorph.E4, Holomorph.C2]

theorem crossing_centralizes_inner (hEA : IsElementaryAbelian 2 d.SC)
    (hcard : Nat.card d.SC = 4) :
    rightConjugate d.x d.SC ≤ centralizer (d.S ⊓ d.K : Set G) := by
  intro u hu
  have huS := d.rightConjugate_le d.sc_le_s hu
  have him : d.toImageSylow ⟨u, huS⟩ ∈ image d (rightConjugate d.x d.SC) :=
    (mem_image d _ (d.rightConjugate_le d.sc_le_s) _).mpr ⟨⟨u, hu⟩, rfl⟩
  rw [crossing_image d hEA hcard] at him
  have hI : imageInner d (d.S ⊓ d.K) = sylowInner d.imageSylow := by
    apply le_antisymm (imageInner_le d _)
    intro a ha
    obtain ⟨k, hk⟩ := (innerEquiv d).surjective ⟨a, ha⟩
    exact ⟨innerEquiv d k, ⟨k, k.property, rfl⟩, congrArg Subtype.val hk⟩
  have hm : u ∈ preimage d (centralizer (imageInner d (d.S ⊓ d.K) : Set d.imageSylow)) := by
    rw [hI]
    exact (mem_preimage d _ ⟨u, huS⟩).mpr him
  rw [← centralizer_preimage d _ le_rfl] at hm
  exact hm.2

theorem crossing_induces_transposition (hEA : IsElementaryAbelian 2 d.SC)
    (hcard : Nat.card d.SC = 4) :
    ∃ (v : G) (hv : v ∈ rightConjugate d.x d.SC) (σ : Equiv.Perm (Fin 6)),
      σ.IsSwap ∧ d.action ⟨v, d.s_le_h (d.rightConjugate_le d.sc_le_s hv)⟩ = permutationAction σ := by
  have ht : Identification.sylowEquiv d.imageSylow Holomorph.transposition ∈
      image d (rightConjugate d.x d.SC) := by
    rw [crossing_image d hEA hcard, SylowGeometry.centralizer_inner]
    apply mem_sup_right
    exact mem_map_of_mem _ (mem_zpowers _)
  obtain ⟨v, hv⟩ := (mem_image d _ (d.rightConjugate_le d.sc_le_s) _).mp ht
  refine ⟨v, v.property, _, Identification.conjugatedTransposition_isSwap d.imageSylow, ?_⟩
  exact (congrArg Subtype.val hv).trans (Identification.sylowEquiv_transposition d.imageSylow)

private theorem model_zero_join :
    Holomorph.ElementaryPair.zero =
      centralizer (Holomorph.innerD : Set Holomorph.Model) ⊔ Holomorph.kleinZero := by
  rw [Holomorph.centralizer_innerD, ← Holomorph.centralTranspositionEmbedding_range]
  apply le_antisymm
  · rintro _ ⟨i, rfl⟩
    exact ( _ : Subgroup Holomorph.Model).mul_mem
      (mem_sup_left ⟨(1, i.1), by revert i; decide +kernel⟩)
      (mem_sup_right ⟨i.2, rfl⟩)
  · apply sup_le
    · rintro _ ⟨i, rfl⟩
      exact ⟨(i.2, i.1, 1), by
        revert i
        decide +kernel⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨(1, i), by revert i; decide +kernel⟩

private theorem model_one_join :
    Holomorph.ElementaryPair.one =
      centralizer (Holomorph.innerD : Set Holomorph.Model) ⊔ Holomorph.kleinOne := by
  rw [Holomorph.centralizer_innerD, ← Holomorph.centralTranspositionEmbedding_range]
  apply le_antisymm
  · rintro _ ⟨i, rfl⟩
    exact ( _ : Subgroup Holomorph.Model).mul_mem
      (mem_sup_left ⟨(1, i.1), by revert i; decide +kernel⟩)
      (mem_sup_right ⟨i.2, rfl⟩)
  · apply sup_le
    · rintro _ ⟨i, rfl⟩
      exact ⟨(i.2, i.1, 1), by
        revert i
        decide +kernel⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨(1, i), by revert i; decide +kernel⟩


private theorem centralizer_inner_map (P : Sylow 2 AutA6) :
    (centralizer (Holomorph.innerD : Set Holomorph.Model)).map
      (Identification.sylowEquiv P).toMonoidHom = centralizer (sylowInner P : Set P) := by
  rw [Holomorph.centralizer_innerD, Subgroup.map_sup, ← Holomorph.center_model,
    center_map_equiv, SylowGeometry.centralizer_inner]
  rfl

private theorem pair_zero_join (P : Sylow 2 AutA6) :
    ElementaryPair.zero P = centralizer (sylowInner P : Set P) ⊔ SylowGeometry.kleinZero P := by
  change Holomorph.ElementaryPair.zero.map _ = _
  rw [model_zero_join, Subgroup.map_sup, centralizer_inner_map]
  rfl

private theorem pair_one_join (P : Sylow 2 AutA6) :
    ElementaryPair.one P = centralizer (sylowInner P : Set P) ⊔ SylowGeometry.kleinOne P := by
  change Holomorph.ElementaryPair.one.map _ = _
  rw [model_one_join, Subgroup.map_sup, centralizer_inner_map]
  rfl

theorem centralizer_fourZero_split (hEA : IsElementaryAbelian 2 d.SC)
    (hcard : Nat.card d.SC = 4) :
    d.S ⊓ centralizer (fourZero d : Set G) = d.SC ⊔ rightConjugate d.x d.SC ⊔ fourZero d := by
  have hzero : image d (fourZero d) = SylowGeometry.kleinZero d.imageSylow := by
    rw [image_inner d _ (fourZero_le d)]
    exact imageInner_liftInner d _ (SylowGeometry.kleinZero_le_inner d.imageSylow)
  rw [centralizer_fourZero, pair_zero_join, ← crossing_image d hEA hcard, ← hzero,
    preimage_sup, preimage_image d _ (d.rightConjugate_le d.sc_le_s),
    preimage_image d _ ((fourZero_le d).trans inf_le_left)]
  ac_rfl

theorem centralizer_fourOne_split (hEA : IsElementaryAbelian 2 d.SC)
    (hcard : Nat.card d.SC = 4) :
    d.S ⊓ centralizer (fourOne d : Set G) = d.SC ⊔ rightConjugate d.x d.SC ⊔ fourOne d := by
  have hone : image d (fourOne d) = SylowGeometry.kleinOne d.imageSylow := by
    rw [image_inner d _ (fourOne_le d)]
    exact imageInner_liftInner d _ (SylowGeometry.kleinOne_le_inner d.imageSylow)
  rw [centralizer_fourOne, pair_one_join, ← crossing_image d hEA hcard, ← hone,
    preimage_sup, preimage_image d _ (d.rightConjugate_le d.sc_le_s),
    preimage_image d _ ((fourOne_le d).trans inf_le_left)]
  ac_rfl

private theorem split_elementary (hEA : IsElementaryAbelian 2 d.SC)
    (hcard : Nat.card d.SC = 4) (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) [IsKleinFour E] :
    IsElementaryAbelian 2 (d.SC ⊔ rightConjugate d.x d.SC ⊔ E : Subgroup G) := by
  let := hEA
  let : IsElementaryAbelian 2 (rightConjugate d.x d.SC) := rightConjugate_elementary d.x d.SC hEA
  let : IsElementaryAbelian 2 (d.SC ⊔ rightConjugate d.x d.SC : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp d.commuting_conjugate)
  let : IsElementaryAbelian 2 E := {
    toIsMulCommutative := IsKleinFour.isMulCommutative
    exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  apply IsElementaryAbelian.sup_of_le_centralizer
  apply le_centralizer_iff.mp
  apply sup_le
  · exact (d.centralizer_K ▸ inf_le_right).trans (centralizer_le (hE.trans inf_le_right))
  · exact (crossing_centralizes_inner d hEA hcard).trans (centralizer_le hE)

theorem centralizer_fourZero_elementary (hEA : IsElementaryAbelian 2 d.SC)
    (hcard : Nat.card d.SC = 4) :
    IsElementaryAbelian 2 (d.S ⊓ centralizer (fourZero d : Set G) : Subgroup G) := by
  rw [centralizer_fourZero_split d hEA hcard]
  exact split_elementary d hEA hcard _ (fourZero_le d)

theorem centralizer_fourOne_elementary (hEA : IsElementaryAbelian 2 d.SC)
    (hcard : Nat.card d.SC = 4) :
    IsElementaryAbelian 2 (d.S ⊓ centralizer (fourOne d : Set G) : Subgroup G) := by
  rw [centralizer_fourOne_split d hEA hcard]
  exact split_elementary d hEA hcard _ (fourOne_le d)

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.RankTwo
