module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OutsideFixedSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CyclicSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterTorusSource
public import Theory.GroupTheory.ElementaryPairNorm
/-!
# Fusion in the centerless outside-involution row

For the centerless natural block, |U|=|Z(R)|². The norm u↦[u,uᵗ]
is a homomorphism with kernel Z(R), so it reaches every central element.
Its norms belong to [R,t], proving transitivity on tZ(R). Comparing the
two elementary factors then reduces every involution in tR to a central
translate and proves its R-conjugacy to t.

Source: Aschbacher–Smith, Lemma 2.4.14(1), printed p.533.
-/
public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_centerless_elementary_pair_card
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hcenter : center (d.block.map d.H.subtype) = ⊥) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    Nat.card (sourceModule (d.block.map d.H.subtype)) =
      Nat.card (R ⊓ centralizer (R : Set G) : Subgroup G)^2 := by
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let Z := R ⊓ centralizer (R : Set G)
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  obtain ⟨c⟩ := source_cyclic_torus_setup d hG T hST hsingle hL hM hTM hunique
  have hZcard : Nat.card Z = 2^n :=
    (source_centerless_torus_regular d hG T hST hsingle hL hM hTM hunique hcenter c.torus
      (c.torus_le.trans inf_le_right) (Odd.of_dvd_nat c.hall_odd (card_dvd_of_le c.torus_le_hall))
      c.torus_card (c.torus_le_hall.trans c.hall_normalizes)).1
  have hfixed : ChapterC.blockFixed L = ⊥ := by
    change (center L).subgroupOf (ChapterC.blockU L) = ⊥
    rw [hcenter]
    exact bot_subgroupOf _
  change Nat.card (sourceModule L) = Nat.card Z^2
  calc
    Nat.card (sourceModule L) = Nat.card (ChapterC.blockU L) := card_map_of_injective L.subtype_injective
    _ = Nat.card (ChapterC.blockU L ⧸ ChapterC.blockFixed L)*Nat.card (ChapterC.blockFixed L) :=
      card_eq_card_quotient_mul_card_subgroup (ChapterC.blockFixed L)
    _ = 2^(n*2) := by rw [hK.module_card,hfixed];simp
    _ = Nat.card Z^2 := by rw [hZcard,pow_mul]

theorem source_centerless_outside_involution_fusion
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hcenter : center (d.block.map d.H.subtype) = ⊥)
    (t : G) (htT : t ∈ T) (htS : t ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (ht2 : t^2=1)
    (htZ : t ∈ centralizer
      ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
        centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)
        : Subgroup G) : Set G)) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    (∀ z ∈ Z, ∃ k ∈ ⁅R,zpowers t⁆, k*t*k⁻¹=t*z) ∧
      ∀ r ∈ R, (t*r)^2=1 → ∃ k ∈ R, k*t*k⁻¹=t*r := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let U := sourceModule L
  let V := U.map (MulAut.conj t).toMonoidHom
  let Z := R ⊓ centralizer (R : Set G)
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht2)
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have ht := d.lemma_2_4_8_1 hG T hST hsingle hK
  have hf := source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique
  have hU : U = twoCore d.H := (lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2
  let : IsElementaryAbelian 2 U := hU.symm ▸ (d.core_source hG T hST).2.2.2.1
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj t).toMonoidHom
  have hgen : U ⊔ V = R := by simpa only [hti] using (hf.2.2.2 t htT htS).1.symm
  have hZ : U ⊓ V = Z := by
    simpa only [hti] using source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique t htT htS
  have hUR : U ≤ R := le_sup_left.trans_eq hgen
  have hVR : V ≤ R := le_sup_right.trans_eq hgen
  have hRU : R ≤ normalizer (U : Set G) :=
    (source_core_absorption d hG T hST hsingle hL hM hTM hunique).1.trans
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L)))
  have hRt : R.map (MulAut.conj t).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (ht.2.2 htT)
  have hRV : R ≤ normalizer (V : Set G) := by
    have hh := (map_mono (f := (MulAut.conj t).toMonoidHom) hRU).trans
      (U.le_normalizer_map (MulAut.conj t).toMonoidHom)
    rwa [hRt] at hh
  have hder : ⁅R,R⁆ ≤ Z := by
    rw [←hZ]
    apply le_inf
    · rw [←hgen]
      exact commutator_sup_le_of_normalized_derived U V (hVR.trans hRU)
        (by rw [commutator_self_eq_bot_iff.mpr inferInstance];exact bot_le)
    · rw [←hgen,sup_comm U V]
      exact commutator_sup_le_of_normalized_derived V U (hUR.trans hRV)
        (by rw [commutator_self_eq_bot_iff.mpr inferInstance];exact bot_le)
  have hinv : ∀ r ∈ R, r^2=1 → r ∈ U ∨ r ∈ V := by
    simpa only [hti] using (source_elementary_subgroup_pair d hG T hST hsingle hL hM hTM hunique t htT htS).1
  have hcard : Nat.card U=Nat.card Z^2 :=
    source_centerless_elementary_pair_card d hG T hST hsingle hL hM hTM hunique hcenter
  have hcentral := elementary_pair_conjugate_central_translate R U Z t ht2 hUR hVR hZ hder
    (show Z ≤ centralizer (R : Set G) from inf_le_right) htZ hinv hcard
  exact ⟨hcentral, elementary_pair_conjugate_involution_coset R U V Z t ht2 (ht.2.2 htT)
    hgen hRU rfl hZ inf_le_right hcentral⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single
