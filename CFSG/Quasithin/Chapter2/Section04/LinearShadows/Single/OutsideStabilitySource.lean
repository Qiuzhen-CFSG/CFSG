module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OutsideFixedSource
public import Theory.GroupTheory.ElementaryPairQuadratic
/-!
# Stability of the outside central coset

The original elementary pair makes R/Z(R) elementary abelian. The
outside involution acts quadratically there, so [[R,t],t] ≤ Z(R).
Equivalently its displacement subgroup preserves tZ(R) by conjugation.
Together with OutsideFusionSource this gives the complete action clause
of Aschbacher–Smith, Lemma 2.4.14(1), printed p.533.
-/
public section
open Subgroup
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_outside_involution_double_commutator
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (t : G) (htT : t ∈ T) (htS : t ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (ht2 : t^2=1) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    ⁅⁅R,zpowers t⁆,zpowers t⁆ ≤ R ⊓ centralizer (R : Set G) := by
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
  exact elementary_pair_double_commutator_le R U V Z hgen hRU hder inf_le_left inf_le_right
    t ht2 (ht.2.2 htT) (inf_normalizer_le_normalizer_inf
      ⟨ht.2.2 htT, normalizer_le_normalizer_centralizer R (ht.2.2 htT)⟩)

/-- The displacement subgroup preserves the central coset of the outside involution. -/
theorem source_outside_involution_coset_stable
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (t : G) (htT : t ∈ T) (htS : t ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (ht2 : t^2=1) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    ∀ k ∈ ⁅R,zpowers t⁆, ∃ z ∈ Z, k*t*k⁻¹=t*z := by
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let Z := R ⊓ centralizer (R : Set G)
  have hh := source_outside_involution_double_commutator d hG T hST hsingle hL hM hTM hunique
    t htT htS ht2
  change ∀ k ∈ ⁅R,zpowers t⁆, ∃ z ∈ Z, k*t*k⁻¹=t*z
  intro k hk
  refine ⟨⁅t⁻¹,k⁆,?_,?_⟩
  · apply hh
    rw [commutator_comm]
    exact commutator_mem_commutator ((zpowers t).inv_mem (mem_zpowers t)) hk
  · rw [commutatorElement_def]
    group

end CFSG.Quasithin.Chapter2.LinearShadows.Single
