module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ElementarySource
public import Theory.GroupTheory.ElementaryPairFixedPoints
public import Theory.GroupTheory.PGroup.OmegaAmbient
/-!
# Outside involutions centralizing the Thompson center

The actual two elementary factors of R are exchanged by every involution
in T−S. Their involution union shows that a fixed element is central when
the involution centralizes Z(R). The conjugate pair generates R modulo
its displacement subgroup, forcing R′ into that subgroup; the original
conjugate escape makes the inclusion of Z(R) strict.

Source: Aschbacher–Smith, Lemma 2.4.14(1), printed p.533, as used in
Lemmas 2.4.18–19 and 2.4.21, printed pp.534–536.
-/
public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_outside_involution_center_fixed
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (t : G) (htT : t ∈ T) (htS : t ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (ht2 : t^2=1)
    (htZ : t ∈ centralizer
      ((Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
        centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G)
        : Subgroup G) : Set G)) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    R ⊓ centralizer ({t} : Set G) = Z ∧ Z < ⁅R,zpowers t⁆ := by
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
  have hcore := lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique
  have hU : U = twoCore d.H := hcore.2
  let : IsElementaryAbelian 2 U := hU.symm ▸ (d.core_source hG T hST).2.2.2.1
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj t).toMonoidHom
  have hgen : U ⊔ V = R := by simpa only [hti] using (hf.2.2.2 t htT htS).1.symm
  have hZ : U ⊓ V = Z := by
    simpa only [hti] using source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique t htT htS
  have hRU : R ≤ normalizer (U : Set G) :=
    (source_core_absorption d hG T hST hsingle hL hM hTM hunique).1.trans
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L)))
  have hRt : R.map (MulAut.conj t).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (ht.2.2 htT)
  have hRV : R ≤ normalizer (V : Set G) := by
    have hh := (map_mono (f := (MulAut.conj t).toMonoidHom) hRU).trans
      (U.le_normalizer_map (MulAut.conj t).toMonoidHom)
    rwa [hRt] at hh
  have haa (x : G) : (MulAut.conj t) ((MulAut.conj t) x) = x := by
    simp only [MulAut.conj_apply]
    have htt : t*t=1 := by simpa only [pow_two] using ht2
    rw [hti]
    calc t*(t*x*t)*t = (t*t)*x*(t*t) := by group
         _ = x := by rw [htt,one_mul,mul_one]
  have hVU : V.map (MulAut.conj t).toMonoidHom = U := by
    ext x
    constructor
    · rintro ⟨v,⟨u,hu,rfl⟩,rfl⟩
      change (MulAut.conj t) ((MulAut.conj t) u) ∈ U
      rw [haa]
      exact hu
    · intro hx
      refine ⟨(MulAut.conj t) x,mem_map_of_mem (MulAut.conj t).toMonoidHom hx,haa x⟩
  have hinv : ∀ r ∈ R, r^2=1 → r ∈ U ∨ r ∈ V := by
    simpa only [hti] using (source_elementary_subgroup_pair d hG T hST hsingle hL hM hTM hunique t htT htS).1
  have hfixed : R ⊓ centralizer ({t} : Set G) = Z := by
    apply le_antisymm
    · rintro r ⟨hr,hc⟩
      rw [←hZ]
      refine elementary_pair_fixed_le_intersection R U V hgen hRU hRV
        (hZ ▸ (show Z ≤ centralizer (R : Set G) from inf_le_right))
        (MulAut.conj t) haa rfl hVU ?_ hinv r hr ?_
      · intro z hz
        have hc := mem_centralizer_iff.mp htZ z (show z ∈ Z from hZ ▸ hz)
        change t*z*t⁻¹=z
        rw [←hc,mul_inv_cancel_right]
      · change t*r*t⁻¹=r
        rw [←mem_centralizer_singleton_iff.mp hc,mul_inv_cancel_right]
    · rintro z ⟨hzR,hzc⟩
      exact ⟨hzR,mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp htZ z ⟨hzR,hzc⟩))⟩
  refine ⟨hfixed,?_⟩
  apply center_lt_commutator_of_conjugate_abelian_pair R U Z t hgen
  · change R ⊓ centralizer (R : Set G) ≤ ⁅R,R⁆
    have hR : R = S ⊓ L := hf.1
    rw [hR]
    exact source_sylow_center_le_derived d hG T hST hsingle hL
  · exact hZ.symm ▸ inf_le_left
  · intro hle
    have hU0 : d.U0.map d.H.subtype ≤ U := hU.symm ▸
      (le_sup_left.trans_eq (d.core_source hG T hST).2.1.symm)
    have he := d.lemma_2_4_5_2b T hST.le (T : Subgroup G) hST.le le_rfl ht.1 t htT htS
    apply he.2
    rw [hti]
    exact ((map_mono hU0).trans hle).trans_eq hU

/-- Every involution fixed by an outside actor lies in the Thompson center. -/
theorem source_outside_fixed_involution_mem_center
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (t : G) (htT : t ∈ T) (htS : t ∉ (d.S : Subgroup d.H).map d.H.subtype) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    ∀ r ∈ R, r^2=1 → Commute t r → r ∈ R ⊓ centralizer (R : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let U := sourceModule (d.block.map d.H.subtype)
  let a := MulAut.conj t⁻¹
  let V := U.map a.toMonoidHom
  have hZ : U ⊓ V = R ⊓ centralizer (R : Set G) :=
    source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique t htT htS
  change ∀ r ∈ R, r^2=1 → Commute t r → r ∈ R ⊓ centralizer (R : Set G)
  intro r hr hr2 htr
  have hf : a r = r := by
    change t⁻¹*r*(t⁻¹)⁻¹=r
    rw [htr.inv_left.eq,mul_inv_cancel_right]
  rw [←hZ]
  rcases (source_elementary_subgroup_pair d hG T hST hsingle hL hM hTM hunique t htT htS).1 r hr hr2 with hu | hv
  · refine ⟨hu,?_⟩
    exact ⟨r,hu,hf⟩
  · refine ⟨?_,hv⟩
    obtain ⟨u,hu,he⟩ := hv
    have hur : u=r := a.injective (he.trans hf.symm)
    exact hur ▸ hu

/-- The omega subgroup of an outside fixed group is precisely the fixed
part of the Thompson center, the common step in all three 2.4.14 rows. -/
theorem source_outside_fixed_omega
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (t : G) (htT : t ∈ T) (htS : t ∉ (d.S : Subgroup d.H).map d.H.subtype) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    omegaOneAmbient (R ⊓ centralizer ({t} : Set G)) = Z ⊓ centralizer ({t} : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let U := sourceModule (d.block.map d.H.subtype)
  let Z := R ⊓ centralizer (R : Set G)
  let C := R ⊓ centralizer ({t} : Set G)
  have hU : U = twoCore d.H := (lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2
  let : IsElementaryAbelian 2 U := hU.symm ▸ (d.core_source hG T hST).2.2.2.1
  have hZU : Z ≤ U := by
    have he : U ⊓ U.map (MulAut.conj t⁻¹).toMonoidHom = Z :=
      source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique t htT htS
    rw [←he]
    exact inf_le_left
  change omegaOneAmbient C = Z ⊓ centralizer ({t} : Set G)
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    rintro r ⟨hr,hc⟩ hr2
    exact ⟨source_outside_fixed_involution_mem_center d hG T hST hsingle hL hM hTM hunique
      t htT htS r hr hr2 (mem_centralizer_singleton_iff.mp hc).symm,hc⟩
  · rintro z ⟨hz,hc⟩
    exact (omegaOneAmbient_le_iff C (omegaOneAmbient C)).mp le_rfl z ⟨hz.1,hc⟩
      (elemPow_eq_one_of_isElementaryAbelian (p:=2) z (hZU hz))

end CFSG.Quasithin.Chapter2.LinearShadows.Single
