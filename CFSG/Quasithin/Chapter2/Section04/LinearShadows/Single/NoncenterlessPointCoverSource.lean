module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ModuleFusionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DeltaCentralSource
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Whole distinguished conjugates covering fused elements

In the nontrivial-center branch, every element of the original R that is
fused into Z lies in a whole conjugate of Z contained in R. First use
the elementary pair to reduce to U. The actual L-action moves an element
of U into Z(R). Fusion separation excludes the distinguished delta orbit,
so its image lies on one of the two Z-axes. Both axes lie in U, which L
normalizes; transporting back gives the required whole conjugate.

Source: Aschbacher–Smith, the fusion argument of 2.4.21, printed p.536,
using the original 2.4.20(2) separation and 2.4.8 elementary pair.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- An element of the original R fused into Z lies in a whole Z-conjugate inside R. -/
theorem source_noncenterless_fused_conjugate_cover
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    ∀ r ∈ R, (∃ z ∈ distinguishedZ d, IsConj r z) → ∃ g : G,
      (distinguishedZ d).map (MulAut.conj g).toMonoidHom ≤ R ∧
      r ∈ (distinguishedZ d).map (MulAut.conj g).toMonoidHom := by
  let L := d.block.map d.H.subtype
  let U := sourceModule L
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let A := R ⊓ centralizer (R : Set G)
  let Z := distinguishedZ d
  obtain ⟨x,hxT,hxS⟩ := SetLike.exists_of_lt hST
  let Zx := Z.map (MulAut.conj x⁻¹).toMonoidHom
  have hf := (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).2.2.2 x hxT hxS
  have hUR : U ≤ R := le_sup_left.trans_eq hf.1.symm
  have hUxR : U.map (MulAut.conj x⁻¹).toMonoidHom ≤ R := le_sup_right.trans_eq hf.1.symm
  have hAU : A ≤ U :=
    (source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS).ge.trans inf_le_left
  have hpair : Z ⊔ Zx = A :=
    (source_distinguished_center_pair d hG T hST hsingle hL hM hTM hunique hz x hxT hxS).2
  have hZU : Z ≤ U := (le_sup_left.trans_eq hpair).trans hAU
  have hZxU : Zx ≤ U := (le_sup_right.trans_eq hpair).trans hAU
  have hLN : L ≤ normalizer (U : Set G) :=
    L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L))
  let : IsElementaryAbelian 2 Z :=
    (source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique).1
  have hcov (u : G) (hu : u∈U) (huf : ∃ z ∈ Z, IsConj u z) :
      ∃ l : G, Z.map (MulAut.conj l).toMonoidHom ≤ U ∧ u∈Z.map (MulAut.conj l).toMonoidHom := by
    obtain ⟨l,hl,hw⟩ := source_module_fused_into_sylow_center d hG T hST hsingle hL hM hTM hunique u hu
    let w := l*u*l⁻¹
    have huw : IsConj u w := isConj_iff.mpr ⟨l,rfl⟩
    have hwaxes : w∈Z ∨ w∈Zx := by
      by_contra h
      push Not at h
      have hwDelta : w ∈ distinguishedDelta d x := ⟨hw,h.1,h.2⟩
      obtain ⟨z,hzZ,huz⟩ := huf
      exact (source_distinguished_delta_central d hG T hST hsingle hL hM hTM hunique hz
        x hxT hxS w hwDelta).2.2.2 z hzZ (huw.symm.trans huz)
    have hln : U.map (MulAut.conj l⁻¹).toMonoidHom = U :=
      mem_normalizer_iff_map_conj_eq.mp (hLN (L.inv_mem hl))
    have hwu : (MulAut.conj l⁻¹) w = u := by
      dsimp [w,MulAut.conj_apply]
      group
    rcases hwaxes with hwZ | hwZx
    · exact ⟨l⁻¹,(map_mono hZU).trans_eq hln,⟨w,hwZ,hwu⟩⟩
    · refine ⟨l⁻¹*x⁻¹,?_,?_⟩
      · change Z.conjBy (l⁻¹*x⁻¹) ≤ U
        rw [conjBy_mul]
        exact (map_mono hZxU).trans_eq hln
      · change u ∈ Z.conjBy (l⁻¹*x⁻¹)
        rw [conjBy_mul]
        exact ⟨w,hwZx,hwu⟩
  change ∀ r∈R, (∃ z∈Z,IsConj r z) → ∃ g : G,
    Z.map (MulAut.conj g).toMonoidHom ≤ R ∧ r∈Z.map (MulAut.conj g).toMonoidHom
  intro r hr hrf
  have hr2 : r^2=1 := by
    obtain ⟨z,hzZ,hrz⟩ := hrf
    have hz2 : z^2=1 := elemPow_eq_one_of_isElementaryAbelian (p:=2) z hzZ
    exact isConj_one_left.mp (hz2 ▸ IsConj.pow 2 hrz)
  rcases (source_elementary_subgroup_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS).1 r hr hr2 with hu | hu
  · obtain ⟨l,hle,hlr⟩ := hcov r hu hrf
    exact ⟨l,hle.trans hUR,hlr⟩
  · obtain ⟨u,hu,he⟩ := hu
    have hur : IsConj u r := isConj_iff.mpr ⟨x⁻¹,he⟩
    have huf : ∃z∈Z,IsConj u z := by
      obtain ⟨z,hzZ,hrz⟩ := hrf
      exact ⟨z,hzZ,hur.trans hrz⟩
    obtain ⟨l,hle,hlu⟩ := hcov u hu huf
    refine ⟨x⁻¹*l,?_,?_⟩
    · change Z.conjBy (x⁻¹*l) ≤ _
      rw [conjBy_mul]
      exact (map_mono hle).trans hUxR
    · change r ∈ Z.conjBy (x⁻¹*l)
      rw [conjBy_mul]
      change r∈(Z.map (MulAut.conj l).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom
      rw [←he]
      exact mem_map_of_mem _ hlu
end CFSG.Quasithin.Chapter2.LinearShadows.Single
