module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.AbsorptionSource
public import Theory.GroupTheory.DerivedCenterAbelianPair
/-!
# The complete original Sylow and elementary pair in 2.4.8(3)

After absorption R is the actual Sylow intersection S∩L. The genuine
C.5 fixed-module calculation puts Z(R) in R′. Since the two elementary
cores U and Uˣ are normal in R and generate it, their intersection is
exactly Z(R). The original global C.6 family gives every maximum elementary
subgroup of S and T, for each x in T−S.

The ambient expression R∩C_G(R) is the embedded center of R.
Source: Aschbacher–Smith, Lemma 2.4.8(3), printed pp.529–530.
-/
public section
open Subgroup

namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_absorbed_center_pair
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (x : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    let U := sourceModule L
    U ⊓ U.map (MulAut.conj x⁻¹).toMonoidHom = R ⊓ centralizer (R : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let U := sourceModule L
  let a := MulAut.conj x⁻¹
  have hf := source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique
  have hc := lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique
  have hu : IsElementaryAbelian 2 U := by
    change IsElementaryAbelian 2 (sourceModule L)
    rw [hc.2]
    exact (d.core_source hG T hST).2.2.2.1
  let := hu
  let : IsElementaryAbelian 2 (U.map a.toMonoidHom) := IsElementaryAbelian.map a.toMonoidHom
  have hRL : R ≤ L := (source_core_absorption d hG T hST hsingle hL hM hTM hunique).1
  have hRU : R ≤ normalizer (U : Set G) := hRL.trans
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L)))
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have ht := d.lemma_2_4_8_1 hG T hST hsingle hK
  have hRa : R.map a.toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp
    (ht.2.2 (T.inv_mem hxT))
  have hRV : R ≤ normalizer (U.map a.toMonoidHom : Set G) := by
    have hh := (map_mono (f := a.toMonoidHom) hRU).trans (U.le_normalizer_map a.toMonoidHom)
    rwa [hRa] at hh
  have hcent : R ⊓ centralizer (R : Set G) ≤ ⁅R,R⁆ := by
    have hR : R = S ⊓ L := hf.1
    rw [hR]
    exact source_sylow_center_le_derived d hG T hST hsingle hL
  exact center_eq_intersection_of_derived_center_abelian_pair R U (U.map a.toMonoidHom)
    (hf.2.2.2 x hxT hxS).1.symm hRU hRV hcent
/-- Original 2.4.8(3), including the actual Sylow and center intersection. -/
theorem lemma_2_4_8_3
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    let U := sourceModule L
    R = S ⊓ L ∧ ChapterB.baumann S = R ∧
      (∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = R) ∧
      ∀ x ∈ T, x ∉ S →
        R = U ⊔ U.map (MulAut.conj x⁻¹).toMonoidHom ∧
        U ⊓ U.map (MulAut.conj x⁻¹).toMonoidHom = R ⊓ centralizer (R : Set G) ∧
        Stellmacher.elementaryAbelianMaxSubgroups S = {U,U.map (MulAut.conj x⁻¹).toMonoidHom} ∧
        Stellmacher.elementaryAbelianMaxSubgroups (T : Subgroup G) =
          {U,U.map (MulAut.conj x⁻¹).toMonoidHom} := by
  have h := source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique
  refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
  intro x hx hxS
  have hxg := h.2.2.2 x hx hxS
  exact ⟨hxg.1,source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique x hx hxS,hxg.2⟩

end CFSG.Quasithin.Chapter2.LinearShadows.Single
