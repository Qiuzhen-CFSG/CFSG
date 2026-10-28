module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CyclicSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.SylowSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.InsideCenterDisplacementSource
public import Theory.GroupTheory.FixedProductCoboundaries
/-!
# Fixed factors for an inside involution

The two elementary subgroups generate the original Thompson subgroup, with
intersection its center. Actual center coboundaries correct the two factors
of a fixed product so that each factor is fixed individually. This yields
the splitting used for element-conjugate generation in source 2.4.21, p.536.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_inside_fixed_product_of_center_coboundary
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (x : G) (hxT : x∈T) (hxS : x∉(d.S : Subgroup d.H).map d.H.subtype)
    (a : G) (haS : a∈(d.S : Subgroup d.H).map d.H.subtype) (ha2 : a^2=1)
    (hc : ∀ w ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G),
      Commute a w → ∃ v ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓
        centralizer (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G),
        w=v*(a*v*a⁻¹)⁻¹) :
    let U := sourceModule (d.block.map d.H.subtype)
    Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓ centralizer ({a} : Set G) =
      (U ⊓ centralizer ({a} : Set G)) ⊔
        (U.map (MulAut.conj x⁻¹).toMonoidHom ⊓ centralizer ({a} : Set G)) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let U := sourceModule (d.block.map d.H.subtype)
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have ht := d.lemma_2_4_8_1 hG T hST hsingle hK
  have hp := (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).2.2.2 x hxT hxS
  have hUV := source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS
  have hSU : S ≤ normalizer (U : Set G) := by
    change S ≤ normalizer (sourceModule (d.block.map d.H.subtype) : Set G)
    rw [(lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2]
    exact (map_subtype_le _).trans (le_normalizer_twoCore d.H)
  have hSe : S.map (MulAut.conj x⁻¹).toMonoidHom=S :=
    mem_normalizer_iff_map_conj_eq.mp (ht.2.1 (T.inv_mem hxT))
  have hSV : S ≤ normalizer (V : Set G) := by
    rw [←hSe]
    exact (map_mono hSU).trans (U.le_normalizer_map (MulAut.conj x⁻¹).toMonoidHom)
  have hVU : V ≤ normalizer (U : Set G) :=
    (le_sup_right.trans hp.1.ge).trans ((sSup_le fun _ h => h.1).trans hSU)
  let α := (MulAut.conj a).toMonoidHom
  have haI : a⁻¹=a := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ha2)
  have hα : Function.Involutive α := by
    intro r
    change a*(a*r*a⁻¹)*a⁻¹=r
    rw [haI]
    calc
      a*(a*r*a)*a = (a*a)*r*(a*a) := by group
      _ = r := by rw [←pow_two,ha2,one_mul,mul_one]
  let : IsElementaryAbelian 2 U := by
    let := hK.2.1.elementary
    exact IsElementaryAbelian.map (d.block.map d.H.subtype).subtype
  have he := fixed_sup_of_intersection_coboundaries U V hVU α hα
    (fun u hu => (mem_normalizer_iff.mp (hSU haS) u).mp hu)
    (fun v hv => (mem_normalizer_iff.mp (hSV haS) v).mp hv)
    (fun w hw => elemPow_eq_one_of_isElementaryAbelian w hw.1) (by
      intro w hw hwf
      have hwa : Commute a w := mul_inv_eq_iff_eq_mul.mp hwf
      obtain ⟨v,hv,he⟩ := hc w (hUV.le hw) hwa
      exact ⟨v,hUV.ge hv,he⟩)
  have hF : α.eqLocus (MonoidHom.id G)=centralizer ({a} : Set G) := by
    ext r
    change a*r*a⁻¹=r ↔ r∈centralizer ({a} : Set G)
    rw [mem_centralizer_singleton_iff,mul_inv_eq_iff_eq_mul]
    exact eq_comm
  rw [hF,←hp.1] at he
  exact he

theorem source_noncenterless_inside_fixed_product
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (x : G) (hxT : x∈T) (hxS : x∉(d.S : Subgroup d.H).map d.H.subtype)
    (a : G) (haS : a∈(d.S : Subgroup d.H).map d.H.subtype) (ha2 : a^2=1)
    (haR : a∉Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    let U := sourceModule (d.block.map d.H.subtype)
    Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ⊓ centralizer ({a} : Set G) =
      (U ⊓ centralizer ({a} : Set G)) ⊔
        (U.map (MulAut.conj x⁻¹).toMonoidHom ⊓ centralizer ({a} : Set G)) := by
  exact source_inside_fixed_product_of_center_coboundary d hG T hST hsingle hL hM hTM hunique
    x hxT hxS a haS ha2
    (source_noncenterless_inside_center_coboundary d hG T hST hsingle hL hM hTM hunique c hz a haS ha2 haR)
end CFSG.Quasithin.Chapter2.LinearShadows.Single
