module

public import Stellmacher.Recognition.Parrott.NormalizerRootCosetCounts
public import Stellmacher.Recognition.Parrott.NormalizerRootSets
public import Theory.GroupTheory.ElementaryCosetSquareGeometry

/-!
# Coordinates for the two elementary root cosets

The candidate coordinates of K = O₂(N_G(F)) are xⁱcʲbᵏq, with i,j < 4,
k < 2 and q in the supplied F. All these words lie in the actual core.
There are exactly 1024 coordinate tuples. Uniqueness therefore implies
exhaustion, using the supplied order of K.

The square exclusion and centralizer count already hold throughout xF:
both properties are constant on elementary cosets. The general calculation
is separated into coordinate uniqueness and square geometry of words; these
are explicit premises until their construction and calculation are proved.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.682, the sixteen-root paragraph, using equations (1)–(19).
-/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

namespace ParrottSylowGeneratorData

/-- Ordered candidate coordinates, retaining the literal supplied F. -/
public abbrev NormalizerRootParameters (_f : ParrottSylowGeneratorData n) :=
  Fin 4 × Fin 4 × Fin 2 × e.F

/-- The ordered word uses the supplied x,c,b and a right factor in F. -/
@[expose] public def normalizerRootWord (f : ParrottSylowGeneratorData n)
    (p : f.NormalizerRootParameters) : G :=
  f.x ^ p.1.val * f.c ^ p.2.1.val * f.b ^ p.2.2.1.val * p.2.2.2

/-- Every candidate word lies in the actual normalizer core. -/
public theorem normalizerRootWord_mem_core (f : ParrottSylowGeneratorData n)
    (p : f.NormalizerRootParameters) :
    f.normalizerRootWord p ∈ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype := by
  let K := (pCore 2 (normalizer (e.F : Set G))).map
    (normalizer (e.F : Set G)).subtype
  have hc : f.c ∈ K := by
    rw [show K = _ from n.core_eq_sylow_centralizer]
    exact ⟨f.local_mem_sylow.2.2.2.2.2.2.2.1,
      mem_centralizer_singleton_iff.mpr
        ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq10_ct).eq⟩
  have hb : f.b ∈ K := by
    rw [show K = _ from n.core_eq_sylow_centralizer]
    exact ⟨f.local_mem_sylow.2.2.2.2.2.2.1,
      mem_centralizer_singleton_iff.mpr f.comm_bt.eq⟩
  exact K.mul_mem (K.mul_mem (K.mul_mem
    (K.pow_mem f.x_mem_normalizer_core _) (K.pow_mem hc _)) (K.pow_mem hb _))
    (n.omega_le_core (n.elementary_le_omega p.2.2.2.property))

/-- The proposed coordinates have precisely the known cardinality of K. -/
public theorem normalizerRootParameters_card (f : ParrottSylowGeneratorData n) :
    Nat.card f.NormalizerRootParameters = 1024 := by
  simp only [NormalizerRootParameters, Nat.card_prod, Nat.card_fin, e.card]

/-- Uniqueness of the ordered words implies that they exhaust the core. -/
public theorem normalizerRootWord_range_of_injective [Finite G]
    (f : ParrottSylowGeneratorData n) (hinj : Function.Injective f.normalizerRootWord) :
    Set.range f.normalizerRootWord =
      ((pCore 2 (normalizer (e.F : Set G))).map
        (normalizer (e.F : Set G)).subtype : Set G) := by
  apply Set.eq_of_subset_of_ncard_le
  · rintro g ⟨p, rfl⟩
    exact f.normalizerRootWord_mem_core p
  · rw [Set.ncard_range_of_injective hinj, f.normalizerRootParameters_card]
    change Nat.card ((pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype) ≤ 1024
    rw [card_map_of_injective (normalizer (e.F : Set G)).subtype_injective, n.core_card]
  · exact Set.toFinite _

/-- In K, omega membership is detected by the action on the supplied v. -/
public theorem normalizer_core_mem_omega_iff_commute_v
    (_f : ParrottSylowGeneratorData n) (m : G)
    (hm : m ∈ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype) :
    m ∈ (omega₁ (pCore 2 (normalizer (e.F : Set G))) (p := 2)).map
      ((normalizer (e.F : Set G)).subtype.comp
        (pCore 2 (normalizer (e.F : Set G))).subtype) ↔ Commute m n.v := by
  rw [n.omega_eq_centralizer]
  let ZU := (center (omega₁ (pCore 2 (normalizer (e.F : Set G))) (p := 2))).map
    (((normalizer (e.F : Set G)).subtype.comp
      (pCore 2 (normalizer (e.F : Set G))).subtype).comp
        (omega₁ (pCore 2 (normalizer (e.F : Set G))) (p := 2)).subtype)
  have hvZU : n.v ∈ ZU := by
    rw [show ZU = _ from n.omega_center_eq]
    exact mem_sup_right (mem_zpowers n.v)
  constructor
  · intro hh
    exact (hh.2 n.v hvZU).symm
  · intro hmv
    have hmz := mem_centralizer_singleton_iff.mp
      (e.sylow_le_centralizer (n.core_le_sylow hm))
    have hmt := mem_centralizer_singleton_iff.mp
      ((n.core_eq_sylow_centralizer ▸ hm).2)
    have hZ : ZU ≤ centralizer ({m} : Set G) := by
      rw [show ZU = _ from n.omega_center_eq]
      exact sup_le (sup_le
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hmz.symm))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hmt.symm)))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hmv.symm.eq))
    exact ⟨hm, fun g hg => mem_centralizer_singleton_iff.mp (hZ hg)⟩

/-- Assembly of the general geometry from uniqueness and a calculation on
ordered words. The two premises are separate, independently provable inputs. -/
public theorem normalizer_root_geometry_of_word_calculation [Finite G]
    (f : ParrottSylowGeneratorData n)
    (hinj : Function.Injective f.normalizerRootWord)
    (hcalc : ∀ p : f.NormalizerRootParameters,
      f.normalizerRootWord p ∉
        (omega₁ (pCore 2 (normalizer (e.F : Set G))) (p := 2)).map
          ((normalizer (e.F : Set G)).subtype.comp
            (pCore 2 (normalizer (e.F : Set G))).subtype) →
      orderOf (f.normalizerRootWord p) = 4 →
      (f.normalizerRootWord p) ^ 2 ∉ e.F ∧
      Nat.card (e.F ⊓ centralizer ({f.normalizerRootWord p} : Set G) : Subgroup G) = 8 ∧
      ∀ q : f.NormalizerRootParameters,
        (f.normalizerRootWord q) ^ 2 = (f.normalizerRootWord p) ^ 2 →
        (f.normalizerRootWord p)⁻¹ * f.normalizerRootWord q ∈ e.F ∨
          f.normalizerRootWord p * f.normalizerRootWord q ∈ e.F) :
    let N := normalizer (e.F : Set G)
    let K := (pCore 2 N).map N.subtype
    let U := (omega₁ (pCore 2 N) (p := 2)).map (N.subtype.comp (pCore 2 N).subtype)
    ∀ m ∈ K, m ∉ U → orderOf m = 4 →
      m ^ 2 ∉ e.F ∧ Nat.card (e.F ⊓ centralizer ({m} : Set G) : Subgroup G) = 8 ∧
      ∀ g ∈ K, g ^ 2 = m ^ 2 → m⁻¹ * g ∈ e.F ∨ m * g ∈ e.F := by
  intro N K U m hm hmU hm4
  have hcover : Set.range f.normalizerRootWord = (K : Set G) :=
    f.normalizerRootWord_range_of_injective hinj
  have hmp : m ∈ Set.range f.normalizerRootWord := by rw [hcover]; exact hm
  obtain ⟨p, rfl⟩ := hmp
  obtain ⟨hsq, hcard, hroots⟩ := hcalc p hmU hm4
  refine ⟨hsq, hcard, ?_⟩
  intro g hg hg2
  have hgq : g ∈ Set.range f.normalizerRootWord := by rw [hcover]; exact hg
  obtain ⟨q, rfl⟩ := hgq
  exact hroots q hg2

/-- Every element of xF has square outside F and centralizer of order eight
inside F, without any additional order assumption. -/
public theorem x_coset_square_geometry [Finite G] (f : ParrottSylowGeneratorData n)
    (m : G) (hm : f.x⁻¹ * m ∈ e.F) :
    m ^ 2 ∉ e.F ∧ Nat.card (e.F ⊓ centralizer ({m} : Set G) : Subgroup G) = 8 := by
  let _ := e.elementary
  have heq : m = f.x * (f.x⁻¹ * m) := by simp
  rw [heq]
  exact ⟨fun hh => f.x_sq_not_mem_elementary
    ((mul_sq_mem_iff_of_mem_normalizer e.F f.x
      (map_subtype_le _ f.x_mem_normalizer_core) _ hm).mp hh),
    by rw [inf_centralizer_singleton_mul_of_mem e.F f.x _ hm]
       exact f.x_elementary_centralizer_card⟩

end ParrottSylowGeneratorData
end Stellmacher.Recognition
