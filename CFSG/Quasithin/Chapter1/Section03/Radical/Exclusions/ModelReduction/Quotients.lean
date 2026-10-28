module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockContract
public import Theory.GroupTheory.PGroup.Omega
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# The actual star quotient in the radical pushing-up argument

C.2.7 uses KR/C_KR(V), where V = Ω₁(Z(O₂(KR))). Its image K* is
different from the quotient K/O₂(K) in 1.3.4. The maps below retain both
quotients and their actual comparison homomorphism. If K/O₂(K) is
quasisimple and K* is nontrivial, that comparison is a perfect central
cover, so their quotients by their centers are isomorphic. No model
identification or case exclusion is assumed in constructing these maps.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma C.2.7, printed pp.145–147, and proof of 1.3.8, p.514.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction

variable {G : Type*} [Group G]

/-- V = Ω₁(Z(O₂(KR))), intrinsically in KR = K ⊔ R. -/
def starV (K R : Subgroup G) : Subgroup (K ⊔ R : Subgroup G) :=
  ((omega₁ (center (pCore 2 (K ⊔ R : Subgroup G))) (p := 2)).map
    (center (pCore 2 (K ⊔ R : Subgroup G))).subtype).map
      (pCore 2 (K ⊔ R : Subgroup G)).subtype

instance starV_characteristic (K R : Subgroup G) : (starV K R).Characteristic := by
  let _ := omega₁_characteristic (center (pCore 2 (K ⊔ R : Subgroup G))) (p := 2)
  exact inferInstanceAs (((omega₁ (center (pCore 2 (K ⊔ R : Subgroup G))) (p := 2)).map
    (center (pCore 2 (K ⊔ R : Subgroup G))).subtype).map
      (pCore 2 (K ⊔ R : Subgroup G)).subtype).Characteristic

/-- The centralizer kernel in the source definition of the star quotient. -/
def starKernel (K R : Subgroup G) : Subgroup (K ⊔ R : Subgroup G) :=
  centralizer (starV K R : Set (K ⊔ R : Subgroup G))

instance starKernel_characteristic (K R : Subgroup G) :
    (starKernel K R).Characteristic := inferInstanceAs
      (centralizer (starV K R : Set (K ⊔ R : Subgroup G))).Characteristic

/-- The ambient star quotient of C.2.7. -/
abbrev StarQuotient (K R : Subgroup G) := (K ⊔ R : Subgroup G) ⧸ starKernel K R

/-- The image of an ambient subgroup in the actual star quotient. -/
def starImage (K R A : Subgroup G) : Subgroup (StarQuotient K R) :=
  (A.subgroupOf (K ⊔ R)).map (QuotientGroup.mk' (starKernel K R))

/-- O₂(KR) centralizes the displayed omega-center, independently of C.2.7. -/
theorem core_le_starKernel (K R : Subgroup G) :
    pCore 2 (K ⊔ R : Subgroup G) ≤ starKernel K R := by
  intro x hx
  apply mem_centralizer_iff.mpr
  rintro v ⟨w, ⟨z, hz, rfl⟩, rfl⟩
  exact congrArg Subtype.val ((mem_center_iff.mp z.property) ⟨x, hx⟩).symm

/-- K maps onto its actual star image. -/
def toStarImage (K R : Subgroup G) : K →* starImage K R K :=
  ((QuotientGroup.mk' (starKernel K R)).subgroupMap (K.subgroupOf (K ⊔ R))).comp
    (subgroupOfEquivOfLe (show K ≤ K ⊔ R from le_sup_left)).symm.toMonoidHom

theorem toStarImage_surjective (K R : Subgroup G) :
    Function.Surjective (toStarImage K R) :=
  ((QuotientGroup.mk' (starKernel K R)).subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe (show K ≤ K ⊔ R from le_sup_left)).symm.surjective

/-- Normalization by R puts O₂(K) in the kernel of the map to K*. -/
theorem core_le_toStarImage_ker {K R : Subgroup G} (hRK : R ≤ normalizer K) :
    pCore 2 K ≤ (toStarImage K R).ker := by
  intro x hx
  apply Subtype.ext
  change QuotientGroup.mk' (starKernel K R)
    (⟨(x : G), (show K ≤ K ⊔ R from le_sup_left) x.property⟩ : (K ⊔ R : Subgroup G)) = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  apply core_le_starKernel
  have hm := pCoreIn_mono_of_normalizes (p := 2)
    (show K ≤ K ⊔ R from le_sup_left) (sup_le K.le_normalizer hRK)
    (mem_map_of_mem K.subtype hx)
  obtain ⟨y, hy, he⟩ := hm
  have he' : y = (⟨(x : G), (show K ≤ K ⊔ R from le_sup_left) x.property⟩ :
      (K ⊔ R : Subgroup G)) := Subtype.ext he
  exact he' ▸ hy

/-- The comparison from the 1.3.4 quotient onto K* in C.2.7. -/
def coreToStar {K R : Subgroup G} (hRK : R ≤ normalizer K) :
    XiQuotient K →* starImage K R K :=
  QuotientGroup.lift (pCore 2 K) (toStarImage K R) (core_le_toStarImage_ker hRK)

theorem coreToStar_mk {K R : Subgroup G} (hRK : R ≤ normalizer K) (k : K) :
    coreToStar hRK (QuotientGroup.mk' (pCore 2 K) k) = toStarImage K R k := rfl

theorem coreToStar_surjective {K R : Subgroup G} (hRK : R ≤ normalizer K) :
    Function.Surjective (coreToStar hRK) := by
  intro y
  obtain ⟨k, rfl⟩ := toStarImage_surjective K R y
  exact ⟨QuotientGroup.mk' (pCore 2 K) k, rfl⟩

/-- Nontriviality of the actual star image makes the kernel central. This
does not identify the two quotients themselves. -/
theorem coreToStar_ker_le_center {K R : Subgroup G} (hRK : R ≤ normalizer K)
    (hq : IsQuasisimple (XiQuotient K)) (hne : starImage K R K ≠ ⊥) :
    (coreToStar hRK).ker ≤ center (XiQuotient K) := by
  let _ := hq
  rcases IsQuasisimple.normal_le_center_or_eq_top (coreToStar hRK).ker with hc | ht
  · exact hc
  · exfalso
    apply hne
    apply bot_unique
    intro y hy
    obtain ⟨x, hx⟩ := coreToStar_surjective hRK ⟨y, hy⟩
    have hx1 : coreToStar hRK x = 1 := show x ∈ (coreToStar hRK).ker from ht ▸ mem_top x
    exact congrArg Subtype.val (hx.symm.trans hx1)

/-- The actual comparison, as a perfect central cover. -/
def coreStarCover {K R : Subgroup G} (hRK : R ≤ normalizer K)
    (hq : IsQuasisimple (XiQuotient K)) (hne : starImage K R K ≠ ⊥) :
    PerfectCentralCovering.Cover (XiQuotient K) (starImage K R K) where
  toMonoidHom := coreToStar hRK
  surjective := coreToStar_surjective hRK
  isPerfect := hq.toIsPerfect
  ker_le_center := coreToStar_ker_le_center hRK hq hne

/-- The central simple quotients used for comparing the two source model lists. -/
noncomputable def coreStarCenterEquiv {K R : Subgroup G} (hRK : R ≤ normalizer K)
    (hq : IsQuasisimple (XiQuotient K)) (hne : starImage K R K ≠ ⊥) :
    (XiQuotient K ⧸ center (XiQuotient K)) ≃*
      ((starImage K R K) ⧸ center (starImage K R K)) :=
  (coreStarCover hRK hq hne).quotientCenterEquiv

/-- When the 1.3.4 quotient has trivial center, its map to the nontrivial
star image is an isomorphism, rather than only a central cover. -/
noncomputable def coreStarEquivOfCenterEqBot {K R : Subgroup G}
    (hRK : R ≤ normalizer K) (hq : IsQuasisimple (XiQuotient K))
    (hne : starImage K R K ≠ ⊥) (hz : center (XiQuotient K) = ⊥) :
    XiQuotient K ≃* starImage K R K := by
  apply MulEquiv.ofBijective (coreToStar hRK)
  refine ⟨(MonoidHom.ker_eq_bot_iff _).mp ?_, coreToStar_surjective hRK⟩
  exact bot_unique (hz ▸ coreToStar_ker_le_center hRK hq hne)

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
