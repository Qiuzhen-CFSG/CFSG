module
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The line-normalizer quotient inside an element centralizer

Embed C_L(t) into C_G(t), take the normalizer of a central subgroup B of
C_L(t) there, and quotient by the entire embedded B. The resulting map
has kernel exactly B. Membership in the image of the original normalizer
N_G(L) is detected on every lift, because B lies in L.

These generic constructions are used in the first F.4.42 quotient for U₅.
They follow the existing unitary-four short-line construction without
importing its source-specific proof dependencies.
-/

@[expose] public noncomputable section
open Subgroup
namespace Theory.GroupTheory.CentralizerLineQuotient
variable {G : Type*} [Group G] (L : Subgroup G) (t : L)

/-- The actual residual centralizer embeds in the ambient centralizer. -/
def shortCentralizerEmbedding : centralizer ({t} : Set L) →*
    centralizer ({t.val} : Set G) :=
  (L.subtype.comp (centralizer ({t} : Set L)).subtype).codRestrict _ (by
    intro x
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property)))

theorem shortCentralizerEmbedding_injective :
    Function.Injective (shortCentralizerEmbedding L t) := by
  intro x y he
  have hh : x.val.val = y.val.val :=
    congrArg (fun a : centralizer ({t.val} : Set G) => a.val) he
  exact Subtype.ext (Subtype.ext hh)

/-- The normalizer is taken inside the actual ambient short-root centralizer. -/
def shortLineNormalizer (U : Subgroup (centralizer ({t} : Set L))) :
    Subgroup (centralizer ({t.val} : Set G)) :=
  normalizer (U.map (shortCentralizerEmbedding L t) : Set _)

/-- The original entire line in its ambient normalizer. -/
def shortLineKernel (U : Subgroup (centralizer ({t} : Set L))) :
    Subgroup (shortLineNormalizer L t U) :=
  (U.map (shortCentralizerEmbedding L t)).subgroupOf (shortLineNormalizer L t U)

instance shortLineKernel_normal (U : Subgroup (centralizer ({t} : Set L))) :
    (shortLineKernel L t U).Normal :=
  normal_subgroupOf_of_le_normalizer le_rfl

/-- Centrality of the local line places the whole residual centralizer in
the actual ambient line normalizer. -/
def shortLineNormalizerMap (U : Subgroup (centralizer ({t} : Set L)))
    (hU : U ≤ center (centralizer ({t} : Set L))) :
    centralizer ({t} : Set L) →* shortLineNormalizer L t U :=
  (shortCentralizerEmbedding L t).codRestrict _ (by
    intro x
    apply Subgroup.centralizer_le_normalizer
    rintro y ⟨u,hu,rfl⟩
    exact (map_mul _ u x).symm.trans
      ((congrArg (shortCentralizerEmbedding L t) (mem_center_iff.mp (hU hu) x).symm).trans
        (map_mul _ x u)))

/-- The literal homomorphism into N_{C_G(t)}(U)/U. -/
def shortLineQuotientMap (U : Subgroup (centralizer ({t} : Set L)))
    (hU : U ≤ center (centralizer ({t} : Set L))) :
    centralizer ({t} : Set L) →* shortLineNormalizer L t U ⧸ shortLineKernel L t U :=
  (QuotientGroup.mk' (shortLineKernel L t U)).comp (shortLineNormalizerMap L t U hU)

/-- The kernel is the whole original line, without an extra central kernel. -/
theorem shortLineQuotientMap_ker (U : Subgroup (centralizer ({t} : Set L)))
    (hU : U ≤ center (centralizer ({t} : Set L))) :
    (shortLineQuotientMap L t U hU).ker = U := by
  ext x
  change QuotientGroup.mk' (shortLineKernel L t U)
    (shortLineNormalizerMap L t U hU x) = 1 ↔ x ∈ U
  apply (QuotientGroup.eq_one_iff _).trans
  change shortCentralizerEmbedding L t x ∈ U.map (shortCentralizerEmbedding L t) ↔ x ∈ U
  constructor
  · rintro ⟨y,hy,he⟩
    exact (shortCentralizerEmbedding_injective L t he) ▸ hy
  · exact mem_map_of_mem _


/-- Inclusion of the line normalizer into the original ambient group. -/
def shortLineAmbientEmbedding (U : Subgroup (centralizer ({t} : Set L))) :
    shortLineNormalizer L t U →* G :=
  (centralizer ({t.val} : Set G)).subtype.comp (shortLineNormalizer L t U).subtype

/-- The original normalizer intersected with the ambient short-line normalizer. -/
def shortLineLocal (U : Subgroup (centralizer ({t} : Set L))) :
    Subgroup (shortLineNormalizer L t U) :=
  (normalizer (L : Set G)).comap (shortLineAmbientEmbedding L t U)

/-- Its literal image modulo the entire short-root line. -/
def shortLineLocalQuotient (U : Subgroup (centralizer ({t} : Set L))) :
    Subgroup (shortLineNormalizer L t U ⧸ shortLineKernel L t U) :=
  (shortLineLocal L t U).map (QuotientGroup.mk' (shortLineKernel L t U))

/-- The entire quotient kernel lies in the original local subgroup. -/
theorem shortLineKernel_le_local (U : Subgroup (centralizer ({t} : Set L))) :
    shortLineKernel L t U ≤ shortLineLocal L t U := by
  intro a ha
  obtain ⟨u,hu,he⟩ := ha
  change a.val.val ∈ normalizer (L : Set G)
  have hh := congrArg (fun x : centralizer ({t.val} : Set G) => x.val) he
  change u.val.val = a.val.val at hh
  exact hh ▸ L.le_normalizer u.val.property

/-- The original residual centralizer maps into the quotient local subgroup. -/
theorem shortLineQuotientMap_mem_local (U : Subgroup (centralizer ({t} : Set L)))
    (hU : U ≤ center (centralizer ({t} : Set L))) (a : centralizer ({t} : Set L)) :
    shortLineQuotientMap L t U hU a ∈ shortLineLocalQuotient L t U :=
  mem_map_of_mem _ (L.le_normalizer a.val.property)

/-- Membership in the quotient local subgroup is detected on every lift;
the full line is contained in the local subgroup. -/
theorem shortLineLocalQuotient_mk_iff (U : Subgroup (centralizer ({t} : Set L)))
    (a : shortLineNormalizer L t U) :
    QuotientGroup.mk' (shortLineKernel L t U) a ∈ shortLineLocalQuotient L t U ↔
      a.val.val ∈ normalizer (L : Set G) := by
  constructor
  · rintro ⟨b,hb,he⟩
    have hk : b⁻¹*a ∈ shortLineKernel L t U := QuotientGroup.eq.mp he
    have hh := (shortLineLocal L t U).mul_mem hb (shortLineKernel_le_local L t U hk)
    change b*(b⁻¹*a) ∈ shortLineLocal L t U at hh
    change a ∈ shortLineLocal L t U
    simpa only [mul_inv_cancel_left] using hh
  · intro ha
    exact mem_map_of_mem _ ha

end Theory.GroupTheory.CentralizerLineQuotient
