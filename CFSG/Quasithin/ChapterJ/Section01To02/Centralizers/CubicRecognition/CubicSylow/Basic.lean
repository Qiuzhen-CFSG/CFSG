module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.Quotients
public import Theory.SpecificGroups.AlternatingSix.M10.ThreeSylow

/-!
# The cubic Sylow subgroup in J.2.7

Starting with the literal marking N_G(B)/B ≅ Aut(A₆), every Sylow
three-subgroup R of N_G(B) has order 27, contains B, and has quotient
R/B ≅ C₃ × C₃. Compatibility with the specified M₁₀ puts R in C_G(B),
so B is central in R. All embeddings here are the original inclusions
into G, including the image of the quotient kernel.

This is the initial construction of the final cubic argument, not yet
the exclusion of E₂₇ or the ambient order-three fusion theorem. The
semidihedral action and the fusion input in J.2.7(7) are still needed
for those conclusions.

Source: Aschbacher–Smith, J.2.7, printed p.437 (PDF p.448).
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow
open Subgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The genuine ambient image of a Sylow subgroup of N_G(B). -/
def ambient (R : Sylow 3 c.NB) : Subgroup G :=
  (R : Subgroup c.NB).map c.NB.subtype

theorem ambient_le_NB (R : Sylow 3 c.NB) : ambient c R ≤ c.NB :=
  map_subtype_le _

def ambientEquiv (R : Sylow 3 c.NB) : R ≃* ambient c R :=
  (R : Subgroup c.NB).equivMapOfInjective c.NB.subtype c.NB.subtype_injective

theorem ambient_isPGroup (R : Sylow 3 c.NB) : IsPGroup 3 (ambient c R) :=
  R.isPGroup'.map c.NB.subtype

/-- The quotient homomorphism followed by the actual Aut(A₆) marking. -/
def markedMap (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6))) :
    c.NB →* MulAut (alternatingGroup (Fin 6)) :=
  e.toMonoidHom.comp c.normalizerQuotientMap

theorem markedMap_surjective
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6))) :
    Function.Surjective (markedMap c e) :=
  e.surjective.comp c.normalizerQuotientMap_surjective

theorem markedMap_ker
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6))) :
    (markedMap c e).ker = c.normalizerKernel := by
  rw [markedMap, MonoidHom.ker_comp_of_injective _ _ e.injective,
    c.normalizerQuotientMap_ker]

/-- The kernel still has its original ambient image. -/
theorem markedMap_ker_image
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6))) :
    (markedMap c e).ker.map c.NB.subtype = c.B := by
  rw [markedMap_ker]
  exact map_subgroupOf_eq_of_le le_normalizer

theorem normalizerKernel_card (hB : Nat.card c.B = 3) :
    Nat.card c.normalizerKernel = 3 :=
  (Nat.card_congr (subgroupOfEquivOfLe (show c.B ≤ c.NB from le_normalizer)).toEquiv).trans hB

theorem normalizer_card (hB : Nat.card c.B = 3)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6))) :
    Nat.card c.NB = 4320 := by
  rw [card_eq_card_quotient_mul_card_subgroup c.normalizerKernel,
    normalizerKernel_card c hB, Nat.card_congr e.toEquiv,
    AlternatingSix.ShadowLocal.card_aut]

theorem card (hB : Nat.card c.B = 3)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (R : Sylow 3 c.NB) : Nat.card R = 27 := by
  rw [R.card_eq_multiplicity, normalizer_card c hB e]
  decide +kernel

theorem ambient_card (hB : Nat.card c.B = 3)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (R : Sylow 3 c.NB) : Nat.card (ambient c R) = 27 :=
  (Nat.card_congr (ambientEquiv c R).symm.toEquiv).trans (card c hB e R)

theorem kernel_le (hB : Nat.card c.B = 3) (R : Sylow 3 c.NB) :
    c.normalizerKernel ≤ (R : Subgroup c.NB) :=
  (IsPGroup.of_card (show Nat.card c.normalizerKernel = 3 ^ 1 by
    simpa using normalizerKernel_card c hB)).le_sylow_of_normal R

theorem B_le (hB : Nat.card c.B = 3) (R : Sylow 3 c.NB) : c.B ≤ ambient c R := by
  rw [← map_subgroupOf_eq_of_le (show c.B ≤ c.NB from le_normalizer)]
  exact map_mono (kernel_le c hB R)

/-- R's actual image in the marked quotient. -/
def imageSylow (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (R : Sylow 3 c.NB) : Sylow 3 (MulAut (alternatingGroup (Fin 6))) :=
  R.mapSurjective (markedMap_surjective c e)

/-- B restricted to R, inside N_G(B). -/
abbrev kernel (R : Sylow 3 c.NB) : Subgroup R :=
  c.normalizerKernel.subgroupOf (R : Subgroup c.NB)

instance kernel_normal (R : Sylow 3 c.NB) : (kernel c R).Normal :=
  inferInstanceAs (c.normalizerKernel.comap (R : Subgroup c.NB).subtype).Normal

def quotientMap (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (R : Sylow 3 c.NB) : R →* imageSylow c e R :=
  (markedMap c e).subgroupMap (R : Subgroup c.NB)

theorem quotientMap_surjective
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6))) (R : Sylow 3 c.NB) :
    Function.Surjective (quotientMap c e R) :=
  (markedMap c e).subgroupMap_surjective (R : Subgroup c.NB)

theorem quotientMap_ker
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6))) (R : Sylow 3 c.NB) :
    (quotientMap c e R).ker = kernel c R := by
  ext x
  change ((markedMap c e).subgroupMap (R : Subgroup c.NB)) x = 1 ↔ _
  rw [← Subtype.val_inj]
  change (markedMap c e) (x : c.NB) = 1 ↔ _
  rw [← MonoidHom.mem_ker, markedMap_ker]
  rfl

/-- The literal R/B quotient, with a genuine isomorphism to E₉. -/
def quotientEquiv
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6))) (R : Sylow 3 c.NB) :
    R ⧸ kernel c R ≃* AlternatingSix.M10.LocalGeometry.NineCoordinates :=
  (QuotientGroup.quotientMulEquivOfEq (quotientMap_ker c e R).symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective (quotientMap c e R)
      (quotientMap_surjective c e R)).trans
        (AlternatingSix.M10.ThreeSylow.equiv (imageSylow c e R)))

theorem kernel_image (hB : Nat.card c.B = 3) (R : Sylow 3 c.NB) :
    (kernel c R).map (c.NB.subtype.comp (R : Subgroup c.NB).subtype) = c.B := by
  rw [← map_map, map_subgroupOf_eq_of_le (kernel_le c hB R)]
  exact map_subgroupOf_eq_of_le le_normalizer

instance ambientKernel_normal (R : Sylow 3 c.NB) :
    (c.B.subgroupOf (ambient c R)).Normal :=
  normal_subgroupOf_of_le_normalizer (ambient_le_NB c R)

theorem kernel_map_ambientEquiv (R : Sylow 3 c.NB) :
    (kernel c R).map (ambientEquiv c R).toMonoidHom = c.B.subgroupOf (ambient c R) := by
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact hr
  · intro hx
    refine ⟨(ambientEquiv c R).symm x, ?_, (ambientEquiv c R).apply_symm_apply x⟩
    have he := congrArg Subtype.val ((ambientEquiv c R).apply_symm_apply x)
    change (((ambientEquiv c R).symm x : c.NB) : G) = (x : G) at he
    change (((ambientEquiv c R).symm x : c.NB) : G) ∈ c.B
    rw [he]
    exact hx

/-- The same quotient taken directly in the ambient subgroup of G. -/
def ambientQuotientEquiv
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6))) (R : Sylow 3 c.NB) :
    ambient c R ⧸ c.B.subgroupOf (ambient c R) ≃*
      AlternatingSix.M10.LocalGeometry.NineCoordinates :=
  (QuotientGroup.congr (kernel c R) (c.B.subgroupOf (ambient c R))
    (ambientEquiv c R) (kernel_map_ambientEquiv c R)).symm.trans
    (quotientEquiv c e R)

/-- Compatibility of the literal centralizer image with M₁₀ forces R
to centralize the original B. -/
theorem ambient_le_GB (hB : Nat.card c.B = 3)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension)
    (R : Sylow 3 c.NB) : ambient c R ≤ c.GB := by
  have hker : (markedMap c e).ker ≤ c.GB.subgroupOf c.NB := by
    rw [markedMap_ker]
    intro x hx
    exact c.B_le_GB_of_card hB hx
  have himage : (c.GB.subgroupOf c.NB).map (markedMap c e) =
      AlternatingSix.M10.extension := by
    rw [markedMap, ← map_map]
    exact hM
  have hr : (R : Subgroup c.NB) ≤ c.GB.subgroupOf c.NB := by
    rw [← comap_map_eq_self hker, himage]
    exact map_le_iff_le_comap.mp
      (AlternatingSix.M10.ThreeSylow.le_extension (imageSylow c e R))
  rintro _ ⟨x, hx, rfl⟩
  exact hr hx

theorem B_le_center (hB : Nat.card c.B = 3)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension)
    (R : Sylow 3 c.NB) : c.B.subgroupOf (ambient c R) ≤ center (ambient c R) := by
  intro b hb
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (((ambient_le_GB c hB e hM R x.property) b hb).symm)

end CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow
