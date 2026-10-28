module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Lifting

/-!
# The ambient Borel quotient in F.1.3(1)

Source: Aschbacher–Smith, `refs/quasithin.pdf`, printed pp.259–260.
For an actual local Sylow T = S ∩ L, the ambient Borel B = N_L(S ∩ L)
is identified with the intrinsic normalizer of T. Restricting L → L/O₂(L)
to B is surjective onto the quotient Sylow normalizer and has kernel O₂(L),
regarded as a normal subgroup of B. The first isomorphism theorem therefore
identifies B/O₂(L) with this normalizer.

The representative formulas retain the actual quotient projection, including
when it is followed by an isomorphism to a concrete rank-one model. Combined
with that model's point-stabilizer or matrix-Borel theorem, they identify the
source Borel quotient with the concrete Borel. These transport statements
require only the displayed local Sylow data; the parent module proves the
rank-one properties from F.1.1.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] (L S : Subgroup G)

/-- The ambient Borel, restricted to L, is the intrinsic Sylow normalizer. -/
theorem borel_subgroupOf_eq_sylowNormalizer (T : Sylow 2 L)
    (hT : (T : Subgroup L).map L.subtype = S ⊓ L) :
    (borel L S).subgroupOf L = sylowNormalizer T := by
  have hc : (S ⊓ L).subgroupOf L = (T : Subgroup L) := by
    rw [← hT]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  change (L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)).subgroupOf L = _
  rw [Subgroup.inf_subgroupOf_left, Subgroup.subgroupOf_normalizer_eq inf_le_right, hc]

/-- The whole embedded two-core lies in the Borel when S ∩ L is Sylow. -/
theorem twoCore_le_borel_of_sylow (T : Sylow 2 L)
    (hT : (T : Subgroup L).map L.subtype = S ⊓ L) : twoCore L ≤ borel L S := by
  calc
    twoCore L ≤ (T : Subgroup L).map L.subtype :=
      Subgroup.map_mono (pCore_isPGroup.le_sylow_of_normal T)
    _ = S ⊓ L := hT
    _ ≤ borel L S := localSylow_le_borel L S

/-- Identify the ambient and intrinsic normalizers using their actual inclusions. -/
def borelNormalizerEquiv (T : Sylow 2 L)
    (hT : (T : Subgroup L).map L.subtype = S ⊓ L) :
    borel L S ≃* sylowNormalizer T :=
  (Subgroup.subgroupOfEquivOfLe (borel_le L S)).symm.trans
    (MulEquiv.subgroupCongr (borel_subgroupOf_eq_sylowNormalizer L S T hT))

/-- The embedded two-core of L is normal relative to its Borel. -/
theorem twoCore_normal_in_borel : ((twoCore L).subgroupOf (borel L S)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    ((borel_le L S).trans (L.le_normalizer.trans
      (Subgroup.normalizer_le_normalizer_characteristic_image L (pCore 2 L))))

variable [Finite L]

/-- Restrict the actual local quotient projection to the ambient Borel. -/
def borelProjection (T : Sylow 2 L)
    (hT : (T : Subgroup L).map L.subtype = S ⊓ L) :
    borel L S →* sylowNormalizer (quotientSylow T) :=
  (normalizerProjection T).comp (borelNormalizerEquiv L S T hT).toMonoidHom

/-- The restricted map agrees with L → L/O₂(L) on each element. -/
@[simp] theorem borelProjection_apply (T : Sylow 2 L)
    (hT : (T : Subgroup L).map L.subtype = S ⊓ L) (b : borel L S) :
    (borelProjection L S T hT b : L ⧸ pCore 2 L) =
      QuotientGroup.mk' (pCore 2 L) ⟨b, b.property.1⟩ := rfl

/-- The Borel maps onto the quotient Sylow normalizer. -/
theorem borelProjection_surjective (T : Sylow 2 L)
    (hT : (T : Subgroup L).map L.subtype = S ⊓ L) :
    Function.Surjective (borelProjection L S T hT) :=
  (normalizerProjection_surjective T).comp (borelNormalizerEquiv L S T hT).surjective

/-- The restricted projection has kernel exactly the relative embedded two-core. -/
theorem borelProjection_ker (T : Sylow 2 L)
    (hT : (T : Subgroup L).map L.subtype = S ⊓ L) :
    (borelProjection L S T hT).ker = (twoCore L).subgroupOf (borel L S) := by
  ext b
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  change QuotientGroup.mk' (pCore 2 L) (⟨b, b.property.1⟩ : L) = 1 ↔
    (b : G) ∈ (pCore 2 L).map L.subtype
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hb
    exact ⟨⟨b, b.property.1⟩, hb, rfl⟩
  · rintro ⟨x, hx, hxb⟩
    have he : x = (⟨b, b.property.1⟩ : L) := Subtype.ext hxb
    exact he ▸ hx

/-- The source quotient B/O₂(L) is the quotient Sylow normalizer. -/
noncomputable def borelQuotientEquiv (T : Sylow 2 L)
    (hT : (T : Subgroup L).map L.subtype = S ⊓ L) :
    letI := twoCore_normal_in_borel L S
    borel L S ⧸ (twoCore L).subgroupOf (borel L S) ≃*
      sylowNormalizer (quotientSylow T) :=
  letI := twoCore_normal_in_borel L S
  (QuotientGroup.quotientMulEquivOfEq (borelProjection_ker L S T hT).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (borelProjection_surjective L S T hT))

/-- The quotient equivalence is induced by the actual restricted projection. -/
@[simp] theorem borelQuotientEquiv_mk (T : Sylow 2 L)
    (hT : (T : Subgroup L).map L.subtype = S ⊓ L) (b : borel L S) :
    borelQuotientEquiv L S T hT (QuotientGroup.mk b) = borelProjection L S T hT b := rfl

variable {K : Type*} [Group K]

/-- Transport B/O₂(L) into a chosen concrete quotient model, retaining its actual Sylow. -/
noncomputable def borelQuotientModelEquiv (T : Sylow 2 L)
    (hT : (T : Subgroup L).map L.subtype = S ⊓ L) (e : (L ⧸ pCore 2 L) ≃* K) :
    letI := twoCore_normal_in_borel L S
    borel L S ⧸ (twoCore L).subgroupOf (borel L S) ≃*
      sylowNormalizer ((quotientSylow T).mapSurjective (f := e.toMonoidHom) e.surjective) :=
  letI := twoCore_normal_in_borel L S
  (borelQuotientEquiv L S T hT).trans
    ((e.subgroupMap (sylowNormalizer (quotientSylow T))).trans
      (MulEquiv.subgroupCongr
        (by
          exact Subgroup.map_equiv_normalizer_eq
            (quotientSylow T : Subgroup (L ⧸ pCore 2 L)) e)))

/-- The model equivalence commutes with the original local quotient projection. -/
@[simp] theorem borelQuotientModelEquiv_mk (T : Sylow 2 L)
    (hT : (T : Subgroup L).map L.subtype = S ⊓ L) (e : (L ⧸ pCore 2 L) ≃* K)
    (b : borel L S) :
    (borelQuotientModelEquiv L S T hT e (QuotientGroup.mk b) : K) =
      e (QuotientGroup.mk' (pCore 2 L) ⟨b, b.property.1⟩) := rfl

end CFSG.Quasithin.ChapterF.Source
