module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Preparation.LocalSetup
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.SylowKernelCore
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks

/-!
# The relative core and plane preimage in 15.3.24

Put A = Y₊S and B = Y₊(S ∩ L). Relative normalization gives
B = A ∩ L and A normalizes B. Consequently O₂(B) = O₂(A) ∩ L,
where each core is embedded in the original ambient group. The marked
component quotient therefore sends the actual R ∩ L to the two-core of
the actual B image.

If that image is a maximal plane stabilizer, the properness L ≰ M forces
M ∩ L = B. The kernel containment recovers the literal preimage in L,
and the model two-core calculation identifies its unipotent radical.
The model recognition premise is explicit; it is not proved here.

Source: Aschbacher–Smith, 15.3.24, first two paragraphs of the proof,
combined manuscript (1 March 2004), printed p.1129.
-/

public section

open Subgroup BinaryLinear.OuterCyclic
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Preparation

variable {G : Type*} [Group G] {d : LocalData G} {I : Subgroup G}
variable {c : ComponentWitness d I}

/-- Dedekind's identity for the actual normalized product Y₊S. -/
theorem base_join_eq_intersection (h : Earlier d c) :
    d.Yplus ⊔ (d.S ⊓ c.L) = (d.Yplus ⊔ d.S) ⊓ c.L := by
  apply SetLike.coe_injective
  rw [coe_mul_of_right_le_normalizer_left _ _
    (inf_le_left.trans h.sylow_normalizes_yplus),
    mul_inf_assoc _ _ _ h.yplus_le, coe_inf,
    coe_mul_of_right_le_normalizer_left _ _ h.sylow_normalizes_yplus]

/-- The base product is normal relative to Y₊S, with no ambient normality assertion. -/
theorem join_normalizes_base (h : Earlier d c) :
    d.Yplus ⊔ d.S ≤ normalizer ((d.Yplus ⊔ (d.S ⊓ c.L) : Subgroup G) : Set G) := by
  apply sup_le
  · exact le_sup_left.trans (d.Yplus ⊔ (d.S ⊓ c.L)).le_normalizer
  · apply le_trans (le_inf h.sylow_normalizes_yplus ?_)
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
    exact (le_inf d.S.le_normalizer h.sylow_normalizes_component).trans
      inf_normalizer_le_normalizer_inf

/-- The actual radical intersection is the embedded core of the component base product. -/
theorem radical_intersection_eq_base_core (h : Earlier d c) :
    d.R ⊓ c.L = (d.Yplus ⊔ (d.S ⊓ c.L)).pCoreIn 2 := by
  have hBA : d.Yplus ⊔ (d.S ⊓ c.L) ≤ d.Yplus ⊔ d.S :=
    sup_le_sup_left inf_le_left _
  apply le_antisymm
  · apply le_trans ?_ (inf_pCoreIn_le_of_le 2 hBA)
    exact le_inf (by
      rw [base_join_eq_intersection h]
      exact inf_le_inf (pCoreIn_le 2 _) le_rfl) inf_le_left
  · exact le_inf (pCoreIn_mono_of_normalizes hBA (join_normalizes_base h))
      ((pCoreIn_le 2 _).trans (sup_le h.yplus_le inf_le_right))

/-- The full kernel of the component quotient lies in the base product. -/
theorem component_core_le_base (h : Earlier d c) :
    c.L.pCoreIn 2 ≤ d.Yplus ⊔ (d.S ⊓ c.L) := by
  apply le_trans (le_inf h.core_le_R (pCoreIn_le 2 c.L))
  rw [radical_intersection_eq_base_core h]
  exact pCoreIn_le 2 _

/-- The base product lies in the literal intersection with M. -/
theorem base_le_intersection (h : Earlier d c) :
    d.Yplus ⊔ (d.S ⊓ c.L) ≤ d.M ⊓ c.L := by
  apply sup_le
  · exact le_inf (by rw [← h.theta_local]; exact (theta_le _).trans inf_le_left)
      h.yplus_le
  · exact inf_le_inf (inf_le_left.trans d.sylow_le) le_rfl

/-- The marked image functor transports embedded cores through its two-group kernel. -/
theorem modelImage_pCoreIn [Finite G] {L X : Subgroup G} {n : ℕ} (hn : 0 < n)
    (e : (L ⧸ pCore 2 L) ≃* Projective n) (hXL : X ≤ L) :
    modelImage hn e (X.pCoreIn 2) = (modelImage hn e X).pCoreIn 2 := by
  let : Finite (LinearGroup n) := Finite.of_injective
    (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
  have he : (X.pCoreIn 2).subgroupOf L = (X.subgroupOf L).pCoreIn 2 := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 X).trans hXL),
      map_pCoreIn_of_injective 2 _ _ L.subtype_injective,
      map_subgroupOf_eq_of_le hXL]
  unfold modelImage
  rw [he]
  apply map_pCoreIn_of_ker_isPGroup
  rw [linearAction_ker]
  exact pCore_isPGroup

/-- A plane identification of the base image identifies the actual radical image. -/
theorem radical_image_of_base_image [Finite G] (h : Earlier d c)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Projective 4)
    (W : Submodule (ZMod 2) (Space 4))
    (hW : modelImage (by decide) e (d.Yplus ⊔ (d.S ⊓ c.L)) = BinaryLinear.parabolic W) :
    modelImage (by decide) e (d.R ⊓ c.L) = BinaryLinear.radical W := by
  rw [radical_intersection_eq_base_core h,
    modelImage_pCoreIn (by decide) e (sup_le h.yplus_le inf_le_right), hW]
  exact BinaryLinear.SmallParabolicLevi.map_twoCore_eq_radical W

/-- The given component Sylow maps onto an actual Sylow subgroup of the linear model. -/
theorem exists_model_sylow [Finite G] (h : Earlier d c) {n : ℕ} (hn : 0 < n)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Projective n) :
    ∃ P : Sylow 2 (LinearGroup n),
      (P : Subgroup (LinearGroup n)) = modelImage hn e (d.S ⊓ c.L) := by
  obtain ⟨Q, hQ⟩ := h.sylow_component
  refine ⟨Q.mapSurjective (linearAction_surjective hn e), ?_⟩
  change (Q : Subgroup c.L).map (linearAction hn e) = _
  have he : (d.S ⊓ c.L).subgroupOf c.L = (Q : Subgroup c.L) := by
    rw [← hQ]
    exact comap_map_eq_self_of_injective c.L.subtype_injective _
  rw [modelImage, he]

/-- A maximal base image forces the literal intersection to equal the base product. -/
theorem intersection_join_of_coatom [Finite G] (h : Earlier d c) {n : ℕ} (hn : 0 < n)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Projective n)
    (hmax : IsCoatom (modelImage hn e (d.Yplus ⊔ (d.S ⊓ c.L)))) :
    d.M ⊓ c.L = d.Yplus ⊔ (d.S ⊓ c.L) := by
  let B := d.Yplus ⊔ (d.S ⊓ c.L)
  let f := linearAction hn e
  have hker : f.ker ≤ B.subgroupOf c.L := by
    rw [linearAction_ker]
    intro l hl
    exact component_core_le_base h (mem_map.mpr ⟨l, hl, rfl⟩)
  have hBI : B ≤ d.M ⊓ c.L := base_le_intersection h
  have hle : modelImage hn e B ≤ modelImage hn e (d.M ⊓ c.L) :=
    map_mono (subgroupOf_mono _ hBI)
  have hproper : modelImage hn e (d.M ⊓ c.L) ≠ ⊤ := by
    intro ht
    have he : (d.M ⊓ c.L).subgroupOf c.L = ⊤ := by
      have hk : f.ker ≤ (d.M ⊓ c.L).subgroupOf c.L :=
        hker.trans (subgroupOf_mono _ hBI)
      have hh := comap_map_eq_self hk
      rw [show ((d.M ⊓ c.L).subgroupOf c.L).map f = ⊤ from ht, comap_top] at hh
      exact hh.symm
    apply c.outside
    intro l hl
    have hh : (⟨l, hl⟩ : c.L) ∈ (d.M ⊓ c.L).subgroupOf c.L := he ▸ mem_top _
    exact hh.1
  have himage : modelImage hn e (d.M ⊓ c.L) = modelImage hn e B := by
    rcases hle.eq_or_lt with he | hs
    · exact he.symm
    · exact (hproper (hmax.2 _ hs)).elim
  apply le_antisymm ?_ hBI
  intro l hl
  have hmem : (⟨l, hl.2⟩ : c.L) ∈ B.subgroupOf c.L := by
    rw [← comap_map_eq_self hker]
    change f ⟨l, hl.2⟩ ∈ modelImage hn e B
    rw [← himage]
    exact mem_map_of_mem f hl
  exact hmem

/-- A maximal plane image recovers its exact preimage under the supplied marking. -/
theorem planeParabolic_of_base_image [Finite G] (h : Earlier d c)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Projective 4)
    (W : Submodule (ZMod 2) (Space 4)) (hdim : Module.finrank (ZMod 2) W = 2)
    (hW : modelImage (by decide) e (d.Yplus ⊔ (d.S ⊓ c.L)) = BinaryLinear.parabolic W)
    (hmax : IsCoatom (BinaryLinear.parabolic W)) :
    Nonempty (PlaneParabolic d c.L e) := by
  have hj := intersection_join_of_coatom h (by decide) e (hW.symm ▸ hmax)
  refine ⟨⟨W, hdim, ?_⟩⟩
  rw [hj, ← hW]
  apply (comap_map_eq_self ?_).symm
  rw [linearAction_ker]
  intro l hl
  exact component_core_le_base h (mem_map.mpr ⟨l, hl, rfl⟩)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Preparation
