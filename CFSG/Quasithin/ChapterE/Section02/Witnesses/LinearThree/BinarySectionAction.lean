module

public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearThree.BinarySectionSource
public import Theory.Representation.BinaryConjugationSection.Descent
public import Theory.Representation.BinaryConjugationSection.FullMovement
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.SpecificGroups.PSL3Two.InvolutionConjugacy
-- The placement API names core(M); the source quotient names minimalParabolicCore.
-- This internal proof uses their defining equality without exposing the core body.
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The actual component action on the binary E.2.17 section

The original elementary subgroup maps into the normal linear-three component
by source long-root placement. The maximal core centralizes the literal
section, so conjugation descends to H/J. Its component restriction is fully
moved: the source residual moves the whole section and is contained in the
normal component because the quotient is a two-group. The order-eight seed
and its order-two central kernel give the precise rank-two bound.

Source: Aschbacher–Smith, E.2.17, printed pp.229–230.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterE.Witnesses.LinearThree
variable {H : Type*} [Group H] [Finite H]

theorem source_binary_image_le_component
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 2)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal) :
    V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)) ≤
      K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)) := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let A := V.map q
  let C := K.map q
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map q
  have hi := Structure.source_normal_simple_image T hP hs K hK hgen
  let : C.Normal := hi.2.2.1
  let : IsSimpleGroup C := hi.1
  have hmin : ChapterB.IsMinimalParabolicOver S ⊤ :=
    (Structure.source_star_minimal_core_free T hP).1
  have hcore : (ChapterB.minimalParabolicMax S hmin).normalCore = ⊥ := by
    convert (Structure.source_star_minimal_core_free T hP).2 using 1
    rfl
  have hAS : A ≤ (S : Subgroup (H ⧸ J)) := map_mono hVT
  have hSA : (S : Subgroup (H ⧸ J)) ≤ normalizer (A : Set (H ⧸ J)) :=
    (map_mono ((normal_subgroupOf_iff_le_normalizer hVT).mp hvn)).trans (le_normalizer_map q)
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by simpa only [Nat.card_eq_fintype_card, pow_one] using hcard)
  obtain ⟨g, _, _, hplace⟩ := Structure.LinearThree.exists_longRoot_placement
    F (n := 1) (by decide) (by simpa using hcard) C e S hi.2.2.2 hmin hcore A hAS hSA
  intro x hx
  obtain ⟨a, _, rfl⟩ := hplace hx
  exact ((e.trans (MulAut.conj g)).symm a).property

omit [Finite H] in
theorem binary_model_equiv (hm : ClassicalGroup.IsPSL H 3 2) :
    Nonempty (H ≃* Matrix.PSL3Two.SL) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
  exact ⟨(e.trans (Atlas.fieldEquivPSL 3 eF)).trans Matrix.PSL3Two.equiv.symm⟩

omit [Finite H] in
theorem source_binary_section_action
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (L Z : Subgroup H) [L.Normal] [Z.Normal] (hZL : Z ≤ L)
    [IsElementaryAbelian 2 (L ⧸ Z.subgroupOf L)]
    (hLJ : ⁅L, ChapterB.minimalParabolicCore T hP⁆ ≤ Z)
    (hfull : ⁅L, pResidual 2 H⁆ = L) :
    let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)
    ∃ (σ : Representation (ZMod 2) (H ⧸ ChapterB.minimalParabolicCore T hP)
        (Additive (L ⧸ Z.subgroupOf L)))
      (c : BinaryConjugationSection ⊤ L Z (σ.comp (q.comp (⊤ : Subgroup H).subtype))),
      (∀ l : L, (c.coordinates l).toAdd =
        Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf L) l)) ∧
      subspaceCommutator (σ.comp (K.map q).subtype) ⊤ ⊤ = ⊤ := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let π := q.comp (⊤ : Subgroup H).subtype
  have hπ : Function.Surjective π := by
    intro x
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective J x
    exact ⟨⟨a, trivial⟩, ha⟩
  obtain ⟨σ, c, hc⟩ := BinaryConjugationSection.exists_descended_actor
    ⊤ L Z le_top hZL le_normalizer_of_normal le_normalizer_of_normal π hπ (by
      intro a ha l hl
      have haJ : (a : H) ∈ J := (QuotientGroup.eq_one_iff (a : H)).mp ha
      rw [commutator_comm] at hLJ
      exact hLJ (commutator_mem_commutator haJ hl))
  refine ⟨σ, c, hc, ?_⟩
  have hm := c.subspaceCommutator_eq_top_of_movement (pResidual 2 H) le_top (by
    rw [commutator_comm, hfull, sup_eq_left.mpr hZL])
  rw [subspaceCommutator_comp_map] at hm
  have he : ((pResidual 2 H).subgroupOf ⊤).map π = (pResidual 2 H).map q := by
    rw [show π = q.comp (⊤ : Subgroup H).subtype from rfl, ← map_map,
      map_subgroupOf_eq_of_le le_top]
  rw [he] at hm
  have hRK : pResidual 2 H ≤ K := sInf_le
    ⟨inferInstance, isPGroup_quotient_of_sup_eq_top K (T : Subgroup H) T.isPGroup' hgen⟩
  rw [subspaceCommutator_comp_map, ← MonoidHom.range_eq_map, range_subtype]
  apply top_unique
  apply hm.ge.trans
  apply Submodule.span_mono
  rintro v ⟨a, ha, w, hw, hv⟩
  exact ⟨a, map_mono hRK ha, w, hw, hv⟩

theorem section_seed_finrank
    {A L Z B : Subgroup H} {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {ρ : Representation (ZMod 2) A M} (c : BinaryConjugationSection A L Z ρ)
    (hBL : B ≤ L) (hZB : Z ≤ B) (hB : Nat.card B = 8) (hZ : Nat.card Z = 2) :
    Module.finrank (ZMod 2) (c.imageSpace B) = 2 := by
  apply c.imageSpace_finrank_of_index B hBL 2
  have hh := (Z.subgroupOf B).card_mul_index
  have hc : Nat.card (Z.subgroupOf B) = Nat.card Z :=
    Nat.card_congr (subgroupOfEquivOfLe hZB).toEquiv
  rw [hc, hZ, hB] at hh
  change 2 * Z.relIndex B = 8 at hh
  norm_num
  omega

end CFSG.Quasithin.ChapterE.Witnesses.LinearThree
