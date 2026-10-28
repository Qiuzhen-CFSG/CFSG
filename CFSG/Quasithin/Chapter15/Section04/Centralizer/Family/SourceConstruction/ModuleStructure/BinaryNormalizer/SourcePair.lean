module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure.BinaryNormalizer.IntrinsicFactors
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.Basic

/-!
# Intrinsic quotient factors and actual residual lifts for 15.4.12

The faithful action of image M Y on W=[V,Y] agrees with conjugation by each
element of Y. Relative normality then forces compatibility with conjugation
by every element of M. The intrinsic pair theorem constructs the two cubic
quotient factors and proves M permutes them. Irreducibility of T supplies a
swapping element, which the existing Permutation APIs lift to the actual
two-residuals of the preimages under quotientMap M.

No factor permutation, swapping witness, or individual T-invariance is an
input. The faithful quotient action is an explicit premise for the parent
ModuleStructure assembly to construct.

Source: Aschbacher--Smith, 15.4.12(6), pp.1160--1161, and the factor interchange
used at the start of 15.4.18, p.1162, combined manuscript (1 March 2004).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure.BinaryNormalizer
open LocalSetup.TwoFactors.SourceFactors.Permutation
variable {G : Type*} [Group G]

/-- Projection of Y into its literal image in M/O₂(M). -/
def memberProjection (M Y : Subgroup G) (hYM : Y ≤ M) : Y →* image M Y :=
  ((quotientMap M).subgroupMap (Y.subgroupOf M)).comp
    (subgroupOfEquivOfLe hYM).symm.toMonoidHom

theorem memberProjection_val (M Y : Subgroup G) (hYM : Y ≤ M) (y : Y) :
    (memberProjection M Y hYM y : CoreQuotient M) = quotientMap M (inclusion hYM y) := rfl

theorem memberProjection_surjective (M Y : Subgroup G) (hYM : Y ≤ M) :
    Function.Surjective (memberProjection M Y hYM) :=
  ((quotientMap M).subgroupMap_surjective _).comp (subgroupOfEquivOfLe hYM).symm.surjective

/-- Conjugation by M on the actual quotient image. -/
def imageConjugation (M Y : Subgroup G) (hnY : M ≤ normalizer (Y : Set G)) :
    M →* MulAut (image M Y) := by
  let : (Y.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hnY
  let : (image M Y).Normal :=
    (inferInstance : (Y.subgroupOf M).Normal).map (quotientMap M) (QuotientGroup.mk'_surjective _)
  exact (MulAut.conjNormal : CoreQuotient M →* MulAut (image M Y)).comp (quotientMap M)

theorem imageConjugation_val (M Y : Subgroup G) (hnY : M ≤ normalizer (Y : Set G))
    (g : M) (a : image M Y) :
    (imageConjugation M Y hnY g a : CoreQuotient M) =
      quotientMap M g * (a : CoreQuotient M) * (quotientMap M g)⁻¹ := rfl

/-- Conjugation by M on an invariant subgroup, with its ambient embedding retained. -/
def moduleConjugation (M W : Subgroup G) (hnW : M ≤ normalizer (W : Set G)) : M →* MulAut W :=
  letI := conjMulDistribMulActionOfLeNormalizer M W hnW
  MulDistribMulAction.toMulAut M W

theorem moduleConjugation_val (M W : Subgroup G) (hnW : M ≤ normalizer (W : Set G))
    (g : M) (w : W) : (moduleConjugation M W hnW g w : G) =
      (g : G) * (w : G) * (g : G)⁻¹ := rfl

/-- Agreement on every original element of Y forces full M-equivariance;
no quotient-factor permutation is a premise. -/
theorem source_intertwining (M Y W : Subgroup G) (hYM : Y ≤ M)
    (hnY : M ≤ normalizer (Y : Set G)) (hnW : M ≤ normalizer (W : Set G))
    (ρ : image M Y →* MulAut W)
    (hρ : ∀ (y : Y) (w : W), (ρ (memberProjection M Y hYM y) w : G) =
      (y : G) * (w : G) * (y : G)⁻¹)
    (g : M) (a : image M Y) (w : W) :
    moduleConjugation M W hnW g (ρ a w) =
      ρ (imageConjugation M Y hnY g a) (moduleConjugation M W hnW g w) := by
  obtain ⟨y,rfl⟩ := memberProjection_surjective M Y hYM a
  let y' : Y := ⟨(g : G) * (y : G) * (g : G)⁻¹,
    (mem_normalizer_iff.mp (hnY g.property) y).mp y.property⟩
  have he : imageConjugation M Y hnY g (memberProjection M Y hYM y) =
      memberProjection M Y hYM y' := by
    apply Subtype.ext
    rw [imageConjugation_val,memberProjection_val,memberProjection_val,←map_inv,←map_mul,←map_mul]
    rfl
  rw [he]
  apply Subtype.ext
  rw [moduleConjugation_val,hρ,hρ,moduleConjugation_val]
  change (g : G) * ((y : G) * (w : G) * (y : G)⁻¹) * (g : G)⁻¹ =
    ((g : G) * (y : G) * (g : G)⁻¹) * ((g : G) * (w : G) * (g : G)⁻¹) *
      ((g : G) * (y : G) * (g : G)⁻¹)⁻¹
  group

/-- The pair transported into the fixed quotient, rather than an isomorphic copy. -/
def quotientFactors (M Y W : Subgroup G) [MulDistribMulAction (image M Y) W]
    (P : FactorPair (A := image M Y) (W := W)) : Bool → Subgroup (CoreQuotient M) :=
  fun i => (P.line i).map (image M Y).subtype

private theorem quotientFactors_conj (M Y W : Subgroup G) [MulDistribMulAction (image M Y) W]
    (P : FactorPair (A := image M Y) (W := W))
    (hnY : M ≤ normalizer (Y : Set G)) (g : M) (i j : Bool)
    (he : (P.line i).map (imageConjugation M Y hnY g).toMonoidHom = P.line j) :
    (quotientFactors M Y W P i).map (MulAut.conj (quotientMap M g)).toMonoidHom =
      quotientFactors M Y W P j := by
  have hh := congrArg (Subgroup.map (image M Y).subtype) he
  rw [map_map] at hh
  have hc : (image M Y).subtype.comp (imageConjugation M Y hnY g).toMonoidHom =
      (MulAut.conj (quotientMap M g)).toMonoidHom.comp (image M Y).subtype := by
    ext a
    rfl
  rw [hc] at hh
  simpa only [quotientFactors,map_map] using hh

/-- The quotient factors generate the literal image and are distinct of order three. -/
theorem quotientFactors_structure (M Y W : Subgroup G) [MulDistribMulAction (image M Y) W]
    (P : FactorPair (A := image M Y) (W := W)) :
    (∀ i, Nat.card (quotientFactors M Y W P i) = 3) ∧
      Function.Injective (quotientFactors M Y W P) ∧
      quotientFactors M Y W P false ⊔ quotientFactors M Y W P true = image M Y := by
  refine ⟨fun i => (card_map_of_injective (image M Y).subtype_injective).trans (P.card i), ?_, ?_⟩
  · intro i j he
    exact P.distinct (map_injective (image M Y).subtype_injective he)
  · change (P.line false).map _ ⊔ (P.line true).map _ = _
    rw [←Subgroup.map_sup,P.complement.sup_eq_top,←MonoidHom.range_eq_map,range_subtype]

variable [Finite G]

theorem source_pair_permuted (M Y W : Subgroup G) (hYM : Y ≤ M)
    (hnY : M ≤ normalizer (Y : Set G)) (hnW : M ≤ normalizer (W : Set G))
    [IsElementaryAbelian 3 (image M Y)] [IsElementaryAbelian 2 W]
    (hA : Nat.card (image M Y) = 9) (hW : Nat.card W = 16)
    (ρ : image M Y →* MulAut W) (hfaith : Function.Injective ρ)
    (hρ : ∀ (y : Y) (w : W), (ρ (memberProjection M Y hYM y) w : G) =
      (y : G) * (w : G) * (y : G)⁻¹) :
    letI := MulDistribMulAction.compHom W ρ
    ∀ (P : FactorPair (A := image M Y) (W := W)) (g : M) i,
      ∃ j, (quotientFactors M Y W P i).map (MulAut.conj (quotientMap M g)).toMonoidHom =
        quotientFactors M Y W P j := by
  let _ := MulDistribMulAction.compHom W ρ
  let _ : FaithfulSMul (image M Y) W := ⟨fun {a b} h => hfaith (MulEquiv.ext h)⟩
  intro P g i
  obtain ⟨j,hj⟩ := P.permuted hA hW (imageConjugation M Y hnY g)
    (moduleConjugation M W hnW g) (source_intertwining M Y W hYM hnY hnW ρ hρ g) i
  exact ⟨j,quotientFactors_conj M Y W P hnY g i j hj⟩

/-- Irreducibility produces a T-element interchanging the actual residual lifts. -/
theorem source_pair_swap (M Y W T : Subgroup G) (hYM : Y ≤ M) (hTM : T ≤ M)
    (hnY : M ≤ normalizer (Y : Set G)) (hnW : M ≤ normalizer (W : Set G))
    [IsElementaryAbelian 3 (image M Y)] [IsElementaryAbelian 2 W]
    (hA : Nat.card (image M Y) = 9) (hW : Nat.card W = 16)
    (ρ : image M Y →* MulAut W) (hfaith : Function.Injective ρ)
    (hρ : ∀ (y : Y) (w : W), (ρ (memberProjection M Y hYM y) w : G) =
      (y : G) * (w : G) * (y : G)⁻¹)
    (hirr : ∀ D : Subgroup (image M Y),
      (∀ t : T, D.map (imageConjugation M Y hnY (inclusion hTM t)).toMonoidHom = D) →
      D = ⊥ ∨ D = ⊤) :
    letI := MulDistribMulAction.compHom W ρ
    ∀ P : FactorPair (A := image M Y) (W := W),
      ∃ t ∈ T,
        (liftedFactors M (quotientMap M) (quotientFactors M Y W P) false).map
          (MulAut.conj t).toMonoidHom =
          liftedFactors M (quotientMap M) (quotientFactors M Y W P) true ∧
        (liftedFactors M (quotientMap M) (quotientFactors M Y W P) true).map
          (MulAut.conj t).toMonoidHom =
          liftedFactors M (quotientMap M) (quotientFactors M Y W P) false ∧
        t ∉ normalizer (liftedFactors M (quotientMap M) (quotientFactors M Y W P) false : Set G) := by
  let _ := MulDistribMulAction.compHom W ρ
  let _ : FaithfulSMul (image M Y) W := ⟨fun {a b} h => hfaith (MulEquiv.ext h)⟩
  intro P
  obtain ⟨t,ht,_⟩ := P.exists_swap hA hW ((imageConjugation M Y hnY).comp (inclusion hTM))
    (fun t => ⟨moduleConjugation M W hnW (inclusion hTM t),
      source_intertwining M Y W hYM hnY hnW ρ hρ (inclusion hTM t)⟩) hirr
  obtain ⟨hc,hi,_⟩ := quotientFactors_structure M Y W P
  apply liftedFactors_swap M T hTM (quotientMap M) (QuotientGroup.mk'_surjective _) _ hc hi
    (source_pair_permuted M Y W hYM hnY hnW hA hW ρ hfaith hρ P)
  exact ⟨t,quotientFactors_conj M Y W P hnY (inclusion hTM t) false true ht⟩

/-- The Chapter 15 consumer: construct the quotient pair and its actual residual
lifts from the faithful action on W=[V,Y]. Relative normality, original quotient
coordinates and original conjugation are retained throughout. -/
theorem source_residual_pair (M Y V T : Subgroup G) (hYM : Y ≤ M) (hVM : V ≤ M)
    (hTM : T ≤ M) (hnY : (Y.subgroupOf M).Normal) (hnV : (V.subgroupOf M).Normal)
    [IsElementaryAbelian 3 (image M Y)] [IsElementaryAbelian 2 (⁅V,Y⁆ : Subgroup G)]
    (hA : Nat.card (image M Y) = 9) (hW : Nat.card (⁅V,Y⁆ : Subgroup G) = 16)
    (ρ : image M Y →* MulAut (⁅V,Y⁆ : Subgroup G)) (hfaith : Function.Injective ρ)
    (hρ : ∀ (y : Y) (w : (⁅V,Y⁆ : Subgroup G)),
      (ρ (memberProjection M Y hYM y) w : G) = (y : G) * (w : G) * (y : G)⁻¹)
    (hirr : ∀ D : Subgroup (image M Y),
      (∀ t : T, D.map (imageConjugation M Y
        ((normal_subgroupOf_iff_le_normalizer hYM).mp hnY) (inclusion hTM t)).toMonoidHom = D) →
      D = ⊥ ∨ D = ⊤) :
    letI := MulDistribMulAction.compHom (⁅V,Y⁆ : Subgroup G) ρ
    ∃ P : FactorPair (A := image M Y) (W := (⁅V,Y⁆ : Subgroup G)),
      (∀ i, Nat.card (commutatorAction (P.line i) (⁅V,Y⁆ : Subgroup G)) = 4) ∧
      IsCompl (commutatorAction (P.line false) (⁅V,Y⁆ : Subgroup G))
        (commutatorAction (P.line true) (⁅V,Y⁆ : Subgroup G)) ∧
      (∀ (g : M) i, ∃ j,
        (quotientFactors M Y ⁅V,Y⁆ P i).map (MulAut.conj (quotientMap M g)).toMonoidHom =
          quotientFactors M Y ⁅V,Y⁆ P j) ∧
      ∃ t ∈ T,
        (liftedFactors M (quotientMap M) (quotientFactors M Y ⁅V,Y⁆ P) false).map
          (MulAut.conj t).toMonoidHom =
          liftedFactors M (quotientMap M) (quotientFactors M Y ⁅V,Y⁆ P) true ∧
        (liftedFactors M (quotientMap M) (quotientFactors M Y ⁅V,Y⁆ P) true).map
          (MulAut.conj t).toMonoidHom =
          liftedFactors M (quotientMap M) (quotientFactors M Y ⁅V,Y⁆ P) false ∧
        t ∉ normalizer (liftedFactors M (quotientMap M)
          (quotientFactors M Y ⁅V,Y⁆ P) false : Set G) := by
  let _ := MulDistribMulAction.compHom (⁅V,Y⁆ : Subgroup G) ρ
  let _ : FaithfulSMul (image M Y) (⁅V,Y⁆ : Subgroup G) :=
    ⟨fun {a b} h => hfaith (MulEquiv.ext h)⟩
  have hNY := (normal_subgroupOf_iff_le_normalizer hYM).mp hnY
  have hNV := (normal_subgroupOf_iff_le_normalizer hVM).mp hnV
  have hNW : M ≤ normalizer ((⁅V,Y⁆ : Subgroup G) : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hNV hg),
      mem_normalizer_iff_map_conj_eq.mp (hNY hg)]
  obtain ⟨P⟩ := exists_factorPair (W := (⁅V,Y⁆ : Subgroup G)) hA hW
  obtain ⟨hc,hd⟩ := P.moved_decomposition hW
  exact ⟨P,hc,hd,source_pair_permuted M Y ⁅V,Y⁆ hYM hNY hNW hA hW ρ hfaith hρ P,
    source_pair_swap M Y ⁅V,Y⁆ T hYM hTM hNY hNW hA hW ρ hfaith hρ hirr P⟩

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure.BinaryNormalizer
