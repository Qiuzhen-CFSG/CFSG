module
public import Theory.SpecificGroups.PSL2.SixteenCubicWreath
public import Theory.GroupTheory.PResidual.CubicCoreQuotient
public import Theory.GroupTheory.PResidual.PrimeToPerfect
public import Theory.GroupTheory.PCoreProduct
public import Theory.ElementaryAbelian.Basic

/-!
# The cubic residual of a PSL₂(16) Borel square

The literal upper triangular Borel square has torus quotient GF(16)ˣ².
Its prime-to-three residual therefore has two-core quotient equal to the
actual pair of cubic roots of unity. It is two-perfect and is preserved by
all automorphisms preserving the Borel, including factor exchanges.
Sylow conjugacy in each factor identifies the Borel at any specified Sylow.

These constructions supply the auxiliary cubic subgroup in the last paragraph
of Aschbacher--Smith 14.6.14, printed p.1033. Ambient outside placement and
primitive selection belong to the Chapter14 consumer. In particular, the
order-nine quotient alone does not assert irreducibility of its Sylow action.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear
open Matrix.ProjectiveSpecialLinearGroup.OddBorel
namespace Theory.PSL2.SixteenCubicBorel
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
local notation "L" => Theory.PSL2.Group F

@[expose] def pairBorel : Subgroup (L × L) := (borel F).prod (borel F)
@[expose] def pairCubic : Subgroup (L × L) :=
  (primeToResidual 3 (pairBorel F)).map (pairBorel F).subtype

omit [CharP F 2] in
private theorem residual_units_pair (hF : Nat.card F = 16) :
    primeToResidual 3 (Fˣ × Fˣ) = (rootsOfUnity 3 F).prod (rootsOfUnity 3 F) := by
  let R := (rootsOfUnity 3 F).prod (rootsOfUnity 3 F)
  have hc : Nat.card R = 9 := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
      FiniteField.CubicSixteen.roots_card F hF]
  have hi : R.index = 25 := by
    have hh := R.card_mul_index
    rw [hc,Nat.card_prod,Nat.card_units,hF] at hh
    omega
  exact le_antisymm (primeToResidual_le R (by rw [hi]; decide))
    (le_primeToResidual_of_isPGroup (IsPGroup.of_card (n := 2) hc))

/-- Transport the cubic residual through an actual torus-pair quotient. -/
def cubicResidualQuotientEquiv {A : Type*} [_root_.Group A] [Finite A]
    (hF : Nat.card F = 16) (q : (A ⧸ pCore 2 A) ≃* Fˣ × Fˣ) :
    (primeToResidual 3 A ⧸ pCore 2 (primeToResidual 3 A)) ≃*
      (rootsOfUnity 3 F × rootsOfUnity 3 F) :=
  (primeToResidualCoreQuotientImage (A := A) 3 2).trans
    ((q.subgroupMap (primeToResidual 3 _)).trans
      ((MulEquiv.subgroupCongr ((map_primeToResidual q).trans
        (residual_units_pair F hF))).trans (Subgroup.prodEquiv _ _)))

def pairQuotientTorusEquiv (hF : Nat.card F = 16) :
    (pairBorel F ⧸ pCore 2 (pairBorel F)) ≃* Fˣ × Fˣ := by
  let e := Subgroup.prodEquiv (borel F) (borel F)
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    ((QuotientGroup.quotientMulEquivOfEq (pCore_prod 2)).trans
      ((QuotientGroup.prodMulEquiv _ _).trans
        (MulEquiv.prodCongr (quotientTorusEquiv F (n := 4) hF)
          (quotientTorusEquiv F (n := 4) hF))))

/-- The actual cubic residual of the Borel square has the cubic torus pair
as its intrinsic two-core quotient. -/
def pairCubicQuotientEquiv (hF : Nat.card F = 16) :
    (pairCubic F ⧸ pCore 2 (pairCubic F)) ≃*
      (rootsOfUnity 3 F × rootsOfUnity 3 F) := by
  let e := equivMapOfInjective (primeToResidual 3 (pairBorel F))
    (pairBorel F).subtype (pairBorel F).subtype_injective
  let q := pairQuotientTorusEquiv F hF
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans
    ((primeToResidualCoreQuotientImage (A := pairBorel F) 3 2).trans
      ((q.subgroupMap (primeToResidual 3 _)).trans
        ((MulEquiv.subgroupCongr ((map_primeToResidual q).trans
          (residual_units_pair F hF))).trans (Subgroup.prodEquiv _ _))))

theorem pairCubic_quotient_card (hF : Nat.card F = 16) :
    Nat.card (pairCubic F ⧸ pCore 2 (pairCubic F)) = 9 := by
  rw [Nat.card_congr (pairCubicQuotientEquiv F hF).toEquiv,Nat.card_prod,
    FiniteField.CubicSixteen.roots_card F hF]

theorem pairCubic_quotient_elementary (hF : Nat.card F = 16) :
    IsElementaryAbelian 3 (pairCubic F ⧸ pCore 2 (pairCubic F)) := by
  let e := pairCubicQuotientEquiv F hF
  let : IsElementaryAbelian 3 (rootsOfUnity 3 F × rootsOfUnity 3 F) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Prod.ext (Subtype.ext x.1.property) (Subtype.ext x.2.property)) }
  exact IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective

omit [CharP F 2] in
theorem pairCubic_twoPerfect : IsPPerfect 2 (pairCubic F) :=
  (isPPerfect_primeToResidual 3 2 (by decide)).of_surjective
    ((pairBorel F).subtype.subgroupMap _) ((pairBorel F).subtype.subgroupMap_surjective _)

omit [Finite F] [CharP F 2] in
theorem pairCubic_le : pairCubic F ≤ pairBorel F := map_subtype_le _

omit [Finite F] [CharP F 2] in
/-- Every automorphism preserving the actual Borel square preserves its
cubic residual, including actors that exchange the two components. -/
theorem map_pairCubic (a : MulAut (L × L))
    (ha : (pairBorel F).map a.toMonoidHom = pairBorel F) :
    (pairCubic F).map a.toMonoidHom = pairCubic F := by
  rw [pairCubic,map_embedded_primeToResidual,ha]

/-- The Borel at an arbitrary supplied Sylow of the square has genuine
coordinates in the product of the two upper triangular Borels. -/
def sylowBorelEquiv (S : Sylow 2 (L × L)) :
    normalizer (S : Set (L × L)) ≃* pairBorel F := by
  let f := MonoidHom.fst L L
  let g := MonoidHom.snd L L
  let S1 := S.mapSurjective (f := f) (fun x => ⟨(x,1),rfl⟩)
  let S2 := S.mapSurjective (f := g) (fun x => ⟨(1,x),rfl⟩)
  have hp : IsPGroup 2 ((S1 : Subgroup L).prod (S2 : Subgroup L)) := by
    obtain ⟨m,hm⟩ := S1.isPGroup'.exists_card_eq
    obtain ⟨n,hn⟩ := S2.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := m+n) (by
      rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,hm,hn,pow_add])
  have hS : (S1 : Subgroup L).prod (S2 : Subgroup L) = (S : Subgroup (L × L)) :=
    S.is_maximal' hp (fun x hx => ⟨mem_map_of_mem f hx,mem_map_of_mem g hx⟩)
  have hN : normalizer (S : Set (L × L)) =
      (normalizer (S1 : Set L)).prod (normalizer (S2 : Set L)) := by
    apply le_antisymm
    · exact le_prod_iff.mpr ⟨le_normalizer_map f,le_normalizer_map g⟩
    · apply le_normalizer_iff.mpr
      intro x hx y hy
      rw [← hS] at hy ⊢
      exact ⟨le_normalizer_iff.mp le_rfl x.1 hx.1 y.1 hy.1,
        le_normalizer_iff.mp le_rfl x.2 hx.2 y.2 hy.2⟩
  exact (MulEquiv.subgroupCongr hN).trans
    ((Subgroup.prodEquiv _ _).trans
      ((MulEquiv.prodCongr (sylowNormalizerEquiv F S1) (sylowNormalizerEquiv F S2)).trans
        (Subgroup.prodEquiv _ _).symm))

/-- The quotient of the literal Sylow normalizer is the torus pair. -/
def sylowBorelQuotientEquiv (hF : Nat.card F = 16) (S : Sylow 2 (L × L)) :
    (normalizer (S : Set (L × L)) ⧸ pCore 2 (normalizer (S : Set (L × L)))) ≃*
      Fˣ × Fˣ :=
  (QuotientGroup.congr _ _ (sylowBorelEquiv F S)
    (pCore_map_iso 2 (sylowBorelEquiv F S))).trans (pairQuotientTorusEquiv F hF)

end Theory.PSL2.SixteenCubicBorel
