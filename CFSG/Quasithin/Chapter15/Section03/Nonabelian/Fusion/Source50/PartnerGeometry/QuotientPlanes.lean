module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.SelectedTransverse
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.ScalarInputs
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Displacement
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers.Geometry

/-!
# Complementary literal quotient planes

The two selected elementary partners have order 2^(s+3) and intersect in Z.
Their actual images in U/Z are disjoint subspaces of dimension s+2. Since
U/Z has dimension 2(s+2), they are complementary. These are the precise
subspaces used by the paired transvection coordinates in 15.3.56(5).
-/
@[expose] public noncomputable section
open Subgroup InvertedCubicTensor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open Recognition Recognition.LocalRestrictions
variable {G : Type*} [Group G] [Finite G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]

omit [Finite G] in
private theorem subspace_mk_mem (A : Subgroup G) (hZA : Z ≤ A) (u : closureU Z ZS) :
    Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) u) ∈
      vectorSubspace Z ZS A ↔ (u : G) ∈ A := by
  change u ∈ (vectorImage Z ZS A).comap (QuotientGroup.mk' _) ↔ _
  rw [vectorImage_preimage Z ZS A hZA]
  rfl

/-- The source rank is the dimension of the literal quotient image. -/
theorem quotient_plane_rank (A : Subgroup G) (n : ℕ)
    (hAU : A ≤ closureU Z ZS) (hZA : Z ≤ A) (hZcard : Nat.card Z=2)
    (hAcard : Nat.card A=2^(n+1)) :
    Module.finrank (ZMod 2) (vectorSubspace Z ZS A)=n := by
  have hc := ResidualOrbits.Normalizers.vectorImage_card_mul_center Z ZS A hAU hZA
  rw [hZcard,hAcard,pow_succ] at hc
  have hq : Nat.card (vectorImage Z ZS A)=2^n := Nat.eq_of_mul_eq_mul_right (by decide) hc
  have hd := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := vectorSubspace Z ZS A)
  rw [Nat.card_zmod,Source50.vectorSubspace_card,hq] at hd
  exact Nat.pow_right_injective (by decide : 1<2) hd.symm

omit [Finite G] in
/-- Intersection only in the denominator makes the actual image subspaces disjoint. -/
theorem quotient_planes_disjoint (A B : Subgroup G) (hZA : Z ≤ A) (hZB : Z ≤ B)
    (hcap : A ⊓ B ≤ Z) : Disjoint (vectorSubspace Z ZS A) (vectorSubspace Z ZS B) := by
  apply disjoint_iff.mpr
  apply le_antisymm ?_ bot_le
  intro w hw
  obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf (closureU Z ZS)) w.toMul
  have hwu : w = Additive.ofMul (QuotientGroup.mk' _ u) := congrArg Additive.ofMul hu.symm
  rw [hwu] at hw ⊢
  have hAu := (subspace_mk_mem Z ZS A hZA u).mp hw.1
  have hBu := (subspace_mk_mem Z ZS B hZB u).mp hw.2
  have hqu : QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) u = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (hcap ⟨hAu,hBu⟩)
  rw [hqu]
  exact Submodule.zero_mem _

/-- Exact ranks and dimension exhaust the original vector quotient. -/
theorem quotient_planes_complementary (A B : Subgroup G) (n : ℕ)
    (hAU : A ≤ closureU Z ZS) (hBU : B ≤ closureU Z ZS)
    (hZA : Z ≤ A) (hZB : Z ≤ B) (hZcard : Nat.card Z=2)
    (hAcard : Nat.card A=2^(n+1)) (hBcard : Nat.card B=2^(n+1))
    (hcap : A ⊓ B ≤ Z) (hdim : Module.finrank (ZMod 2) (Space Z ZS)=2*n) :
    IsCompl (vectorSubspace Z ZS A) (vectorSubspace Z ZS B) ∧
      Module.finrank (ZMod 2) (vectorSubspace Z ZS A)=n ∧
      Module.finrank (ZMod 2) (vectorSubspace Z ZS B)=n := by
  have ha := quotient_plane_rank Z ZS A n hAU hZA hZcard hAcard
  have hb := quotient_plane_rank Z ZS B n hBU hZB hZcard hBcard
  refine ⟨?_,ha,hb⟩
  apply (Submodule.isCompl_iff_disjoint _ _ ?_).mpr
    (quotient_planes_disjoint Z ZS A B hZA hZB hcap)
  rw [ha,hb,hdim]
  omega

open CFSG.Quasithin.ChapterG.Section02
open Setup OrthogonalPlusFour Chapter15Collapse
variable {Z ZS} {Zperp V Y T : Subgroup G} {g : G}

/-- The actual source56 pair, using the same canonical multiplicity and
its proved transverse intersection. -/
theorem selected_quotient_planes
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS) (hspan : localSpan Z Y=V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g) (hΩ : omegaCenter T=Z)
    [((OrthogonalPlusFour.S₂ (Chapter15.setup Z Zperp Y T) g).subgroupOf
      ((Chapter15.setup Z Zperp Y T).S g)).Normal]
    [IsElementaryAbelian 2 (OrthogonalPlusFour.Quotient (Chapter15.setup Z Zperp Y T) g)]
    (f : SourceModuleData d)
    (hsame : f.decomposition.leftMultiplicity=f.decomposition.rightMultiplicity)
    (y : (Chapter15.setup Z Zperp Y T).I g) (hy : (y : G) ∈ leftResidual d)
    (hy3 : orderOf y=3) (hyc : matrixSection d y=MatrixOrbit.leftCubic)
    (t : G) (ht : t ∈ T)
    (hcap : intersectionE Z ZS (y:G) ⊓ rightConjugate (intersectionE Z ZS (y:G)) t=Z) :
    IsCompl (vectorSubspace Z ZS (intersectionE Z ZS (y:G)))
      (vectorSubspace Z ZS (rightConjugate (intersectionE Z ZS (y:G)) t)) ∧
      Module.finrank (ZMod 2) (vectorSubspace Z ZS (intersectionE Z ZS (y:G)))=
        f.decomposition.leftMultiplicity+2 ∧
      Module.finrank (ZMod 2) (vectorSubspace Z ZS
        (rightConjugate (intersectionE Z ZS (y:G)) t))=f.decomposition.leftMultiplicity+2 := by
  have hEU : intersectionE Z ZS (y:G) ≤ closureU Z ZS := inf_le_left.trans inf_le_left
  have hu := Chapter15.closure_eq (Y := Y) (T := T) hZS hperp
  have hnorm : T ≤ normalizer (closureU Z ZS : Set G) := hu ▸
    ((normal_subgroupOf_iff_le_normalizer d.closure.normal.1).mp d.closure.normal.2)
  have hEtU : rightConjugate (intersectionE Z ZS (y:G)) t ≤ closureU Z ZS := by
    have hUt : rightConjugate (closureU Z ZS) t=closureU Z ZS :=
      mem_normalizer_iff_map_conj_eq.mp (hnorm (T.inv_mem ht))
    exact (map_mono hEU).trans_eq hUt
  have hZE : Z ≤ intersectionE Z ZS (y:G) := hcap.ge.trans inf_le_left
  have hZEt : Z ≤ rightConjugate (intersectionE Z ZS (y:G)) t := hcap.ge.trans inf_le_right
  have hcard := selected_intersectionE_card hZS hperp hspan d hΩ f hsame y hy hy3 hyc
  have hcardt : Nat.card (rightConjugate (intersectionE Z ZS (y:G)) t)=
      2^(f.decomposition.leftMultiplicity+3) :=
    (card_map_of_injective (MulAut.conj t⁻¹).injective).trans hcard
  exact quotient_planes_complementary Z ZS _ _ (f.decomposition.leftMultiplicity+2)
    hEU hEtU hZE hZEt d.point_card hcard hcardt hcap.le
    (literal_vector_dimension hZS hperp hspan d hΩ f hsame)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
