module
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Assembly
public import Theory.GroupTheory.PRegularLift
public import Theory.GroupTheory.PrimeOrderLift
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.MatrixRankOne

/-!
# Selecting the actual first residual factor and cubic partner

The ordered quotient in G.2.6 identifies the original Y-image with A₃×A₃.
The residual O²(Y∩N₁) therefore contains a preimage of the chosen left cubic.
The preimage lies outside its own two-core, as witnessed by that same matrix
image. No replacement residual or independent module coordinates are used.
Source: Aschbacher–Smith 15.3.54 and the opening of 15.3.56, pp.1146–1147.
-/

@[expose] public noncomputable section
open Subgroup InvertedCubicTensor
open ClassicalOrthogonal.FourPlusMatrix
open Representation.BinaryQuadraticPair
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Chapter15Collapse Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : CFSG.Quasithin.ChapterG.Section02.Setup G}
  {g : G} (d : Hypothesis D g)

def leftResidual : Subgroup G := oddFactor
  (moduleProjection d.quotientSymmetricEquiv) D.L ProductDecomposition.leftFactor

theorem leftResidual_le_L : leftResidual d ≤ D.L := by
  rintro x ⟨a, _, rfl⟩
  exact a.property.1

theorem leftResidual_le_I : leftResidual d ≤ D.I g :=
  (oddFactor_le _ _ _).trans (actorPreimage_le _ _)

theorem exists_left_cubic :
    ∃ y : D.I g, (y : G) ∈ leftResidual d ∧
      d.quotientMatrixEquiv (QuotientGroup.mk' (pCore 2 (D.I g)) y) = MatrixOrbit.leftCubic ∧
      (y : G) ∉ (leftResidual d).pCoreIn 2 := by
  let π := moduleProjection d.quotientSymmetricEquiv
  let a := pairPermEquiv MatrixOrbit.leftCubic
  have ha3 : a^3 = 1 := by
    change (pairPermEquiv MatrixOrbit.leftCubic)^3 = 1
    rw [← map_pow]
    have hc : MatrixOrbit.leftCubic^3 = 1 := by
      apply Prod.ext
      · exact MatrixOrbit.cubic_cube
      · simp [MatrixOrbit.leftCubic]
    rw [hc, map_one]
  have even_of_cube (x : Equiv.Perm (Fin 3)) (hx : x^3=1) :
      x ∈ alternatingGroup (Fin 3) := by
    change Equiv.Perm.sign x = 1
    have he := congrArg Equiv.Perm.sign hx
    rw [map_pow, map_one, Int.units_pow_eq_pow_mod_two] at he
    simpa using he
  have ha : a ∈ (D.L.subgroupOf (D.I g)).map π ⊓ ProductDecomposition.leftFactor := by
    constructor
    · rw [show (D.L.subgroupOf (D.I g)).map π =
        (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)) from
        d.quotientSymmetricEquiv_L_image]
      exact ⟨even_of_cube a.1 (congrArg Prod.fst ha3),
        even_of_cube a.2 (congrArg Prod.snd ha3)⟩
    · constructor
      · trivial
      · change (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three) 1 = 1
        exact map_one _
  have hm := mem_oddFactor_image_of_cube π D.L
    (d.I_eq_LU.symm ▸ le_sup_left) ProductDecomposition.leftFactor a ha ha3
  obtain ⟨y, hy, hey⟩ := hm
  have hyc : d.quotientMatrixEquiv (QuotientGroup.mk' (pCore 2 (D.I g)) y) =
      MatrixOrbit.leftCubic := by
    apply pairPermEquiv.injective
    exact hey
  refine ⟨y, hy, hyc, ?_⟩
  rintro ⟨b, hb, he⟩
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := leftResidual d)) ⟨b,hb⟩
  let f : leftResidual d →* PairSL (F := ZMod 2) :=
    (d.quotientMatrixEquiv.toMonoidHom.comp (QuotientGroup.mk' _)).comp
      (inclusion (leftResidual_le_I d))
  have hfb : f b = MatrixOrbit.leftCubic := by
    have hby : inclusion (leftResidual_le_I d) b = y := Subtype.ext he
    change d.quotientMatrixEquiv (QuotientGroup.mk' _ (inclusion (leftResidual_le_I d) b)) = _
    rw [hby]
    exact hyc
  have hn' : MatrixOrbit.leftCubic^(2^n) = 1 := by
    have hh := congrArg f (congrArg Subtype.val hn)
    change f (b^(2^n)) = f 1 at hh
    simpa only [map_pow, map_one, hfb] using hh
  have hc3 : MatrixOrbit.leftCubic^3 = 1 := by
    apply Prod.ext
    · exact MatrixOrbit.cubic_cube
    · simp [MatrixOrbit.leftCubic]
  have hc : orderOf MatrixOrbit.leftCubic = 3 :=
    orderOf_eq_prime hc3 (by decide +kernel : MatrixOrbit.leftCubic ≠ 1)
  have hd : 3 ∣ 2^n := hc ▸ orderOf_dvd_of_pow_eq_one hn'
  have hbad : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
  norm_num at hbad

/-- Choose the same marked cubic image with a genuine order-three preimage. -/
theorem exists_left_cubic_order_three :
    ∃ y : D.I g, (y : G) ∈ leftResidual d ∧
      d.quotientMatrixEquiv (QuotientGroup.mk' (pCore 2 (D.I g)) y) = MatrixOrbit.leftCubic ∧
      orderOf y = 3 ∧ (y : G) ∉ (leftResidual d).pCoreIn 2 := by
  obtain ⟨y, hy, hyc, _⟩ := exists_left_cubic d
  let f : leftResidual d →* PairSL (F := ZMod 2) :=
    (d.quotientMatrixEquiv.toMonoidHom.comp (QuotientGroup.mk' _)).comp
      (inclusion (leftResidual_le_I d))
  have hfy : f ⟨y,hy⟩ = MatrixOrbit.leftCubic := hyc
  have hk : f.ker = (pCore 2 (D.I g)).comap (inclusion (leftResidual_le_I d)) := by
    ext x
    change d.quotientMatrixEquiv (QuotientGroup.mk' _ (inclusion (leftResidual_le_I d) x)) = 1 ↔ _
    rw [d.quotientMatrixEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff _
  have hkp : IsPGroup 2 f.ker := by
    rw [hk]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hc : orderOf MatrixOrbit.leftCubic = 3 := by
    apply orderOf_eq_prime _ (by decide +kernel : MatrixOrbit.leftCubic ≠ 1)
    apply Prod.ext
    · exact MatrixOrbit.cubic_cube
    · simp [MatrixOrbit.leftCubic]
  let c : f.range := ⟨MatrixOrbit.leftCubic, ⟨⟨y,hy⟩, hfy⟩⟩
  obtain ⟨b, hodd, hb⟩ := f.rangeRestrict.exists_pRegular_lift f.rangeRestrict_surjective
    2 Nat.prime_two c (by rw [← f.range.orderOf_coe c, hc]; decide)
  have hbc : f b = MatrixOrbit.leftCubic := congrArg Subtype.val hb
  have hob : orderOf b = 3 := by
    rw [← f.orderOf_map_eq_of_coprime_of_isPGroup_ker hkp b
      (Nat.prime_two.coprime_iff_not_dvd.mpr hodd), hbc, hc]
  let bI := inclusion (leftResidual_le_I d) b
  refine ⟨bI, b.property, hbc, ?_, ?_⟩
  · exact (orderOf_injective (inclusion (leftResidual_le_I d))
      (inclusion_injective _) b).trans hob
  · rintro ⟨u, hu, he⟩
    have he' : u = b := Subtype.ext he
    subst u
    have hd : orderOf (⟨b,hu⟩ : pCore 2 (leftResidual d)) = 3 :=
      ((pCore 2 (leftResidual d)).orderOf_coe ⟨b,hu⟩).symm.trans hob
    have hp := pCore_isPGroup.orderOf_coprime
      (by decide : Nat.Coprime 2 3) (⟨b,hu⟩ : pCore 2 (leftResidual d))
    rw [hd] at hp
    norm_num at hp

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
