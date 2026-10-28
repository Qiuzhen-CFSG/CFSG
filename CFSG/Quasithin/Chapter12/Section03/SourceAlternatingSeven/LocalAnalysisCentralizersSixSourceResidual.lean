module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersSixSourceRecognition
public import Theory.GroupTheory.PerfectCentralCoverPerfectPreimage
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.SolvableResidual.TwoKernel

/-!
# The original two-residual at a weight-six point

The preimage of the A₆ point stabilizer in L/O₂(L) is perfect: its index
is seven and the central kernel has order one or three, so transfer
applies. The actual point centralizer maps onto this perfect preimage
with two-group kernel. Its solvable residual is therefore its two-residual.
The final equality retains the original embedding into G.

This supplies the bridge from the source O²(C_L(e)) to `pointResidual`
used by the weight-six component and Frattini arguments. Source:
Aschbacher--Smith 12.3.6, printed p.809; I.1.2, printed p.407.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode Theory.GroupTheory PerfectCentralCovering
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
namespace Setup.NaturalCoordinates
variable (E : S.NaturalCoordinates)

/-- The two intrinsic residuals of the actual weight-six point centralizer agree. -/
theorem six_point_pResidual_eq_solvableResidual (v : V)
    (hv : weight (E.coordinates v).toAdd.val = 6) :
    pResidual 2 (L ⊓ centralizer ({(v : G)} : Set G) : Subgroup G) =
      solvableResidual (L ⊓ centralizer ({(v : G)} : Set G) : Subgroup G) := by
  let Q := L ⧸ pCore 2 L
  let π : L →* Q := QuotientGroup.mk' (pCore 2 L)
  let : IsQuasisimple Q := S.hypothesis.quasisimple
  let eQ : (Q ⧸ center Q) ≃* alternatingGroup (Fin 7) :=
    (centralPreimageQuotientEquiv (pCore 2 L)).symm.trans S.quotient
  have hpπ : pCore 2 L ≤ S.projection.ker := by
    intro l hl
    change S.quotient (QuotientGroup.mk' _ l) = 1
    apply S.quotient.map_eq_one_iff.mpr
    exact (QuotientGroup.eq_one_iff l).mpr (le_centralPreimage _ hl)
  let q : Q →* alternatingGroup (Fin 7) := QuotientGroup.lift _ S.projection hpπ
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨l,rfl⟩ := S.projection_surjective a
    exact ⟨π l,rfl⟩
  have hcentral : q.ker ≤ center Q := by
    intro x hx
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
    have he : S.projection l = 1 := hx
    have hl : l ∈ centralPreimage (pCore 2 L) :=
      (QuotientGroup.eq_one_iff l).mp (S.quotient.map_eq_one_iff.mp he)
    exact hl
  let c : Cover Q (alternatingGroup (Fin 7)) := ⟨q,hq,inferInstance,hcentral⟩
  have hcπ : c.toMonoidHom.comp π = S.projection := by
    exact rfl
  have hodd : Odd (Nat.card (center Q)) := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    exact not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot (G := L) 2) _ le_rfl
  have hk : IsPGroup 3 c.toMonoidHom.ker := by
    have hker : c.toMonoidHom.ker = center Q := by
      have h := c.comap_center
      rw [alternatingGroup.center_eq_bot (by simp)] at h
      exact h
    rw [hker]
    rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 7 (by decide) eQ hodd with h | ⟨_,h⟩
    · exact IsPGroup.of_card (n := 0) (by simpa using h)
    · exact IsPGroup.of_card (n := 1) (by simpa using h)
  let P := WeightTwoGeometry.stabilizer (E.coordinates v).toAdd
  let : Group.IsPerfect P := WeightSixGeometry.stabilizer_perfect _ hv
  have hi : P.index = 7 := by
    have h := P.card_mul_index
    have hP : Nat.card P = 360 := by
      rw [Nat.card_congr (WeightSixGeometry.sixEquiv _ hv).toEquiv,
        nat_card_alternatingGroup, Nat.card_fin]
      decide
    have hA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup,Nat.card_fin]
      decide
    rw [hP,hA] at h
    omega
  let R := P.comap c.toMonoidHom
  let : Group.IsPerfect R := c.perfect_preimage_of_primeToIndex hk P (by rw [hi]; decide)
  let f := π.subgroupComap R
  have hf := π.subgroupComap_surjective_of_surjective R (QuotientGroup.mk'_surjective _)
  have hfker : IsPGroup 2 f.ker := by
    have he : f.ker = (pCore 2 L).comap (R.comap π).subtype := by
      ext x
      change (⟨π x, x.property⟩ : R) = 1 ↔ _
      rw [Subtype.ext_iff]
      exact QuotientGroup.eq_one_iff x.val
    rw [he]
    exact pCore_isPGroup.comap_of_injective _ (R.comap π).subtype_injective
  have hres := pResidual_eq_solvableResidual_of_perfect_image f hf hfker
  let C := L ⊓ centralizer ({(v : G)} : Set G)
  have hC : C.subgroupOf L = R.comap π := by
    rw [E.point_centralizer_subgroupOf_eq_comap v]
    change P.comap S.projection = (P.comap c.toMonoidHom).comap π
    rw [comap_comap,hcπ]
  let e : C ≃* R.comap π :=
    (subgroupOfEquivOfLe (show C ≤ L from inf_le_left)).symm.trans (MulEquiv.subgroupCongr hC)
  apply (map_injective (f := e.toMonoidHom) e.injective)
  rw [map_pResidual_of_surjective 2 e.toMonoidHom e.surjective,
    map_solvableResidual_eq e.toMonoidHom e.surjective]
  exact hres

/-- The source two-residual is the existing perfect residual, with the same embedding. -/
theorem six_pointResidual_eq_twoResidual (v : V)
    (hv : weight (E.coordinates v).toAdd.val = 6) :
    SylowNormalizer.pointResidual L (v : G) =
      (pResidual 2 (L ⊓ centralizer ({(v : G)} : Set G) : Subgroup G)).map
        (L ⊓ centralizer ({(v : G)} : Set G)).subtype := by
  rw [E.six_point_pResidual_eq_solvableResidual v hv]
  rfl

end Setup.NaturalCoordinates
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
