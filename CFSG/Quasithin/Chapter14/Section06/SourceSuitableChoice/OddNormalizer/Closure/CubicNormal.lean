module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.PrimeBounds.Suzuki
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.ThreeFree
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection

/-!
# Solvability of the normal cubic-residual closure

When O²(H) is normal in Mc, subnormal two-core transport identifies its
image in Mc/O₂(Mc) with the original elementary residual of order nine.
Every C-component of that quotient must then be a Suzuki group. The actual
maximal-prime Suzuki exclusion contradicts such a component, so Mc is
solvable. The proof retains both literal quotient maps and relative normality.

The full source specialization discharges the quotient's SQTK and Suzuki
premises using the chosen maximal two-local and global maximal odd prime.
The primitive and exchanged-factor inputs are produced by
qt-e-quintic-recognition and qt-e-14612-singleton. The p=3 input remains with
qt-e-14615-quintic-exclusion. The normalizer and suitable-involution consumer
is OddNormalizer.NormalClosureBranch; strict closure assembly remains with
qt-e-suitable-odd-normalizer.

Source: Aschbacher--Smith, proof of 14.6.14(1), printed p.1033.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

/-- The closed residual has its original elementary quotient inside Mc/O₂(Mc). -/
theorem closed_residual_image_equiv
    {H Mc : Subgroup G} (hHMc : H ≤ Mc)
    (hclosure : residualClosure H Mc = residual H)
    (hprim : PrimitiveResidual H 3) :
    Nonempty ((((residual H).subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) ≃*
      pResidual 2 (H ⧸ pCore 2 H)) := by
  have hKMc := (residual_le H).trans hHMc
  have hn : Mc ≤ normalizer (residual H : Set G) := by
    rw [←hclosure]
    exact le_normalizer_conjugateSpanBy _ _
  let : ((residual H).subgroupOf Mc).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKMc).mpr hn
  let e := subgroupOfEquivOfLe hKMc
  let eq := QuotientGroup.congr (pCore 2 ((residual H).subgroupOf Mc))
    (pCore 2 (residual H)) e (pCore_map_iso 2 e)
  let ei := (Normal.isSubnormal (inferInstance : ((residual H).subgroupOf Mc).Normal)).quotientCoreImageEquiv 2
  let := hprim.elementary
  obtain ⟨er,_⟩ := residual_quotient_equiv (p := 3) (by decide) H
    (IsElementaryAbelian.isPGroup 3 _)
  exact ⟨ei.symm.trans (eq.trans er)⟩

/-- Saturation of three-rank and Suzuki exclusion give solvability in the
normal cubic-residual branch, retaining the actual two-core quotient. -/
theorem solvable_of_closed_cubic_residual
    {H Mc : Subgroup G} (hHMc : H ≤ Mc)
    (hsq : IsSQTK KnownSimple.IsKnownSimple Mc)
    (hno : NoSuzukiComponents Mc)
    (hclosure : residualClosure H Mc = residual H)
    (hprim : PrimitiveResidual H 3)
    (hc : Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 3 ^ 2) : Group.IsSolvable Mc := by
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let E := ((residual H).subgroupOf Mc).map q
  have hKMc := (residual_le H).trans hHMc
  have hn : Mc ≤ normalizer (residual H : Set G) := by
    rw [←hclosure]
    exact le_normalizer_conjugateSpanBy _ _
  let : ((residual H).subgroupOf Mc).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKMc).mpr hn
  let : E.Normal := (inferInstance : ((residual H).subgroupOf Mc).Normal).map q
    (QuotientGroup.mk'_surjective _)
  obtain ⟨e⟩ := closed_residual_image_equiv hHMc hclosure hprim
  let := hprim.elementary
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.of_surjective
    e.symm.toMonoidHom e.symm.surjective
  have hE : Nat.card E = 9 := by rw [Nat.card_congr e.toEquiv,hc]; norm_num
  have hQ : IsSQTK KnownSimple.IsKnownSimple (Mc ⧸ pCore 2 Mc) := by
    refine ⟨?_,hsq.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  by_contra hs
  obtain ⟨J,hJ⟩ := exists_isCComponent_of_not_isSolvable hs
  let : Group.IsNilpotent (pCore 2 Mc) := pCore_isNilpotent
  obtain ⟨m,hm,he⟩ := Chapter1.Section02.cComponent_suzuki_of_normal_elementary_nine
    hQ (pCore_quotient_pCore_eq_bot 2) E hE (hJ.map_quotient (pCore 2 Mc))
  have heJ : (J.map Mc.subtype).subgroupOf Mc = J :=
    comap_map_eq_self_of_injective Mc.subtype_injective J
  apply hno (J.map Mc.subtype) (map_subtype_le _) (by rwa [heJ]) m (by omega)
  change Nonempty ((((J.map Mc.subtype).subgroupOf Mc).map q) ≃*
    BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
  rw [heJ]
  exact he

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))

include hG hempty hM hunique hmany hcard e hab hH

/-- The source normal-closure branch at p=3 is solvable; neither solvability
nor a source closure classification is an extra premise. -/
theorem source_solvable_of_normal_cubic_residual
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hp : p = 3) (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (hclosure : residualClosure H Mc = residual H) : Group.IsSolvable Mc := by
  subst p
  have hHMc : H ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hunique)
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hunique.symm ▸ Set.mem_singleton Mc
  exact solvable_of_closed_cubic_residual hHMc (hG.twoLocal_sqtk hMc.1.1)
    (source_no_suzuki_components hG T hunique hH hHMc (Or.inl rfl) hmax hprim)
    hclosure hprim d.residual_card
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
