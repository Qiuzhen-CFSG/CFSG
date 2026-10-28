module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.PrimeBounds.SuzukiModels
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.PrimeBounds.Parameters
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Primitive
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Excluding Suzuki components in the maximal-prime closure

The primitive elementary odd residual makes the original outside subgroup
solvable. A concrete Suzuki Borel then extends its image in Mc/O₂(Mc) to a
solvable subgroup with the defining odd torus divisor. Pulling back along
the literal quotient map gives H ≤ J ≤ Mc, contradicting the maximal-prime
bound and the odd binary torus arithmetic.

The final specialization retains the full rank-two source context and the
original exchanged-factor data. It proves the first two preliminary steps
of 14.6.14; closure recognition and its normalizer application remain with
qt-e-suitable-odd-normalizer. The primitive/14.6.12 inputs retain their
producers qt-e-quintic-recognition and qt-e-14612-singleton.

Source: Aschbacher--Smith, proof of 14.6.14, printed pp.1032--1033.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The primitive residual yields solvability through the two-core quotient. -/
theorem primitiveResidual_isSolvable (H : Subgroup G) {p : ℕ} [Fact p.Prime]
    (d : PrimitiveResidual H p) : Group.IsSolvable H := by
  let := d.elementary
  let : Group.IsNilpotent (pResidual 2 (H ⧸ pCore 2 H)) :=
    (IsElementaryAbelian.isPGroup p _).isNilpotent
  let : Group.IsNilpotent ((H ⧸ pCore 2 H) ⧸ pResidual 2 (H ⧸ pCore 2 H)) :=
    (isPGroup_quotient_pResidual 2).isNilpotent
  let : Group.IsSolvable (H ⧸ pCore 2 H) :=
    (Group.isSolvable_iff_subgroup_quotient (pResidual 2 (H ⧸ pCore 2 H))).mpr
      ⟨inferInstance,inferInstance⟩
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 H)).mpr ⟨inferInstance,inferInstance⟩

/-- Lift the concrete Borel extension through the actual two-core quotient. -/
theorem source_suzuki_component_solvable_extension
    (T : Sylow 2 G) (H Mc : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hHMc : H ≤ Mc) (hs : Group.IsSolvable H)
    (L : Subgroup G) (hL : (L.subgroupOf Mc).IsCComponent)
    {m : ℕ} (hm : 0 < m)
    (e : ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) ≃* SuzukiMatrixGroup m) :
    ∃ J : Subgroup G, H ≤ J ∧ J ≤ Mc ∧ Group.IsSolvable J ∧
      2 ^ (2 * m + 1) - 1 ∣ Nat.card J := by
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let D := (L.subgroupOf Mc).map q
  let S := (T.subtype (hTH.trans hHMc)).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Mc))
  let A := (H.subgroupOf Mc).map q
  let := hs
  let : Group.IsSolvable (H.subgroupOf Mc) :=
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hHMc).toMonoidHom)
      (subgroupOfEquivOfLe hHMc).injective
  have hAs : Group.IsSolvable A :=
    Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
  let : Group.IsNilpotent (pCore 2 Mc) := pCore_isPGroup.isNilpotent
  have hD : D.IsCComponent := hL.map_quotient (pCore 2 Mc)
  obtain ⟨B,hAB,hBs,hd⟩ := suzuki_component_solvable_extension S A D
    (map_mono (subgroupOf_mono Mc hTH)) hAs hD hm e
  let J := (B.comap q).map Mc.subtype
  have hHJ : H ≤ J := by
    intro h hh
    exact ⟨⟨h,hHMc hh⟩,hAB (mem_map_of_mem q hh),rfl⟩
  let := hBs
  let : Group.IsSolvable q.ker := by
    dsimp [q]
    rw [QuotientGroup.ker_mk']
    infer_instance
  let : Group.IsSolvable (B.comap q) := isSolvable_comap_of_solvable_ker q B
  refine ⟨J,hHJ,map_subtype_le _,Group.isSolvable_of_surjective
    (Mc.subtype.subgroupMap_surjective _),?_⟩
  rw [card_map_of_injective Mc.subtype_injective]
  apply hd.trans
  have hc := card_map_dvd (B.comap q) q
  rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (pCore 2 Mc))] at hc

/-- Maximality of the chosen prime rules out every actual Suzuki component image. -/
theorem source_no_suzuki_components_of_solvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M Mc H : Subgroup G}
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hHMc : H ≤ Mc) (hs : Group.IsSolvable H)
    {p : ℕ} (hp : p = 3 ∨ p = 5) (hmax : MaximalOddPrime (T : Subgroup G) M p) :
    NoSuzukiComponents Mc := by
  intro L _hLMc hL m hm he
  obtain ⟨e⟩ := he
  obtain ⟨J,hHJ,hJMc,hJs,hd⟩ := source_suzuki_component_solvable_extension
    T H Mc hH.1.2 hHMc hs L hL hm e
  exact source_no_odd_binary_torus_in_solvable_overgroup hG T hunique hH hp hmax
    J hHJ hJMc hJs (by omega : 2 ≤ 2*m+1) ⟨m,rfl⟩ hd

/-- The earlier primitive data discharge the solvability premise. -/
theorem source_no_suzuki_components
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M Mc H : Subgroup G}
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hHMc : H ≤ Mc)
    {p : ℕ} (hp : p = 3 ∨ p = 5) (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (d : PrimitiveResidual H p) : NoSuzukiComponents Mc := by
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  exact source_no_suzuki_components_of_solvable hG T hunique hH hHMc
    (primitiveResidual_isSolvable H d) hp hmax
open Representation.BinaryOffender SourcePreliminaries
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open scoped IsMulCommutative

/-- The two preliminary assertions of original 14.6.14 for the same outside
subgroup and maximal prime. The earlier primitive and exchanged-factor inputs
are retained literally; no component classification is assumed. -/
theorem source_exchanged_closure_prime_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
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
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p) :
    SolvableOvergroupPrimeBound H Mc p ∧ NoSuzukiComponents Mc := by
  have hF := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  have hHMc : H ≤ Mc :=
    hF.H_centralizes.trans (InitialSource.centralizer_le_partner T hunique)
  exact ⟨source_solvable_overgroup_prime_bound hG T hunique H hH d.prime hmax,
    source_no_suzuki_components hG T hunique hH hHMc d.prime hmax hprim⟩
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
