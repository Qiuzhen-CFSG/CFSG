module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.SelectedLocalClass
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Baumann
import all Theory.SpecificGroups.SymmetricFive.OuterFourGeometry
public import Theory.SpecificGroups.SymmetricFive.AutomorphismRank
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.CoveredSeed
/-!
# The original central-cover S₅ action and the selected pair

The natural quotient determines both the Thompson and Baumann images.
The component quotient and full Sylow product make the action kernel a
two-group, while the faithful S₅ quotient kills the original two-core.
These facts and the equivariantly lifted fixed vector construct the actual
selected local-class embedding on the same original Baumann group.

The internal eight-word table is used only to identify the marked four-group
with the standard two disjoint transpositions. The module's central layer
and its literal quotient projection remain in every source theorem.
Source: C.1.21(4), C.1.23(1), printed pp.129–130.
-/
public section
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
open ChapterB Theory.SpecificGroups.SymmetricFive Theory.SpecificGroups.SymmetricFive.CubicSelection
universe u
variable {H : Type u} [Group H] [Finite H]

private theorem four_eq_D : OuterFourGeometry.four = Offenders.D 5 := by
  have h0 : Equiv.swap (0 : Fin 5) 1 ∈ Offenders.D 5 := Offenders.pairSwap_mem 0 (by decide)
  have h1 : Equiv.swap (2 : Fin 5) 3 ∈ Offenders.D 5 := Offenders.pairSwap_mem 1 (by decide)
  apply le_antisymm
  · rintro x ⟨i,rfl⟩
    fin_cases i
    · exact one_mem _
    · exact h0
    · exact h1
    · exact mul_mem h0 h1
  · apply (closure_le _).mpr
    rintro x ⟨i,hi,rfl⟩
    fin_cases i
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

/-- On the actual marked full Sylow, the original natural action determines
both J and Baumann images. No image identity for either is assumed. -/
theorem marked_quotient_images (R : Sylow 2 H)
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U] (hUR : U ≤ R)
    (q : H →* Sym) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H))
    (hR : (R : Subgroup H).map q = OuterFourGeometry.eight)
    (p : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (NormalElementaryQuotient.representation U q hq hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (p v))
    (hfix : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hk g v = v)
    (hJ : ¬ elementaryAbelianMaxJ (R : Subgroup H) ≤ centralizer (U : Set H)) :
    (elementaryAbelianMaxJ (R : Subgroup H)).map q = OuterFourGeometry.four ∧
      (baumann (R : Subgroup H)).map q = OuterFourGeometry.four := by
  have hD : Offenders.D 5 ≤ (R : Subgroup H).map q := by
    rw [hR,←four_eq_D]
    exact OuterFourGeometry.four_le_eight
  have hj := SymmetricFive.source_thompson_image U R hUR q hq hk
    p hp he hfix hJ hD
  have hb := (SymmetricFive.source_thompson_baumann U R hUR q hq hk
    p hp he hfix hJ).1
  exact ⟨hj.trans four_eq_D.symm,hb.symm.trans (hj.trans four_eq_D.symm)⟩



/-- The actual full natural S₅ action produces a local-class witness for
the original characteristic pair. Kernel, core and Baumann image hypotheses
are derived from the original A₅ component and Sylow data. -/
theorem marked_quotient_original_pair
    (R : Sylow 2 H) (hfit : generalizedFitting H = pCore 2 H)
    (L : Subgroup H) [L.Normal] (hprod : L ⊔ (R : Subgroup H) = ⊤)
    (hcard : Nat.card (L ⧸ pCore 2 L) = Nat.card (alternatingGroup (Fin 5)))
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* Sym) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H))
    (hR : (R : Subgroup H).map q = OuterFourGeometry.eight)
    (hL : L.map q = alternatingGroup (Fin 5))
    (p : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (NormalElementaryQuotient.representation U q hq hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (p v))
    (hfix : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hk g v = v)
    (hJ : ¬ elementaryAbelianMaxJ (R : Subgroup H) ≤ centralizer (U : Set H))
    (D : GlaubermanNiles.CharacteristicPair (baumann (R : Subgroup H)))
    (hD : D.Universal.{u,u}) :
    ∃ (A : Subgroup (cubicLocalGroup q)) (j : baumann (R : Subgroup H) →* A),
      A.map (cubicLocalGroup q).subtype = selectedResidual q L ⊔ baumann (R : Subgroup H) ∧
      ((cubicLocalGroup q).subtype.comp A.subtype).comp j = (baumann (R : Subgroup H)).subtype ∧
      GlaubermanNiles.InLocalClass j ∧ GlaubermanNiles.Alternatives D.first D.second j := by
  have hkp := action_kernel_twoGroup q L R hprod R.isPGroup' hL hcard
  have hUR : U ≤ R := (show U ≤ pCore 2 H from
    le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩).trans
      (pCore_isPGroup.le_sylow_of_normal R)
  have hQ : pCore 2 H ≤ q.ker := by
    rw [←MonoidHom.comap_bot]
    apply map_le_iff_le_comap.mp
    rw [←Theory.SpecificGroups.SymmetricFive.pCore_two_eq_bot]
    exact le_sSup ⟨Subgroup.Normal.map inferInstance q hq,pCore_isPGroup.map q⟩
  have hUP : U ≤ cubicLocalTwoGroup q := by
    have hUc : U ≤ centralizer (U : Set H) := le_centralizer_iff_isMulCommutative.mpr inferInstance
    have hUk : U ≤ q.ker := hk.symm ▸ hUc
    intro x hx
    change q x ∈ OuterFourGeometry.four
    rw [MonoidHom.mem_ker.mp (hUk hx)]
    exact one_mem _
  obtain ⟨hJi,hBi⟩ := marked_quotient_images R U hUR q hq hk hR p hp he hfix hJ
  exact selected_cubic_original_pair_of_seed q hq hkp hfit hQ L hL R hR
    (hkp.le_sylow_of_normal R) hBi hJi
    (selected_covered_omega_seed U q hq hk L _ hL
      (map_comap_eq_self_of_surjective hq _) hUP p hp he hfix) D hD

end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
