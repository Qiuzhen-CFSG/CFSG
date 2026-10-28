module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.CoreReduction
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Application.Source
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.SolvableNormalSup
public import Stellmacher.ElementaryAbelianMaxJWeakClosure
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# Preparing the terminal Thompson extension

All groups here are intrinsic to the source group `H = G₀`. Its normal
two-core contains the module `V`; the two-group centralizer of `V` makes
that core self-centralizing. Every overgroup of the core therefore has
generalized Fitting subgroup equal to its two-core. Thompson heredity
identifies `J(QJ(U))` with `J(U)`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
15.3.68, printed pp.1154–1155, and B.2.3, printed p.75.
-/

public section
open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.ThompsonExtension

variable {H : Type*} [Group H] [Finite H]

/-- The actual extension, formed inside `G₀`. -/
@[expose] noncomputable def extension (U : Sylow 2 H) : Subgroup H :=
  elementaryAbelianMaxJ (U : Subgroup H) ⊔ pPrimeCore 3 H

/-- The source subgroup `QJ(U)`. -/
@[expose] noncomputable def sylowImage (U : Sylow 2 H) : Subgroup H :=
  pCore 2 H ⊔ elementaryAbelianMaxJ (U : Subgroup H)

/-- The generated subgroup of all two-reduced normal elementary abelian
two-subgroups. Two-reduction uses the actual centralizer quotient. -/
@[expose] noncomputable def reducedCore (K : Type*) [Group K] : Subgroup K :=
  sSup {V : Subgroup K | Chapter1.RadicalNormalizers.ThompsonSource.IsR2 V}

/-- Normality follows from normality of every member of the defining family. -/
instance reducedCore_normal (K : Type*) [Group K] : (reducedCore K).Normal := by
  apply Subgroup.normal_sSup
  rintro V ⟨hn, _⟩
  exact hn

/-- Heredity of the elementary Thompson subgroup, including rank zero. -/
theorem thompson_intermediate (S D : Subgroup H)
    (hJD : elementaryAbelianMaxJ S ≤ D) (hDS : D ≤ S) :
    elementaryAbelianMaxJ D = elementaryAbelianMaxJ S := by
  have hs := elementaryAbelianMaxOrder_le_and_j_le_of_eq D S hDS
  have hd := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le S D hJD
  have he := le_antisymm hs.1 hd.1
  exact le_antisymm (hs.2 he) (hd.2 he.symm)

omit [Finite H] in
/-- The subgroup `QJ(U)` lies between `J(U)` and `U`. -/
theorem sylowImage_le (U : Sylow 2 H) : sylowImage U ≤ (U : Subgroup H) :=
  sup_le (pCore_isPGroup.le_sylow_of_normal U) (sSup_le fun _ hA => hA.1)

/-- Consequently its Thompson subgroup is the source `J(U)`. -/
theorem thompson_sylowImage (U : Sylow 2 H) :
    elementaryAbelianMaxJ (sylowImage U) = elementaryAbelianMaxJ (U : Subgroup H) :=
  thompson_intermediate _ _ le_sup_right (sylowImage_le U)

omit [Finite H] in
/-- Normalizing `J` also normalizes `JO_{3'}(H)`. -/
theorem normalizes_extension (U : Sylow 2 H) (Y : Subgroup H)
    (hY : Y ≤ normalizer (elementaryAbelianMaxJ (U : Subgroup H) : Set H)) :
    Y ≤ normalizer (extension U : Set H) := by
  intro y hy
  rw [mem_normalizer_iff_map_conj_eq, extension, Subgroup.map_sup,
    mem_normalizer_iff_map_conj_eq.mp (hY hy), Normal.map_conj_eq]

omit [Finite H] in
/-- The centralizer of the ambient two-core is a normal two-group. -/
theorem core_selfCentralizing (V R : Subgroup H) (hV : V ≤ pCore 2 H)
    (hC : centralizer (V : Set H) ≤ R) (hR : IsPGroup 2 R) :
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  exact le_sSup ⟨inferInstance, hR.to_le ((centralizer_le hV).trans hC)⟩

/-- Every overgroup of the self-centralizing two-core has characteristic two. -/
theorem overgroup_generalizedFitting (K : Subgroup H) (hQK : pCore 2 H ≤ K)
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H) :
    Theory.GroupTheory.generalizedFitting K = pCore 2 K := by
  have hQ : (pCore 2 H).subgroupOf K ≤ pCore 2 K :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  apply Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2
  intro x hx
  apply hQ
  apply hc
  rw [mem_centralizer_iff]
  intro q hq
  exact congrArg Subtype.val (mem_centralizer_iff.mp hx ⟨q, hQK hq⟩ (hQ hq))

/-- Solvability of a normal solvable subgroup extends across a two-subgroup. -/
theorem extension_solvable (U : Sylow 2 H) (hP : Group.IsSolvable (pPrimeCore 3 H)) :
    Group.IsSolvable (extension U) := by
  let J := elementaryAbelianMaxJ (U : Subgroup H)
  let X := extension U
  let : Group.IsSolvable (pPrimeCore 3 H) := hP
  let : Group.IsSolvable ((pPrimeCore 3 H).subgroupOf X) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show pPrimeCore 3 H ≤ X from le_sup_right)).toMonoidHom)
      (subgroupOfEquivOfLe (show pPrimeCore 3 H ≤ X from le_sup_right)).injective
  have hj : IsPGroup 2 J := U.isPGroup'.to_le (sSup_le fun _ hA => hA.1)
  let : Group.IsNilpotent (J.subgroupOf X) := hj.comap_subtype.isNilpotent
  apply Group.isSolvable_of_normal_sup_eq_top ((pPrimeCore 3 H).subgroupOf X)
    (J.subgroupOf X)
  rw [← subgroupOf_sup (show pPrimeCore 3 H ≤ X from le_sup_right)
    (show J ≤ X from le_sup_left), show pPrimeCore 3 H ⊔ J = X from sup_comm _ _]
  exact subgroupOf_self X

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.ThompsonExtension
