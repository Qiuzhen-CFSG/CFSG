module

public import CFSG.Quasithin.Chapter6.Section01.SourceHStarOvergroupAction
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarLeftCartanOvergroup
public import Theory.GroupTheory.JoinCentralizerCore
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections

/-!
# The two-core of the actual H-star Cartan join

Put `Z = Ω₁(Z(T))`, `X = ⟨A,H⟩` and `U = ⟨Zˣ⟩`. Once the earlier
source argument gives `C_H(⟨Zᴴ⟩) = O₂(H)`, a permuting left Hall actor
faithful on `Z` makes `C_T(U)` normal in both `AT` and `H`. Reducedness
then identifies this subgroup with `O₂(X)`.

The final consumer constructs the actual left Hall and its faithful join
from the natural fixed quotient. The earlier centralizer equality remains
explicit. This proves the join-centralizer step, not the preceding
centralizer equality or the final 6.1.5 contradiction.

Source: Aschbacher--Smith 6.1.5, printed p.667, first paragraph.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H A : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

omit [Finite G] h in
/-- The enlarged orbit's centralizer in `H` lies in the original Sylow,
using exactly the earlier source centralizer equality. -/
theorem hstar_join_orbit_centralizer_le_sylow
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hcentral : centralizer
      (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) :
        Set H) = pCore 2 H) :
    H ⊓ centralizer
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ H) : Set G) ≤
        (T : Subgroup G) := by
  intro x hx
  have hxcore : (⟨x, hx.1⟩ : H) ∈ pCore 2 H := by
    rw [← hcentral]
    intro y hy
    apply Subtype.ext
    exact hx.2 y (conjugateSpanBy_mono le_rfl le_sup_right hy)
  exact pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2) hxcore

/-- The source Cartan join has the exact two-core `C_T(U)`, with
normality in the entire join proved rather than supplied. -/
theorem hstar_join_core_eq_sylow_centralizer
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hX : A ⊔ H ∈ Chapter1.HOver G (T : Set G))
    (hperm : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G))
    (hfaith : A ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥)
    (hcentral : centralizer
      (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) :
        Set H) = pCore 2 H) :
    (A ⊔ H).pCoreIn 2 = (T : Subgroup G) ⊓ centralizer
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ H) : Set G) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let X := A ⊔ H
  let U := conjugateSpanBy Z X
  have hZT : Z ≤ (T : Subgroup G) :=
    fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hZX : Z ≤ X := hZT.trans hX.2
  have hUX : U ≤ X := conjugateSpanBy_le_self hZX
  have hred : IsPReduced 2 (U.subgroupOf X) := h.overgroup_omega_orbit_reduced hX
  have hcore : X.pCoreIn 2 ≤ centralizer (U : Set G) := by
    rintro x ⟨x', hx', rfl⟩ u hu
    exact congrArg X.subtype
      ((le_centralizer_iff.mp hred.le_centralizer_pCore hx') ⟨u, hUX hu⟩ hu)
  have hTZ : (T : Subgroup G) ≤ centralizer (Z : Set G) := by
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm
  exact pCoreIn_sup_eq_sylow_centralizer_of_faithful_seed T A H Z U
    hH.1.1.2 hperm hTZ (le_conjugateSpanBy Z X) hfaith
    (hstar_join_orbit_centralizer_le_sylow hH hcentral)
    (le_normalizer_conjugateSpanBy Z X) hcore

/-- Both source centralizers coincide with the join's core, which is
Sylow in its full orbit centralizer. All groups are the literal subgroups
of the original ambient group. -/
theorem hstar_join_centralizer_geometry
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hX : A ⊔ H ∈ Chapter1.HOver G (T : Set G))
    (hperm : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G))
    (hfaith : A ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥)
    (hcentral : centralizer
      (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) :
        Set H) = pCore 2 H) :
    let X := A ⊔ H
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    H ⊓ centralizer (U : Set G) = X.pCoreIn 2 ∧
      (A ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) = X.pCoreIn 2 ∧
      Chapter1.IsSylowIn 2 (X.pCoreIn 2) (X ⊓ centralizer (U : Set G)) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let X := A ⊔ H
  let U := conjugateSpanBy Z X
  have hcore : X.pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (U : Set G) :=
    h.hstar_join_core_eq_sylow_centralizer hH hX hperm hfaith hcentral
  have hTZ : (T : Subgroup G) ≤ centralizer (Z : Set G) := by
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm
  have hHC : H ⊓ centralizer (U : Set G) = X.pCoreIn 2 := by
    rw [hcore]
    exact le_antisymm (le_inf (hstar_join_orbit_centralizer_le_sylow hH hcentral)
      inf_le_right) (le_inf (inf_le_left.trans hH.1.1.2) inf_le_right)
  have hAC : (A ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) = X.pCoreIn 2 :=
    (inf_centralizer_sup_eq_of_faithful_seed A T Z U hperm hTZ
      (le_conjugateSpanBy Z X) hfaith).trans hcore.symm
  refine ⟨hHC, hAC, ?_⟩
  let C := X ⊓ centralizer (U : Set G)
  have hnC : X ≤ normalizer (C : Set G) :=
    (le_inf X.le_normalizer ((le_normalizer_conjugateSpanBy Z X).trans
      (normalizer_le_normalizer_centralizer U))).trans inf_normalizer_le_normalizer_inf
  have hCnorm : (C.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer (show C ≤ X from inf_le_left)).mpr hnC
  have hSyl : Chapter1.IsSylowIn 2 (T : Subgroup G) X :=
    ⟨T.subtype hX.2, map_subgroupOf_eq_of_le hX.2⟩
  have he : (T : Subgroup G) ⊓ C = X.pCoreIn 2 := by
    change (T : Subgroup G) ⊓ (X ⊓ centralizer (U : Set G)) = _
    rw [← inf_assoc,
      inf_eq_left.mpr (show (T : Subgroup G) ≤ X from hX.2), ← hcore]
  rw [← he]
  exact Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl inf_le_left
    hCnorm.isSubnormal

/-- The selected source Hall has all the centralizer geometry required in
the first paragraph of p.667. The only earlier source inputs retained are
the natural quotient and the full H-star orbit-centralizer equality. -/
theorem exists_hstar_left_cartan_centralizer_geometry
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hcentral : centralizer
      (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) :
        Set H) = pCore 2 H) :
    ∃ A : Subgroup G, A ≤ RankOneGeneric.localBorel T L ∧
      IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (RankOneGeneric.localBorel T L)) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      A ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥ ∧
      A ⊔ H ∈ Chapter1.HOver G (T : Set G) ∧
      (let X := A ⊔ H
       let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
       X.pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (U : Set G) ∧
       H ⊓ centralizer (U : Set G) = X.pCoreIn 2 ∧
       (A ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) = X.pCoreIn 2 ∧
       Chapter1.IsSylowIn 2 (X.pCoreIn 2) (X ⊓ centralizer (U : Set G))) := by
  obtain ⟨A,hA,hHall,hperm,hfaith,hX⟩ :=
    h.exists_hstar_left_cartan_overgroup hout hH hm hZH
  exact ⟨A,hA,hHall,hperm,hfaith,hX,
    h.hstar_join_core_eq_sylow_centralizer hH hX hperm hfaith hcentral,
    h.hstar_join_centralizer_geometry hH hX hperm hfaith hcentral⟩

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
