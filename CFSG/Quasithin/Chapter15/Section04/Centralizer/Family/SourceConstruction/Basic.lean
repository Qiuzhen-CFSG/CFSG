module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Defs
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.CoreConsequence
public import CFSG.Quasithin.Chapter1.Section03.Basic
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.SourceFactors.Permutation
public import Theory.GroupTheory.PResidual.NormalizerImage
public import Theory.GroupTheory.PResidual.NormalityLift

/-!+# The source Y-family and its quotient coordinates

The family is exactly the union of the uppercase and lowercase Xi families,
restricted by Y = [Y,J(T)]. The local module is the normal closure of
Omega_1(Z(T)) in M. S and E are the existing Baumann subgroup and Thompson
alpha, respectively; no new versions of either subgroup are introduced.

Every family member in an overgroup M of the Sylow subgroup T is recovered
from its image in M/O_2(M) by taking the two-residual of the preimage. Indeed,
O_2(M) lies in T and therefore normalizes the member, which is two-perfect.
Consequently equality and normalizers can be checked in that same quotient.
These coordinates also define the source candidate from [O_3(Mbar),J(T)].
They do not assert that the candidate belongs to the family: its quotient
structure and nontrivial action remain to be constructed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the definition preceding Lemma 15.4.12 and its proof, printed pp.1160–1161.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section04
variable {G : Type*} [Group G]

/-- The family Y immediately preceding source 15.4.12. -/
def Y (T : Subgroup G) : Set (Subgroup G) :=
  {X | (X ∈ Chapter1.Xi G T ∨ X ∈ Xi T) ∧ X = ⁅X, elementaryAbelianMaxJ T⁆}

namespace YFamily

/-- Both source families consist of two-perfect groups. -/
theorem perfect {T X : Subgroup G} (hX : X ∈ Y T) : IsPPerfect 2 X := by
  rcases hX.1 with h | h
  · exact h.perfect
  · exact h.2.1

/-- Invariance is relative to T, not normality in the ambient group. -/
theorem invariant {T X : Subgroup G} (hX : X ∈ Y T) :
    T ≤ normalizer (X : Set G) := by
  rcases hX.1 with h | h
  · exact h.invariant
  · exact h.1

theorem commutator_eq {T X : Subgroup G} (hX : X ∈ Y T) :
    ⁅X, elementaryAbelianMaxJ T⁆ = X := hX.2.symm

/-- The join in the definition is an actual member of H(T). -/
theorem join_mem_HOver {T X : Subgroup G} (hX : X ∈ Y T) :
    X ⊔ T ∈ Chapter1.HOver G (T : Set G) := by
  rcases hX.1 with h | h
  · exact ⟨h.join_mem_H, show T ≤ X ⊔ T from le_sup_right⟩
  · exact h.2.2.1

/-- The odd quotient in either source family excludes the trivial subgroup. -/
theorem ne_bot {T X : Subgroup G} (hX : X ∈ Y T) : X ≠ ⊥ := by
  rcases hX.1 with h | h
  · exact h.ne_bot
  · intro he
    have hs : Subsingleton X := by rw [he]; infer_instance
    exact Xi.core_ne_top h (Subsingleton.elim _ _)

/-- Relative normality in XT follows directly from T-invariance. -/
theorem normal_in_join {T X : Subgroup G} (hX : X ∈ Y T) :
    (X.subgroupOf (X ⊔ T)).Normal :=
  normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer (YFamily.invariant hX))

end YFamily

namespace FamilySource
open LocalSetup.TwoFactors.SourceFactors.Permutation

/-- The actual source module V(M), in ambient coordinates. -/
def localV (T M : Subgroup G) : Subgroup G :=
  (normalClosure ((omegaOneCenterAmbient T).subgroupOf M : Set M)).map M.subtype

/-- The quotient by the actual local two-core. -/
abbrev CoreQuotient (M : Subgroup G) := M ⧸ pCore 2 M

def quotientMap (M : Subgroup G) : M →* CoreQuotient M := QuotientGroup.mk' (pCore 2 M)

/-- The image of an ambient subgroup, restricted to M, in the fixed quotient. -/
def image (M X : Subgroup G) : Subgroup (CoreQuotient M) :=
  (X.subgroupOf M).map (quotientMap M)

/-- The source construction takes the residual after taking the preimage. -/
def lift (M : Subgroup G) (A : Subgroup (CoreQuotient M)) : Subgroup G :=
  (residualPreimage (quotientMap M) A).map M.subtype

/-- Xbar = [O_3(Mbar),J(T)] in the source, with J(T) mapped by the same quotient. -/
noncomputable def Xbar (T M : Subgroup G) : Subgroup (CoreQuotient M) :=
  ⁅pCore 3 (CoreQuotient M), image M (elementaryAbelianMaxJ T)⁆

/-- The initial candidate Y_0, before the irreducibility case distinction. -/
noncomputable def initialMember (T M : Subgroup G) : Subgroup G := lift M (Xbar T M)

theorem lift_le (M : Subgroup G) (A : Subgroup (CoreQuotient M)) : lift M A ≤ M :=
  map_subtype_le _

theorem lift_perfect [Finite G] (M : Subgroup G) (A : Subgroup (CoreQuotient M)) :
    IsPPerfect 2 (lift M A) :=
  (residualPreimage_perfect (quotientMap M) A).of_surjective
    (M.subtype.subgroupMap _) (M.subtype.subgroupMap_surjective _)

/-- The literal normal closure gives the centralizer equality of 15.4.11(1). -/
theorem localV_centralizer (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T) :
    M ⊓ centralizer (localV T M : Set G) = M.pCoreIn 2 :=
  centralizer_normalClosure_eq_core T _ M
    (fun _ hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1) hTM hC

/-- The normalizing two-group kernel is exactly what is needed to recover a
two-perfect subgroup from its quotient image. -/
theorem residualPreimage_image_eq {D Q : Type*} [Group D] [Group Q]
    (q : D →* Q) (A : Subgroup D) (hp : IsPPerfect 2 A)
    (hk : IsPGroup 2 q.ker) (hn : q.ker ≤ normalizer (A : Set D)) :
    residualPreimage q (A.map q) = A := by
  change (pResidual 2 ((A.map q).comap q)).map ((A.map q).comap q).subtype = A
  rw [comap_map_eq]
  exact embedded_pResidual_sup_kernel q A hp hk hn

/-- O_2(M) normalizes every T-invariant subgroup in M. -/
theorem core_normalizes (T : Sylow 2 G) {M X : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hn : (T : Subgroup G) ≤ normalizer (X : Set G)) :
    (quotientMap M).ker ≤ normalizer (X.subgroupOf M : Set M) := by
  have hc : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    have h := pCoreIn_le_sylow M (T.subtype hTM)
    rwa [T.coe_subtype, map_subgroupOf_eq_of_le hTM] at h
  rw [quotientMap, QuotientGroup.ker_mk']
  intro c hc'
  have hn' := hn (hc (mem_map.mpr ⟨c, hc', rfl⟩))
  apply mem_normalizer_iff.mpr
  intro x
  exact mem_normalizer_iff.mp hn' (x : G)

/-- Every family member is the residual lift of its actual quotient image. -/
theorem member_eq_lift_image (T : Sylow 2 G) {M X : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hX : X ∈ Y (T : Subgroup G)) (hXM : X ≤ M) :
    lift M (image M X) = X := by
  have hp : IsPPerfect 2 (X.subgroupOf M) :=
    (YFamily.perfect hX).of_surjective (subgroupOfEquivOfLe hXM).symm.toMonoidHom
      (subgroupOfEquivOfLe hXM).symm.surjective
  have hk : IsPGroup 2 (quotientMap M).ker := by
    rw [quotientMap, QuotientGroup.ker_mk']; exact pCore_isPGroup
  rw [lift, image, residualPreimage_image_eq (quotientMap M) _ hp hk
    (core_normalizes T hTM (YFamily.invariant hX)), map_subgroupOf_eq_of_le hXM]

/-- Thus the quotient calculation distinguishes ALL family members in M. -/
theorem members_eq_of_image_eq (T : Sylow 2 G) {M X X' : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M)
    (hX : X ∈ Y (T : Subgroup G)) (hXM : X ≤ M)
    (hX' : X' ∈ Y (T : Subgroup G)) (hX'M : X' ≤ M)
    (he : image M X = image M X') : X = X' := by
  rw [← member_eq_lift_image T hTM hX hXM, he,
    member_eq_lift_image T hTM hX' hX'M]

/-- Normality of the quotient image lifts to relative normality in M. -/
theorem member_normal_of_image_normal (T : Sylow 2 G) {M X : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hX : X ∈ Y (T : Subgroup G)) (hXM : X ≤ M)
    (hn : (image M X).Normal) : (X.subgroupOf M).Normal := by
  let : ((X.subgroupOf M).map (quotientMap M)).Normal := hn
  have hp : IsPPerfect 2 (X.subgroupOf M) :=
    (YFamily.perfect hX).of_surjective (subgroupOfEquivOfLe hXM).symm.toMonoidHom
      (subgroupOfEquivOfLe hXM).symm.surjective
  have hk : IsPGroup 2 (quotientMap M).ker := by
    rw [quotientMap, QuotientGroup.ker_mk']; exact pCore_isPGroup
  exact normal_of_map_normal_of_pPerfect (quotientMap M) _ hp hk
    (core_normalizes T hTM (YFamily.invariant hX))

end FamilySource
end CFSG.Quasithin.Chapter15.Section04
