module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.Basic
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass
public import Theory.GroupTheory.NormalClosureCentralizerCore

/-!
# The actual kernel in a selected Baumann overgroup

Suppose the selected subgroup K has a Sylow subgroup whose ambient image
is Baum(T). The original identity C_G(Ω₁(Z(T)))=T forces the centralizer
inside K of the marked Ω₁(Z(Baum(T))) to be exactly that Sylow subgroup.
Indeed the original central seed lies in the Baumann omega center, while
K∩T is precisely the selected Sylow image. Normal closure then cuts the
centralizer down to O₂(K).

The final comparison identifies the literal C.1.17 LocalStar quotient
with K/O₂(K), commuting with their original quotient maps. This supplies
the source kernel for the selected factor in C.1.26 and its application
in Aschbacher--Smith 15.4.7, printed pp.132 and1158.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
open FamilySource ChapterC.GlaubermanNiles
universe u
variable {G : Type u} [Group G]

private theorem central_seed_le_baumann_omega (T : Subgroup G) :
    omegaOneCenterAmbient T ≤ omegaOneCenterAmbient (ChapterB.baumann T) := by
  intro z hz
  obtain ⟨hzt,hz2,hzc⟩ := (mem_omegaOneCenterAmbient_iff T z).mp hz
  have hzB : z ∈ ChapterB.baumann T := by
    refine ⟨hzt,?_⟩
    intro a ha
    exact hzc a ((show elementaryAbelianMaxJ T ≤ T from sSup_le fun _ hA => hA.1) ((mem_omegaOneCenterAmbient_iff _ _).mp ha).1)
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr ⟨hzB,hz2,fun b hb => hzc b hb.1⟩

/-- The marked Baumann Sylow is exactly the centralizer of its literal
omega center inside the selected original overgroup. -/
theorem selected_omega_centralizer (T : Sylow 2 G) (K : Subgroup G)
    (P : Sylow 2 K)
    (hP : (P : Subgroup K).map K.subtype = ChapterB.baumann (T : Subgroup G))
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T) :
    let hBK : ChapterB.baumann (T : Subgroup G) ≤ K := hP ▸ map_subtype_le _
    centralizer ((omegaCenter (ChapterB.baumann (T : Subgroup G))).map
      (inclusion hBK) : Set K) = P := by
  let B := ChapterB.baumann (T : Subgroup G)
  let hBK : B ≤ K := by
    change ChapterB.baumann (T : Subgroup G) ≤ K
    rw [←hP]
    exact map_subtype_le _
  let A := (omegaCenter B).map (inclusion hBK)
  change centralizer (A : Set K) = P
  have hA : A.map K.subtype = omegaOneCenterAmbient B := by
    rw [map_map]
    rfl
  have hBT : B ≤ (T : Subgroup G) := inf_le_left
  have hKT : K ⊓ (T : Subgroup G) = B := by
    rw [inf_comm]
    exact (inf_eq_sylow_map P T.isPGroup' (hP ▸ hBT)).trans hP
  apply map_injective K.subtype_injective
  rw [map_centralizer_subtype,hA,hP]
  apply le_antisymm
  · calc
      K ⊓ centralizer (omegaOneCenterAmbient B : Set G) ≤
          K ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
        inf_le_inf_left _ (centralizer_le (central_seed_le_baumann_omega _))
      _ = B := by rw [hC,hKT]
  · refine le_inf hBK ?_
    intro b hb z hz
    exact ((mem_omegaOneCenterAmbient_iff B z).mp hz).2.2 b hb |>.symm

/-- Taking the original omega-center normal closure cuts the action kernel
down to the actual two-core of the selected overgroup. -/
theorem selected_localKernel (T : Sylow 2 G) (K : Subgroup G)
    (P : Sylow 2 K)
    (hP : (P : Subgroup K).map K.subtype = ChapterB.baumann (T : Subgroup G))
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T) :
    let hBK : ChapterB.baumann (T : Subgroup G) ≤ K := hP ▸ map_subtype_le _
    ChapterC.GlaubermanNiles.localKernel (inclusion hBK) = pCore 2 K := by
  exact centralizer_normalClosure_eq_pCore_of_eq_sylow P _
    (selected_omega_centralizer T K P hP hC)

/-- The comparison with the core quotient commutes with the original
quotient map on every element of the selected overgroup. -/
theorem selected_localStar_equiv (T : Sylow 2 G) (K : Subgroup G)
    (P : Sylow 2 K)
    (hP : (P : Subgroup K).map K.subtype = ChapterB.baumann (T : Subgroup G))
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T) :
    let hBK : ChapterB.baumann (T : Subgroup G) ≤ K := hP ▸ map_subtype_le _
    ∃ f : LocalStar (inclusion hBK) ≃* CoreQuotient K,
      ∀ k : K, f (QuotientGroup.mk' (ChapterC.GlaubermanNiles.localKernel (inclusion hBK)) k) =
        quotientMap K k := by
  exact ⟨QuotientGroup.quotientMulEquivOfEq (selected_localKernel T K P hP hC),fun _ => rfl⟩

end CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
