module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourCartan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CriticalProfileCentral

/-!
# A field-four alpha action excludes full middle central involutions

An involution central in the full middle stabilizer belongs to the common
edge Sylow center, hence to the adjacent alpha center. An actual cubic in
the alpha quotient's Sylow normalizer lifts to an element fixing the middle
vertex. Its fixed-point-free action on the natural alpha center kills that
involution. The intrinsic middle actor can still have a nontrivial center.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The actual field-four center action kills every central involution in
the full middle stabilizer. No beta quotient model or comparison is used. -/
theorem BTwoCenterActionData.full_middle_central_involution_eq_one
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v m w : Vertex (family P)} (c : BTwoCenterActionData (family P) v m w k W)
    (hactor : c.actor = graphLocalGroup (family P) v)
    (hcentral : Z (family P) m ≤ centerIn (graphLocalGroup (family P) m))
    (hk : Nat.card k = 4)
    (x : G) (hx : x ∈ (center (stabilizer (family P) m)).map
      (stabilizer (family P) m).subtype) (hx2 : x^2 = 1) : x = 1 := by
  let := finite_endpoints h
  let F := family P
  let M := stabilizer F m
  obtain ⟨z,hz,rfl⟩ := hx
  have hMC : M ≤ centralizer (zpowers (z : G) : Set G) := by
    apply le_centralizer_iff.mpr
    apply zpowers_le.mpr
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hy⟩)
  have hzp : IsPGroup 2 (zpowers (z : G)) :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) hx2).isPGroup 2 _
  have hzQ : zpowers (z : G) ≤ M.pCoreIn 2 :=
    le_pCoreIn_of_normalizes hzp (zpowers_le.mpr z.property)
      (hMC.trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨T,R,hTR⟩ := source_common_edge_sylow h hB hS c.middle.symm
  have hzT : (z : G) ∈ (T : Subgroup M).map M.subtype :=
    pCoreIn_le_sylow M T (hzQ (mem_zpowers _))
  have hzΩ : (z : G) ∈ omegaCenterIn ((T : Subgroup M).map M.subtype) := by
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨hzT,?_,hx2⟩
    intro y hy
    exact (congrArg Subtype.val
      (mem_center_iff.mp hz ⟨y,map_subtype_le _ hy⟩))
  rw [hTR] at hzΩ
  have hzZ : (z : G) ∈ Z F v :=
    (le_iSup (fun U : Sylow 2 (stabilizer F v) =>
      omegaCenterIn ((U : Subgroup (stabilizer F v)).map
        (stabilizer F v).subtype)) R) hzΩ
  let N := normalizer (c.imageSylow : Set SL(2,k))
  have hdiv : 3 ∣ Nat.card N := by
    change 3 ∣ Nat.card (normalizer ((c.imageSylow : Subgroup SL(2,k)) : Set SL(2,k)))
    rw [Matrix.SpecialLinearGroup.card_sylow_normalizer_even c.imageSylow,hk]
    decide
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := N) 3 hdiv
  have hao : orderOf (a : SL(2,k)) = 3 :=
    (orderOf_injective N.subtype N.subtype_injective a).trans ha
  have ha1 : (a : SL(2,k)) ≠ 1 := by
    intro he
    rw [he,orderOf_one] at hao
    contradiction
  obtain ⟨g,hg⟩ := c.onto (a : SL(2,k))
  have hgm : (g : G) ∈ M := c.normalizer_fixes_neighbor h g (hg.symm ▸ a.property)
  exact c.center_odd_fixed h (c.omega_eq_bot_of_central_neighbor h hB hS hactor hcentral)
    g (by rw [hg,hao]; decide) (by rwa [hg]) z hzZ
    ((congrArg Subtype.val (mem_center_iff.mp hz ⟨g,hgm⟩)).symm)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
