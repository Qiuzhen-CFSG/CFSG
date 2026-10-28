module
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.Containing
public import Theory.SpecificGroups.SL2.PrimeFieldOddSubgroups
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.GroupTheory.PrimeRankCyclicSylow
/-!
# Quasisimplicity above a local A₇ section

A noncentral Fitting subgroup would give a prime-field SL₂ quotient. The
perfect A₇ section survives its solvable kernel and has three-rank at least
two, whereas every odd-prime Sylow of that SL₂ group is cyclic. The resulting
quasisimplicity transports to the literal K/O₂(K) in the local consumer.
The simple-carrier inspection is a further obligation.

Source: Aschbacher–Smith A.3.6, A.3.12 and 1.2.8, pp.43–48,506–507.
-/
public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02.LocalModels
universe u
variable {G H : Type u} [Group G] [Group H] [Finite G] [Finite H]

private theorem section_map (B : Subgroup G) [Group.IsPerfect B]
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    (f : G →* H) [Group.IsSolvable f.ker] :
    Nonempty (((B.map f) ⧸ pCore 2 (B.map f)) ≃* alternatingGroup (Fin 7)) := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := h.some.isSimpleGroup
  let g := f.subgroupMap B
  let : Group.IsSolvable g.ker := by
    change Group.IsSolvable (f.subgroupMap B).ker
    rw [Subgroup.ker_subgroupMap]
    exact Group.isSolvable_of_isSolvable_injective
      (f := B.subtype.subgroupComap f.ker) (fun a b he => Subtype.ext (Subtype.ext
        (congrArg (fun x : f.ker => (x : G)) he)))
  exact ⟨(PerfectCoreTwoExtension.solvableKernelQuotientEquiv g
    (f.subgroupMap_surjective B)).symm.trans h.some⟩

omit [Group H] [Finite H] in
private theorem section_threeRank {B : Subgroup G}
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) :
    2 ≤ primeRank 3 B := by
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 B) pCore_isPGroup,
    primeRank_congr 3 h.some]
  exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)

omit [Group H] [Finite H] in
/-- The actual containing component of a local A₇ section is quasisimple.
The noncentral-Fitting branch has an SL₂ prime-field quotient of three-rank at most one. -/
theorem alternatingSeven_containing_quasisimple
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (hsection : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) :
    IsQuasisimple K := by
  have hfit : fittingSubgroup K ≤ center K := by
    by_contra hn
    obtain ⟨p,hp,_,⟨e⟩⟩ := NoncentralFitting.primeSL2FittingQuotient_of_noncentral
      ChapterA.RankActions.primeSL2CoverRigidity hG hO hK hn
    let : Fact p.Prime := ⟨hp⟩
    let q := QuotientGroup.mk' (fittingSubgroup K)
    let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
    let := Exceptional.local_perfect (local_restrict hB hBK)
    have hsmall : Nonempty (((B.subgroupOf K) ⧸ pCore 2 (B.subgroupOf K)) ≃*
        alternatingGroup (Fin 7)) :=
      ⟨(QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBK)
        (pCore_map_iso 2 (subgroupOfEquivOfLe hBK))).trans hsection.some⟩
    have hmap := section_map (B.subgroupOf K) hsmall q
    have hr := (section_threeRank hmap).trans (primeRank_subgroup_le 3 _)
    rw [primeRank_congr 3 e] at hr
    let P : Sylow 3 SL(2, ZMod p) := Sylow.nonempty.some
    have hc : IsCyclic P :=
      Matrix.SpecialLinearGroup.isCyclic_of_odd_pGroup_injective_primeField
        P.isPGroup' (by decide) (P : Subgroup SL(2, ZMod p)).subtype Subtype.val_injective
    have hb := P.primeRank_le_one_of_isCyclic hc
    omega
  have hs : solvableRadical K = center K := by
    apply le_antisymm (solvableRadical_le_center_of_fitting_le_center hfit)
    exact le_solvableRadical (center K) inferInstance
      (Group.isSolvable_of_comm (fun a b => Subtype.ext
        (mem_center_iff.mp a.property b).symm))
  let := hK.perfect
  let := hK.isSimpleGroup_quotient_solvableRadical
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hs).symm.isSimpleGroup⟩
end CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents

namespace CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Apply the A₇ containing-component argument to the literal quotient of any
local overcomponent in a simple QTKE group. -/
theorem alternatingSeven_local_overcomponent_quotient_quasisimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {X K : Subgroup G}
    (hX : X ∈ L G (T : Subgroup G))
    (hK : K ∈ L G (T : Subgroup G)) (hXK : X ≤ K)
    (h : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7))) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  let H := K ⊔ (T : Subgroup G)
  have hXH : X ≤ H := hXK.trans le_sup_left
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hx : X.subgroupOf H ∈ L H (S : Subgroup H) :=
    (mem_LIn_iff_subgroupOf le_sup_right hXH).mp ⟨hXH,hX⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hbar : (X.subgroupOf H).map q ∈ localCComponents Sbar :=
    mem_L_map_twoCore_mem_localCComponents hx
  have hq := uniqueness_local_quotient_sqtk hG hK.2.2
  let eX := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hXH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hXH))
  have hk : IsPGroup 2 (q.subgroupMap (X.subgroupOf H)).ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eB := MonoidHom.quotientPCoreEquivOfSurjective
    (q.subgroupMap (X.subgroupOf H)) (q.subgroupMap_surjective _) hk
  have hm : Nonempty ((((X.subgroupOf H).map q) ⧸ pCore 2 ((X.subgroupOf H).map q)) ≃*
      alternatingGroup (Fin 7)) := ⟨eB.symm.trans (eX.trans h.some)⟩
  let := pCore_isNilpotent (p := 2) (G := H)
  let : IsQuasisimple ((K.subgroupOf H).map q) := alternatingSeven_containing_quasisimple
    hq (pCore_quotient_pCore_eq_bot 2) Sbar hbar (hK.1.map_quotient _)
    (map_mono (comap_mono hXK)) hm
  let eK := QuotientGroup.congr _ _ (subgroupOfEquivOfLe (show K ≤ H from le_sup_left))
    (pCore_map_iso 2 (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)))
  exact IsQuasisimple.of_mulEquiv ((cComponentTwoCoreQuotientEquiv hK.1).symm.trans eK)
end CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents
