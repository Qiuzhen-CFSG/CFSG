module
public import Stellmacher.SectionNine.DistanceOneChiefKernel
public import Stellmacher.SectionNine.DistanceOneFaithfulProducer
public import Theory.GroupTheory.MaximalSylowKernel
public import Theory.GroupTheory.ElementaryOddSylowUniqueMaximal

/-!
# The chief quotient has the same kernel as the initial-center action

In the noncentral chief branch at critical distance one, the canonical
chief quotient and the initial vertex center have exactly the same
stabilizer action kernel. Both graph and ambient groups remain explicit.

The preceding kernel theorem lets the chief action factor through the
faithful center quotient. The actual extraction supplies its order-nine
elementary odd core, a Sylow supplement, and unique maximal overgroup.
Coprime invariant-complement theory makes that Sylow subgroup maximal.
The generic maximal-Sylow kernel theorem makes the factorized action
injective: the initial residual has nontrivial odd image on the chief
quotient. Thus the original two kernels coincide.

This supplies the faithful quotient in Stellmacher (9.1)(10), Journal of
Algebra190 (1997), p.47. It uses the proved witness setup and actual
canonical chief action, and assumes neither the chief-module order nor
the initial core equality. The order-sixteen calculation and subsequent
nonisomorphic-module argument remain separate.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem distance_one_chief_action_kernel
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) :
    (distanceOneChiefAction ctx.toLocalContext).ker =
      (Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G)).subgroupOf
        (stabilizer ctx.Γ ctx.criticalPath.a) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let Za := ZAt Γ cp.a
  let action : P →* MulAut (DistanceOneChiefQuotient ctx.toLocalContext) :=
    distanceOneChiefAction ctx.toLocalContext
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ : IsElementaryAbelian 2 Za := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hfirst
  have hZaP : Za ≤ P := by
    change z Γ cp.a ≤ stabilizer Γ cp.a
    rw [z, Γ.zAt_def]
    apply sSup_le
    rintro center ⟨sylow, rfl⟩
    exact (omegaOneCenter_le_centerAmbient _).trans
      ((Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _))
  obtain ⟨w⟩ := exists_quotientModuleWitness P Za hZaP (stabilizer_le_normalizer_z Γ cp.a)
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Za w.action
  obtain ⟨hsetup, _, hoddcard, ⟨R, hgen, huniq⟩, X, hX, hXcard⟩ :=
    distance_one_faithful_recognition_setup ctx hb branch.extraction w
  let _ : (SectionOne.oddCore w.X).Normal := pPrimeCore_normal
  let _ : IsElementaryAbelian 3 (SectionOne.oddCore w.X) :=
    SectionOne.nineCore_elementary_of_elementary_four hsetup hoddcard X hX hXcard
  have hRmax : IsCoatom (R : Subgroup w.X) := by
    apply Theory.GroupTheory.sylow_isCoatom_of_elementary_odd_supplement_unique_maximal
      (SectionOne.oddCore w.X) R hgen
    obtain ⟨M, hM, hRM, huniqM⟩ := (uniqueMaximalContaining_top_iff _).mp huniq
    exact ⟨M, ⟨hM, hRM⟩, fun N hN => huniqM N hN.1 hN.2⟩
  have hker : w.projection.ker ≤ action.ker := by
    rw [w.kernel_eq]
    simp only [Subgroup.inf_subgroupOf_left]
    exact (Subgroup.map_eq_bot_iff _).mp
      (distance_one_chief_initial_center_kernel_eq_bot ctx hb hfaith branch)
  let equiv : P ⧸ w.projection.ker ≃* w.X :=
    QuotientGroup.liftEquiv w.projection.ker w.surjective rfl
  let lift := QuotientGroup.lift w.projection.ker action hker
  let bar := lift.comp equiv.symm.toMonoidHom
  have hcomp : bar.comp w.projection = action := by
    apply MonoidHom.ext
    intro element
    change lift (equiv.symm (w.projection element)) = action element
    have hm : equiv (QuotientGroup.mk' w.projection.ker element) = w.projection element :=
      QuotientGroup.liftEquiv_mk _ w.surjective rfl element
    rw [← hm, equiv.symm_apply_apply]
    rfl
  let F := ((e Γ cp.a).subgroupOf P).map w.projection
  have hFle : F ≤ SectionOne.oddCore w.X := by
    have hEsub : (e Γ cp.a).subgroupOf P = twoResidualSubgroup P := by
      rw [CosetGraphContext.e, Γ.twoResidualAt_def]
      change ((twoResidualSubgroup P).map P.subtype).subgroupOf P = _
      exact Subgroup.comap_map_eq_self (by simp)
    change ((e Γ cp.a).subgroupOf P).map w.projection ≤ _
    rw [hEsub, SectionThree.twoResidualSubgroup_eq_hktPResidual']
    simpa only [SectionThree.twoResidualAmbient_top_eq_hktPResidual] using
      SectionEight.local_quotient_residual_image_le_oddCore ctx.sectionSeven Γ cp w
  have hFodd : Odd (Nat.card F) := by
    have hcoreodd : Odd (Nat.card (SectionOne.oddCore w.X)) := by rw [hoddcard]; decide
    exact hcoreodd.of_dvd_nat (Subgroup.card_dvd_of_le hFle)
  have hFmap : F.map bar = ((e Γ cp.a).subgroupOf P).map action := by
    rw [Subgroup.map_map, hcomp]
  have hFinj := bar.injective_of_coatom_sylow_of_nontrivial_odd_image R hRmax
    hsetup.twoCore_eq_bot F hFodd (by
      rw [hFmap]
      exact distance_one_chief_residual_map_ne_bot ctx branch)
  have heq : action.ker = w.projection.ker := by
    rw [← hcomp]
    exact MonoidHom.ker_comp_of_injective _ _ hFinj
  change action.ker = (Subgroup.centralizer (Za : Set G)).subgroupOf P
  rw [heq, w.kernel_eq]
  simp only [Subgroup.inf_subgroupOf_left]
end Stellmacher.SectionNine
