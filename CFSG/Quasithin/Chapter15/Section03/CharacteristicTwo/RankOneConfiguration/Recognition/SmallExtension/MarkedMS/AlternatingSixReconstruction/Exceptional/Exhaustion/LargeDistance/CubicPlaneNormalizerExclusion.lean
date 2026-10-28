module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRemainingRadicals
public import Theory.SpecificGroups.AlternatingSix.TripleCentralInvolution
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBorelThompson

/-!
# The cubic extension kernel cannot normalize a radical with an odd involution

If the full extension kernel E normalized the original radical R, then
[E,R] would be a two-group inside E and hence lie in Q=O₂(LR). Thus R fixes
the actual cubic center of the quasisimple component in LR/Q.

An element of R whose original symmetric image is an involution induces an
actual automorphism of square one on that component: its square lies in E,
whose image is exactly the component centralizer. The checked triple-cover
involution theorem makes this center-fixing automorphism inner. The same
component centralizer then puts the element in the component modulo Q, so
its symmetric image is even. This contradicts an odd involution in R's image.

Both the plane and Borel images contain the same conjugate pair swap. No
whole-core exhaustion, discarded cubic center, or assumed automorphism
order modulo inner automorphisms is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "Rg" => edge L R
local notation "Q" => pCore 2 M
local notation "π" => CubicAction.projection h e hz hk

private theorem center_map_equiv {A B : Type*} [Group A] [Group B]
    (f : A ≃* B) : (center A).map f.toMonoidHom = center B := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (centerCongr f ⟨a,ha⟩).property
  · intro hx
    exact ⟨f.symm x,(centerCongr f.symm ⟨x,hx⟩).property,f.apply_symm_apply x⟩

include h e hz hk in
/-- An odd involution in the literal radical image prevents its normalization
by the full cubic extension kernel. The induced component automorphism has
square one, not just square inner. -/
theorem extensionKernel_not_normalizes_of_odd_involution
    (r : M) (hr : r ∈ Rg) (hpow : (π r)^2 = 1)
    (hodd : π r ∉ alternatingGroup (Fin 6)) :
    ¬ extensionKernel h ≤ normalizer (Rg : Set M) := by
  intro hnorm
  let := h.relative_normal
  let := h.relative_core_quasisimple e
  let q := QuotientGroup.mk' Q
  let C := componentImage L R
  let : C.Normal := (inferInstance : (K).Normal).map q (QuotientGroup.mk'_surjective Q)
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv h.component)
  let f := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  let c : C ≃* (L ⧸ pCore 2 L) := (cComponentTwoCoreQuotientEquiv h.component).symm.trans
    (QuotientGroup.congr _ _ f (pCore_map_iso 2 f))
  let ce : (C ⧸ center C) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.congr _ _ c (center_map_equiv c)).trans
      (SmallMSPair.alternatingCentralQuotientEquiv e)
  have hc : Nat.card (center C) = 3 := (Nat.card_congr (centerCongr c).toEquiv).trans hz
  have hcommR : ⁅extensionKernel h,Rg⁆ ≤ Rg := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp hnorm
  have hcommE : ⁅extensionKernel h,Rg⁆ ≤ extensionKernel h :=
    le_normalizer_iff_commutator_le_left.mp le_normalizer_of_normal
  have hcommQ : ⁅extensionKernel h,Rg⁆ ≤ Q :=
    two_subgroup_le_core_of_le_extensionKernel h hz _
      (h.relative_radical.isPGroup.to_le hcommR) hcommE
  have hcomm : ⁅(extensionKernel h).map q,(Rg).map q⁆ = ⊥ := by
    rw [←map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [q,QuotientGroup.ker_mk'] using hcommQ
  have hfixC : (Rg).map q ≤ centralizer
      (((center C).map C.subtype : Subgroup (M ⧸ Q)) : Set (M ⧸ Q)) := by
    rw [←extensionKernel_image h]
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  let a : MulAut C := MulAut.conjNormal (q r)
  have hfix : ∀ z ∈ center C, a z = z := by
    intro z hzC
    apply Subtype.ext
    rw [show a = MulAut.conjNormal (q r) from rfl,MulAut.conjNormal_apply]
    have hh := hfixC (mem_map_of_mem q hr) (z : M ⧸ Q)
      (mem_map_of_mem C.subtype hzC)
    rw [←hh,mul_inv_cancel_right]
  have hrE : r^2 ∈ extensionKernel h := by
    rw [←CubicAction.projection_kernel h e hz hk]
    change π (r^2)=1
    rwa [map_pow]
  have hrC : q (r^2) ∈ centralizer (C : Set (M ⧸ Q)) := by
    rw [←extensionKernel_image_eq_centralizer h e]
    exact mem_map_of_mem q hrE
  have ha : a^2 = 1 := by
    change (MulAut.conjNormal (q r) : MulAut C)^2=1
    rw [←map_pow,←map_pow]
    exact MonoidHom.mem_ker.mp (by
      rw [MulAut.conjNormal_ker_eq_centralizer]
      exact hrC)
  obtain ⟨b,hb⟩ := AlternatingSix.TripleCentralInvolution.inner_of_fixes_center ce hc a ha hfix
  have hinner : q r ∈ (MulAut.innerSubgroup C).comap
      (MulAut.conjNormal : (M ⧸ Q) →* MulAut C) := ⟨b,hb.symm⟩
  have hcentral : centralizer (C : Set (M ⧸ Q)) ≤ C := by
    rw [←extensionKernel_image_eq_centralizer h e,extensionKernel_image h]
    exact (map_le_range _ _).trans_eq (range_subtype C)
  have hrComp : q r ∈ C := by
    rw [MulAut.conjNormal_comap_innerSubgroup,sup_of_le_left hcentral] at hinner
    exact hinner
  have hrKQ : r ∈ K ⊔ Q := by
    change r ∈ ((K).map q).comap q at hrComp
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk'] using hrComp
  have hQzero : (Q).map π = ⊥ := (Subgroup.map_eq_bot_iff _).mpr
    ((show Q ≤ extensionKernel h from le_sup_right).trans_eq
      (CubicAction.projection_kernel h e hz hk).symm)
  apply hodd
  have hh := mem_map_of_mem π hrKQ
  rwa [Subgroup.map_sup,hQzero,sup_bot_eq,CubicAction.component_image h e hz hk] at hh

include h e hz hk in
/-- A conjugate plane inside the actual radical image supplies the required
odd involution. This also applies when that image is Borel. -/
theorem extensionKernel_not_normalizes_of_plane_le (u : Equiv.Perm (Fin 6))
    (hR : D.map (MulAut.conj u).toMonoidHom ≤ (Rg).map π) :
    ¬ extensionKernel h ≤ normalizer (Rg : Set M) := by
  let t := MulAut.conj u swap01
  have ht : t ∈ (Rg).map π := hR (mem_map_of_mem (MulAut.conj u).toMonoidHom swap01_mem_D)
  obtain ⟨r,hr,hrt⟩ := ht
  have hpow : t^2=1 := by
    change (MulAut.conj u swap01)^2=1
    rw [←map_pow,show swap01^2=1 by decide,map_one]
  have hodd : t ∉ alternatingGroup (Fin 6) := by
    intro hh
    have hmem := (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem t hh u⁻¹
    have he : u⁻¹*t*(u⁻¹)⁻¹=swap01 := by
      dsimp only [t,MulAut.conj_apply]
      group
    rw [he] at hmem
    exact (show swap01 ∉ alternatingGroup (Fin 6) by decide) hmem
  exact extensionKernel_not_normalizes_of_odd_involution h e hz hk r hr
    (hrt ▸ hpow) (hrt ▸ hodd)

include h e hz hk in
/-- Both remaining original radical images contradict normalization by the
cubic extension kernel. -/
theorem extensionKernel_not_normalizes_remaining_radical (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    ¬ extensionKernel h ≤ normalizer (Rg : Set M) := by
  apply extensionKernel_not_normalizes_of_plane_le h e hz hk u
  rcases hR with hp | hb
  · exact hp.ge
  · rw [hb]
    exact map_mono BorelCalculation.plane_le_borel

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
