module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldInvolutionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DistinguishedSource
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.OrthogonalInvolutionCoordinates

/-!
# Actual full-cover coordinates for every inside involution

The absorbed quotient-action kernel lies in the block. An element of S outside
R=S∩L therefore induces an outer automorphism of L/O₂(L). Transport its literal
ambient conjugation to the block; when its center is nontrivial, the original
center-order theorem gives the full orthogonal-cover coordinate packet.

Source: Aschbacher–Smith, 2.4.12(2), used for the inside branch of 2.4.21, p.536.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_inside_outer_involution
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (a : G) (haS : a ∈ (d.S : Subgroup d.H).map d.H.subtype) (ha2 : a^2=1)
    (haR : a ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    let L := d.block.map d.H.subtype
    ∃ b : MulAut L, b^2=1 ∧ (∀l:L,(b l:G)=a*(l:G)*a⁻¹) ∧
      ¬∃g,quotientAut (pCore 2 L) b=MulAut.conj g := by
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let L := d.block.map d.H.subtype
  let aH : d.H := ⟨a,map_subtype_le _ haS⟩
  let b₀ := MulAut.conjNormal (H:=d.block) aH
  let eL : d.block ≃* L := equivMapOfInjective d.block d.H.subtype d.H.subtype_injective
  let b := MulAut.congr eL b₀
  let eK : (d.block ⧸ pCore 2 d.block) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)
  have hb₀ : b₀^2=1 := by
    change MulAut.conjNormal aH ^2=1
    rw [←map_pow]
    have h : aH^2=1 := Subtype.ext ha2
    rw [h,map_one]
  have hb : b^2=1 := by dsimp only [b]; rw [←map_pow,hb₀,map_one]
  have hquot : quotientAut (pCore 2 L) b =
      MulAut.congr eK (normalQuotientAction d.block (pCore 2 d.block) aH) := by
    apply MulEquiv.ext
    intro z
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) z
    obtain ⟨k,rfl⟩ := eL.surjective l
    rw [quotientAut_apply_mk]
    change QuotientGroup.mk' (pCore 2 L) (eL (b₀ (eL.symm (eL k)))) =
      eK (normalQuotientAction d.block (pCore 2 d.block) aH
        (eK.symm (eK (QuotientGroup.mk' (pCore 2 d.block) k))))
    rw [eL.symm_apply_apply,eK.symm_apply_apply,normalQuotientAction_apply_mk]
    rfl
  have hQL : pCore 2 d.H ≤ d.block := by
    intro u hu
    have hcore := (source_core_absorption d hG T hST hsingle hL hM hTM hunique).2
    have hu' : (u:G) ∈ (d.block.map d.H.subtype).pCoreIn 2 := by
      change (u:G)∈twoCore (d.block.map d.H.subtype)
      rw [hcore]
      exact mem_map_of_mem d.H.subtype hu
    exact (mem_map_iff_mem d.H.subtype_injective).mp (pCoreIn_le 2 _ hu')
  have ho : ¬∃g,quotientAut (pCore 2 L) b=MulAut.conj g := by
    rw [hquot,MulAut.congr_inner_iff]
    intro ⟨g,hg⟩
    have hm : aH ∈ (MulAut.innerSubgroup (d.block ⧸ pCore 2 d.block)).comap
        (normalQuotientAction d.block (pCore 2 d.block)) := by
      change normalQuotientAction d.block (pCore 2 d.block) aH∈MulAut.innerSubgroup _
      rw [hg]
      exact ⟨g,rfl⟩
    rw [normalQuotientAction_comap_inner,sup_eq_left.mpr
      ((source_block_quotient_action_kernel d hsingle hL).trans hQL)] at hm
    have haL : a∈L := mem_map_of_mem d.H.subtype hm
    have hR := (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).1
    exact haR (hR.symm ▸ (show a∈(d.S:Subgroup d.H).map d.H.subtype⊓L from ⟨haS,haL⟩))
  refine ⟨b,hb,?_,ho⟩
  intro l
  obtain ⟨k,rfl⟩ := eL.surjective l
  change (eL (b₀ (eL.symm (eL k))):G)=_
  rw [eL.symm_apply_apply]
  rfl
theorem source_inside_orthogonal_involution_coordinates
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (a : G) (haS : a ∈ (d.S : Subgroup d.H).map d.H.subtype) (ha2 : a^2=1)
    (haR : a ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    let L := d.block.map d.H.subtype
    ∃ b : MulAut L, b^2=1 ∧ (∀l:L,(b l:G)=a*(l:G)*a⁻¹) ∧
      (¬∃g,quotientAut (pCore 2 L) b=MulAut.conj g) ∧
      Nonempty (ChapterC.OrthogonalInvolutionCoordinates L n b) := by
  let L := d.block.map d.H.subtype
  obtain ⟨b,hb,hbval,ho⟩ := source_inside_outer_involution d hG T hST hsingle hL hM hTM hunique a haS ha2 haR
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hZcard : Nat.card (center L)=2^n := by
    have hc := (source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique).2.1
    rw [distinguishedZ_of_center_ne_bot d hz,card_map_of_injective L.subtype_injective] at hc
    exact hc
  exact ⟨b,hb,hbval,ho,hK.orthogonal_involution_coordinates
    (source_block_core_eq_module d hG T hST hsingle) hZcard b hb ho⟩

end CFSG.Quasithin.Chapter2.LinearShadows.Single
