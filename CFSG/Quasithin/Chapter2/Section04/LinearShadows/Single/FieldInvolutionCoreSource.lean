module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.FieldInvolution
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldInvolutionQuotientSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldInvolutionFusionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ModelSource.Geometry

/-!
# The fixed-point count on the original two-core

The Hall-torus involution acts outerly on the actual block quotient. The
source center dichotomy puts its two-core in the natural-plane or full
orthogonal-cover case. Their marked semilinear actions give the square-root
fixed count, transported to the exact core subgroup of R=J(S).

This discharges the first fixed-cardinality premise in the original
involution-coset fusion argument of Aschbacher–Smith, Lemma 2.4.12(2), p.532.
-/

public section
noncomputable section
open Subgroup Representation

namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_field_involution_core_fixed_card
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n)
    (s : G) (hs : s ∈ (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G))
    (hs2 : orderOf s = 2) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let N := (twoCore d.H).subgroupOf R
    let α := (R.normalizerMonoidHom ⟨s,source_field_actor_normalizes_thompson d s hs.1⟩).toMonoidHom
    let hN : ∀ x ∈ N, α x ∈ N := source_field_actor_preserves_core d s hs.1
    Nat.card ((α.restrict hN).eqLocus (MonoidHom.id N)) ^ 2 = Nat.card N := by
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let Q := twoCore d.H
  let N := Q.subgroupOf R
  let α := (R.normalizerMonoidHom ⟨s,source_field_actor_normalizes_thompson d s hs.1⟩).toMonoidHom
  let hN : ∀ x ∈ N, α x ∈ N := source_field_actor_preserves_core d s hs.1
  let f : ((d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G) : Subgroup G) := ⟨s,hs⟩
  let fH : d.H := inclusion (inf_le_left.trans (map_subtype_le _)) f
  let a := MulAut.conjNormal (H := d.block) fH
  let eL : d.block ≃* L := equivMapOfInjective d.block d.H.subtype d.H.subtype_injective
  let b := MulAut.congr eL a
  let eK : (d.block ⧸ pCore 2 d.block) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)
  have hs1 : s^2=1 := by simpa only [hs2] using pow_orderOf_eq_one s
  have ha : a^2=1 := by
    change MulAut.conjNormal fH ^ 2 = 1
    rw [←map_pow]
    have hfH : fH^2=1 := Subtype.ext hs1
    rw [hfH,map_one]
  have hb : b^2=1 := by dsimp only [b]; rw [←map_pow,ha,map_one]
  have hquot : quotientAut (pCore 2 L) b =
      MulAut.congr eK (normalQuotientAction d.block (pCore 2 d.block) fH) := by
    apply MulEquiv.ext
    intro z
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) z
    obtain ⟨k,rfl⟩ := eL.surjective l
    rw [quotientAut_apply_mk]
    change QuotientGroup.mk' (pCore 2 L) (eL (a (eL.symm (eL k)))) =
      eK (normalQuotientAction d.block (pCore 2 d.block) fH
        (eK.symm (eK (QuotientGroup.mk' (pCore 2 d.block) k))))
    rw [eL.symm_apply_apply,eK.symm_apply_apply,normalQuotientAction_apply_mk]
    rfl
  have ho : ¬ ∃ g, quotientAut (pCore 2 L) b = MulAut.conj g := by
    rw [hquot,MulAut.congr_inner_iff]
    intro ⟨g,hg⟩
    exact source_field_actor_not_inner d hG T hST hsingle hL hM hTM hunique c f
      (fun hf => by have he : s=1 := congrArg Subtype.val hf; simp [he] at hs2)
      (hg ▸ ⟨g,rfl⟩)
  have hK := hL.of_mulEquiv eL
  have hc : Nat.card (((MulAut.characteristic (pCore 2 L) b).toMonoidHom).eqLocus
      (MonoidHom.id (pCore 2 L))) ^ 2 = Nat.card (pCore 2 L) := by
    obtain ⟨_,D,_,_,_,x,_,_,_,hZ⟩ := source_center_torus_and_splitting d hG T hST hsingle hL hM hTM hunique
    rcases hZ with hz | ⟨hz,_,_⟩
    · exact hK.centerless_core_fixed_card (source_block_core_eq_module d hG T hST hsingle) hz b hb ho
    · exact hK.full_cover_core_fixed_card (source_block_core_eq_module d hG T hST hsingle) hz b hb ho
  have hQR : Q ≤ R := le_sSup (d.core_source hG T hST).2.2
  have hcore : (pCore 2 L).map L.subtype = Q :=
    (source_core_absorption d hG T hST hsingle hL hM hTM hunique).2
  let eQ : pCore 2 L ≃* Q :=
    (equivMapOfInjective (pCore 2 L) L.subtype L.subtype_injective).trans (MulEquiv.subgroupCongr hcore)
  let eN : N ≃* pCore 2 L := (subgroupOfEquivOfLe hQR).trans eQ.symm
  have heQ (u : pCore 2 L) : (eQ u : G) = ((u:L):G) := rfl
  have heN (u : N) : ((eN u:L):G) = ((u:R):G) := by
    rw [←heQ]
    change (eQ (eQ.symm _):G)=_
    rw [eQ.apply_symm_apply]
    rfl
  have hbval (l : L) : (b l:G)=s*(l:G)*s⁻¹ := by
    obtain ⟨k,rfl⟩ := eL.surjective l
    change (eL (a (eL.symm (eL k))):G)=_
    rw [eL.symm_apply_apply]
    rfl
  let κ := MulAut.characteristic (pCore 2 L) b
  have he (u : N) : eN ((α.restrict hN) u) = κ (eN u) := by
    apply (pCore 2 L).subtype_injective
    apply L.subtype_injective
    change ((eN ((α.restrict hN) u) : L) : G) = ((κ (eN u) : L) : G)
    rw [heN]
    change s * ((u:R):G) * s⁻¹ = (b (eN u):G)
    rw [hbval,heN]
  let ef : (α.restrict hN).eqLocus (MonoidHom.id N) ≃ κ.toMonoidHom.eqLocus (MonoidHom.id _) :=
    eN.toEquiv.subtypeEquiv (fun u => by
      change (α.restrict hN) u = u ↔ κ (eN u) = eN u
      rw [←he]
      exact eN.injective.eq_iff.symm)
  change Nat.card ((α.restrict hN).eqLocus (MonoidHom.id N)) ^ 2 = Nat.card N
  rw [Nat.card_congr ef,Nat.card_congr eN.toEquiv]
  exact hc
end CFSG.Quasithin.Chapter2.LinearShadows.Single
