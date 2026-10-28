module
public import Theory.SpecificGroups.PSL2.RootInvolutionFixedCard
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldInvolutionCoreSource

/-!
# The fixed-point count on the original root quotient

The literal quotient R/O₂(H) maps isomorphically onto a Sylow two-subgroup
of L/O₂(L). Conjugation by the chosen Hall-torus involution intertwines these
maps and acts outerly on the whole block quotient. The binary PSL₂ Sylow
calculation therefore gives the square-root fixed count on R/O₂(H) itself.

This discharges the second fixed-cardinality premise in Aschbacher–Smith,
Lemma 2.4.12(2), printed p.532.
-/

public section
noncomputable section
open Subgroup

namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_field_involution_sylow_quotient_fixed_card
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
    let : N.Normal := source_field_core_normal d
    let α := (R.normalizerMonoidHom ⟨s,source_field_actor_normalizes_thompson d s hs.1⟩).toMonoidHom
    let hN : ∀ x ∈ N, α x ∈ N := source_field_actor_preserves_core d s hs.1
    Nat.card ((QuotientGroup.map N N α hN).eqLocus (MonoidHom.id (R ⧸ N))) ^ 2 = Nat.card (R ⧸ N) := by
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let Q := twoCore d.H
  let N := Q.subgroupOf R
  let : N.Normal := source_field_core_normal d
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
  have hbval (l : L) : (b l:G)=s*(l:G)*s⁻¹ := by
    obtain ⟨k,rfl⟩ := eL.surjective l
    change (eL (a (eL.symm (eL k))):G)=_
    rw [eL.symm_apply_apply]
    rfl
  obtain ⟨P₀,hP₀⟩ := (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).2.2.1
  let eR : R ≃* P₀ := (MulEquiv.subgroupCongr hP₀.symm).trans
    (equivMapOfInjective (P₀ : Subgroup L) L.subtype L.subtype_injective).symm
  let ψ : R →* L := (P₀ : Subgroup L).subtype.comp eR.toMonoidHom
  have hψval (r : R) : (ψ r : G) = (r:G) := by
    have hh := (equivMapOfInjective (P₀ : Subgroup L) L.subtype L.subtype_injective).apply_symm_apply
      (MulEquiv.subgroupCongr hP₀.symm r)
    exact congrArg Subtype.val hh
  let q := QuotientGroup.mk' (pCore 2 L)
  let K := L ⧸ pCore 2 L
  let P : Sylow 2 K := P₀.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let φ : R →* K := q.comp ψ
  have hψrange : ψ.range = P₀ := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr eR.surjective,←MonoidHom.range_eq_map,range_subtype]
  have hφrange : φ.range = (P : Subgroup K) := by
    change (q.comp ψ).range = (P₀ : Subgroup L).map q
    rw [MonoidHom.range_comp,hψrange]
  have hcore : (pCore 2 L).map L.subtype = Q :=
    (source_core_absorption d hG T hST hsingle hL hM hTM hunique).2
  have hker : φ.ker = N := by
    ext r
    change q (ψ r) = 1 ↔ (r:G) ∈ Q
    rw [show q (ψ r) = 1 ↔ ψ r ∈ pCore 2 L from QuotientGroup.eq_one_iff _]
    have hh := (mem_map_iff_mem L.subtype_injective :
      ((ψ r:L):G) ∈ (pCore 2 L).map L.subtype ↔ ψ r ∈ pCore 2 L)
    rw [hcore] at hh
    change (ψ r : G) ∈ Q ↔ ψ r ∈ pCore 2 L at hh
    rw [hψval] at hh
    exact hh.symm
  let eRQ : (R ⧸ N) ≃* P := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hφrange))
  have heval (r : R) : (eRQ (QuotientGroup.mk' N r) : K) = φ r := rfl
  let γ := quotientAut (pCore 2 L) b
  have hψeq (r : R) : ψ (α r) = b (ψ r) := by
    apply L.subtype_injective
    change (ψ (α r):G)=(b (ψ r):G)
    rw [hψval,hbval,hψval]
    rfl
  have hφeq (r : R) : φ (α r) = γ (φ r) := by
    change q (ψ (α r)) = quotientAut (pCore 2 L) b (q (ψ r))
    rw [quotientAut_apply_mk,hψeq]
  have hcomp : γ.toMonoidHom.comp φ = φ.comp α := by ext r; exact (hφeq r).symm
  have hγP : (P : Subgroup K).map γ.toMonoidHom = P := by
    rw [←hφrange,←MonoidHom.range_comp,hcomp,MonoidHom.range_comp]
    have hαsur : Function.Surjective α := (R.normalizerMonoidHom
      ⟨s,source_field_actor_normalizes_thompson d s hs.1⟩).surjective
    rw [MonoidHom.range_eq_top.mpr hαsur,←MonoidHom.range_eq_map]
  have hγ : γ^2=1 := by dsimp only [γ]; rw [←map_pow,hb,map_one]
  have hK := hL.of_mulEquiv eL
  obtain ⟨F,_,_,hF,_,ρ,⟨m⟩,_⟩ := hK.2.2
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let e : K ≃* Theory.PSL2.Group F := m.quotientIso.trans (Theory.PSL2.sl2QuotientEquiv F)
  have hc := Theory.PSL2.RootSemilinear.sylow_fixed_card_sq_of_equiv e P γ hγP hγ ho
  let β := QuotientGroup.map N N α hN
  have heβ (z : R ⧸ N) : γ (eRQ z : K) = (eRQ (β z) : K) := by
    obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective N z
    rw [heval]
    change γ (φ r) = (eRQ (QuotientGroup.mk' N (α r)):K)
    rw [heval,hφeq]
  let ef : β.eqLocus (MonoidHom.id (R ⧸ N)) ≃ {u : P // γ u = u} :=
    eRQ.toEquiv.subtypeEquiv (fun z => by
      change β z = z ↔ γ (eRQ z:K) = (eRQ z:K)
      constructor
      · intro h
        rw [heβ,h]
      · intro h
        apply eRQ.injective
        apply Subtype.ext
        exact (heβ z).symm.trans h)
  change Nat.card (β.eqLocus (MonoidHom.id (R ⧸ N))) ^ 2 = Nat.card (R ⧸ N)
  rw [Nat.card_congr ef,Nat.card_congr eRQ.toEquiv]
  exact hc
end CFSG.Quasithin.Chapter2.LinearShadows.Single
