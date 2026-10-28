module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourHyperplaneFullReduced
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Preliminaries

/-!
# Odd centralizer images from the actual hyperplane Sylow kernel

If every hyperplane has the same centralizer in T as the whole module,
conjugate a Sylow subgroup of C_M(U) into T using N_G(B). Its conjugate
fixes the conjugate hyperplane and therefore B. The Sylow image on B is
trivial, so the complete induced centralizer image has odd order.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.FourHyperplaneGeometry
open ChapterE ChapterE.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M B : Subgroup G}

/-- Equality of the literal Sylow kernels on all hyperplanes forces odd
order of the complete local centralizer image on each nonzero hyperplane. -/
theorem odd_centralizer_image_of_hyperplane_sylow_kernel
    (hE : HypothesisE61 KnownSimple.IsKnownSimple T M B)
    (hkernel : ∀ U : Subgroup G, U ≤ B → subgroupCorank B U = 1 →
      (T : Subgroup G) ⊓ centralizer (U : Set G) =
        (T : Subgroup G) ⊓ centralizer (B : Set G))
    (U : Subgroup G) (hUB : U ≤ B) (hU : U ≠ ⊥) (hcor : subgroupCorank B U = 1) :
    Odd (Nat.card (inducedAutomizer B (M ⊓ centralizer (U : Set G)))) := by
  let H := M ⊓ centralizer (U : Set G)
  let N := normalizer (B : Set G)
  have hHN : H ≤ N := hE.localCentralizer_le_normalizer hU hUB
  let I := inducedAutomizer B H
  let f : H →* I := {
    toFun c := ⟨B.normalizerMonoidHom.rangeRestrict ⟨c,hHN c.property⟩,
      ⟨⟨c,hHN c.property⟩,c.property,rfl⟩⟩
    map_one' := by apply Subtype.ext; exact map_one B.normalizerMonoidHom.rangeRestrict
    map_mul' a b := by
      apply Subtype.ext
      exact map_mul B.normalizerMonoidHom.rangeRestrict
        ⟨a,hHN a.property⟩ ⟨b,hHN b.property⟩ }
  have hf : Function.Surjective f := by
    rintro ⟨x,n,hn,rfl⟩
    exact ⟨⟨n,hn⟩,rfl⟩
  let P : Sylow 2 H := Classical.arbitrary _
  let R := (P : Subgroup H).map (inclusion hHN)
  obtain ⟨Q,hRQ⟩ := (P.isPGroup'.map (inclusion hHN)).exists_le_sylow
  let S := T.subtype hE.sylow_le_normalizer
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq N Q S
  have hQ : (Q : Subgroup N).map (MulAut.conj a).toMonoidHom = (S : Subgroup N) := by
    change ((a • Q : Sylow 2 N) : Subgroup N) = _
    rw [ha]
  let e := MulAut.conj (a : G)
  let W := U.map e.toMonoidHom
  have hWB : W ≤ B :=
    (map_mono hUB).trans_eq (mem_normalizer_iff_map_conj_eq.mp a.property)
  have hWcor : subgroupCorank B W = 1 :=
    (Hyperplanes.corank_conjugate B U a a.property).trans hcor
  have hPcentral (p : P) : ((p : H) : G) ∈ centralizer (B : Set G) := by
    have hpQ : inclusion hHN (p : H) ∈ (Q : Subgroup N) :=
      hRQ (mem_map_of_mem (inclusion hHN) p.property)
    have hpS : (MulAut.conj a) (inclusion hHN (p : H)) ∈ (S : Subgroup N) :=
      hQ ▸ mem_map_of_mem (MulAut.conj a).toMonoidHom hpQ
    have hpT : e ((p : H) : G) ∈ (T : Subgroup G) := hpS
    have hpW : e ((p : H) : G) ∈ centralizer (W : Set G) :=
      map_centralizer_le_centralizer_image (U : Set G) e.toMonoidHom
        (mem_map_of_mem e.toMonoidHom (p.val.property.2))
    have hc : e ((p : H) : G) ∈ centralizer (B : Set G) :=
      ((hkernel W hWB hWcor) ▸ (show e ((p : H) : G) ∈
        (T : Subgroup G) ⊓ centralizer (W : Set G) from ⟨hpT,hpW⟩)).2
    intro b hb
    apply e.injective
    rw [map_mul,map_mul]
    exact hc (e b) ((mem_normalizer_iff.mp a.property b).mp hb)
  have hzero : (P : Subgroup H).map f = ⊥ := by
    apply bot_unique
    rintro x ⟨p,hp,rfl⟩
    apply mem_bot.mpr
    apply Subtype.ext
    apply Subtype.ext
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    change (p : G)*(b : G)*(p : G)⁻¹ = (b : G)
    rw [←hPcentral ⟨p,hp⟩ b b.property,mul_inv_cancel_right]
  have hodd := (P.mapSurjective hf).not_dvd_index
  change ¬ 2 ∣ ((P : Subgroup H).map f).index at hodd
  rw [hzero,index_bot] at hodd
  exact Nat.not_even_iff_odd.mp (fun he => hodd (even_iff_two_dvd.mp he))

/-- The source odd-centralizer condition is a consequence of the actual
Sylow hyperplane kernel, rather than an additional obstruction premise. -/
theorem oddCentralizerCondition_of_hyperplane_sylow_kernel
    (hE : HypothesisE61 KnownSimple.IsKnownSimple T M B)
    (hkernel : ∀ U : Subgroup G, U ≤ B → subgroupCorank B U = 1 →
      (T : Subgroup G) ⊓ centralizer (U : Set G) =
        (T : Subgroup G) ⊓ centralizer (B : Set G))
    (U : Subgroup G) (hUB : U ≤ B) (hU : U ≠ ⊥) (hcor : subgroupCorank B U = 1) :
    oddCentralizerCondition M B U :=
  oddCentralizerCondition_of_odd_image (hE.localCentralizer_le_normalizer hU hUB)
    (odd_centralizer_image_of_hyperplane_sylow_kernel hE hkernel U hUB hU hcor)

end CFSG.Quasithin.Chapter6.Source.FourHyperplaneGeometry
