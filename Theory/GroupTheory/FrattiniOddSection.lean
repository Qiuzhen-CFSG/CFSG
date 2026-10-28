module
public import Theory.GroupTheory.OddLineHyperplaneQuotient
/-!
# The odd section in a Frattini normalizer

The selected odd prime line and fixing actor hyperplane give an actual
self-centralizing minimal normal section in N_H(Q)/(I ∩ N_H(Q)). The proof
transfers the line through the explicit Frattini quotient isomorphism,
including failure of coverage by the original normalizer candidate.

Source: GLS, Number 2, G.26.18(a), printed pp.152–153.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G K : Type*} [Group G] [Group K]

/-- Transfer a self-centralizing prime section through the specified quotient
isomorphism, preserving the original covering candidate. -/
theorem prime_section_equiv_transfer (e : G ≃* K) (Y U : Subgroup K) (V : Subgroup G)
    [Y.Normal] {r : ℕ} (hc : Nat.card Y = r)
    (hCY : centralizer (Y : Set K) ≤ Y)
    (hmin : ∀ Z : Subgroup K, Z ≤ Y → Z = ⊥ ∨ Z = Y)
    (hout : ¬ Y ≤ U) (hVU : V.map e.toMonoidHom ≤ U) :
    ∃ Z : Subgroup G, Z.Normal ∧ Nat.card Z = r ∧
      centralizer (Z : Set G) ≤ Z ∧
      (∀ W : Subgroup G, W ≤ Z → W = ⊥ ∨ W = Z) ∧ ¬ Z ≤ V := by
  let Z := Y.comap e.toMonoidHom
  have hm : Z.map e.toMonoidHom = Y := map_comap_eq_self_of_surjective e.surjective Y
  refine ⟨Z,inferInstance,?_,?_,?_,?_⟩
  · rw [←card_map_of_injective (f := e.toMonoidHom) e.injective,hm,hc]
  · intro x hx
    apply hCY
    intro y hy
    have hyZ : e.symm y ∈ Z := by change e (e.symm y) ∈ Y; rw [e.apply_symm_apply]; exact hy
    have hh := congrArg e (hx (e.symm y) hyZ)
    change y * e x = e x * y
    simpa only [map_mul,e.apply_symm_apply] using hh
  · intro W hW
    rcases hmin (W.map e.toMonoidHom) (hm ▸ map_mono hW) with hz | he
    · exact Or.inl ((map_injective (f := e.toMonoidHom) e.injective) (by simpa only [Subgroup.map_bot] using hz))
    · exact Or.inr ((map_injective e.injective) (he.trans hm.symm))
  · intro hh
    exact hout (hm ▸ (map_mono hh).trans hVU)

/-- Passing the fixing hyperplane through the original quotient does not
change its index inside the actor. -/
theorem actor_hyperplane_image_index (q : G →* K) (A B : Subgroup G)
    (hBA : B ≤ A) (hker : A ⊓ q.ker ≤ B) :
    (B.map q).relIndex (A.map q) = B.relIndex A := by
  have hi : (B ⊔ q.ker) ⊓ A = B := by
    refine le_antisymm ?_ (le_inf le_sup_left hBA)
    rintro x ⟨hx,hxA⟩
    obtain ⟨b,hb,k,hk,rfl⟩ := mem_sup_of_normal_right.mp hx
    have hkA : k ∈ A := by
      have hh := A.mul_mem (A.inv_mem (hBA hb)) hxA
      simpa only [inv_mul_cancel_left] using hh
    exact B.mul_mem hb (hker ⟨hkA,hk⟩)
  rw [←relIndex_comap (B.map q) q A,comap_map_eq,←inf_relIndex_right,hi]

variable [Finite G]
/-- The odd section in the actual Frattini normalizer quotient. All maps
come from the same original normal kernel and selected hyperplane. -/
theorem hyperplane_frattini_odd_section (P : Sylow 2 G) (S A B V : Subgroup G)
    [S.Normal] [IsElementaryAbelian 2 A]
    (hAP : A ≤ (P : Subgroup G)) (hBA : B ≤ A) (hi : B.relIndex A = 2)
    (hASB : A ⊓ S ≤ B) (hBV : B ≤ V)
    (D : Subgroup (G ⧸ S)) {r : ℕ} [Fact r.Prime] (ho : Odd r) (hc : Nat.card D = r)
    (hAD : A.map (QuotientGroup.mk' S) ≤ normalizer (D : Set (G ⧸ S)))
    (hm : ⁅D,A.map (QuotientGroup.mk' S)⁆ = D)
    (hDB : D ≤ centralizer (B.map (QuotientGroup.mk' S) : Set (G ⧸ S)))
    (hout : ¬ D ≤ V.map (QuotientGroup.mk' S)) :
    let H := (D ⊔ A.map (QuotientGroup.mk' S)).comap (QuotientGroup.mk' S)
    let I := S ⊔ B
    let Q := ((P : Subgroup G) ⊓ S) ⊔ B
    let N := H ⊓ normalizer (Q : Set G)
    ∃ n : (I.subgroupOf N).Normal, letI := n
      ∃ Y : Subgroup (N ⧸ I.subgroupOf N), Y.Normal ∧ Nat.card Y = r ∧
        centralizer (Y : Set (N ⧸ I.subgroupOf N)) ≤ Y ∧
        (∀ Z : Subgroup (N ⧸ I.subgroupOf N), Z ≤ Y → Z = ⊥ ∨ Z = Y) ∧
        ¬ Y ≤ (V.subgroupOf N).map (QuotientGroup.mk' (I.subgroupOf N)) := by
  let q := QuotientGroup.mk' S
  let Ab := A.map q
  let Bb := B.map q
  let J := D ⊔ Ab
  let H := J.comap q
  let I := S ⊔ B
  let Q := ((P : Subgroup G) ⊓ S) ⊔ B
  let N := H ⊓ normalizer (Q : Set G)
  have hBI : Bb.comap q = I := by
    rw [comap_map_eq,QuotientGroup.ker_mk']
    exact sup_comm _ _
  change ∃ n : (I.subgroupOf N).Normal, letI := n
    ∃ Y : Subgroup (N ⧸ I.subgroupOf N), Y.Normal ∧ Nat.card Y = r ∧
      centralizer (Y : Set (N ⧸ I.subgroupOf N)) ≤ Y ∧
      (∀ Z : Subgroup (N ⧸ I.subgroupOf N), Z ≤ Y → Z = ⊥ ∨ Z = Y) ∧
      ¬ Y ≤ (V.subgroupOf N).map (QuotientGroup.mk' (I.subgroupOf N))
  rw [←hBI]
  let : IsElementaryAbelian 2 Ab := IsElementaryAbelian.map q
  obtain ⟨nb,hYn,hYc,_,hYC,hmin,hout'⟩ := odd_line_hyperplane_section D Ab Bb (V.map q)
    ho hc (map_mono hBA) ((actor_hyperplane_image_index q A B hBA (by simpa only [q,QuotientGroup.ker_mk'] using hASB)).trans hi)
    hAD hm hDB (map_mono hBV) hout
  let := nb
  have hlocal := hyperplane_local_normalizer P S A B hAP hBA hi hASB D hDB
  obtain ⟨_,hHI,_,_,_,_,_,hgen⟩ := hlocal
  have hNI : N ≤ normalizer (Bb.comap q : Set G) := by rw [hBI]; exact inf_le_left.trans hHI
  obtain ⟨nn,e,he⟩ := frattini_quotient_equiv q (QuotientGroup.mk'_surjective S)
    J Bb ((map_mono hBA).trans le_sup_right) N inf_le_left hNI (by rwa [hBI])
  let := nn
  let Yb := (D.subgroupOf J).map (QuotientGroup.mk' (Bb.subgroupOf J))
  let := hYn
  let U := ((V.map q).subgroupOf J).map (QuotientGroup.mk' (Bb.subgroupOf J))
  have hVU : ((V.subgroupOf N).map (QuotientGroup.mk' ((Bb.comap q).subgroupOf N))).map
      e.toMonoidHom ≤ U := by
    rintro z ⟨y,⟨x,hx,rfl⟩,rfl⟩
    rw [show e.toMonoidHom (QuotientGroup.mk' _ x) = _ from he x]
    exact mem_map_of_mem _ (show q x ∈ V.map q from mem_map_of_mem q hx)
  obtain ⟨Y,hY,hcard,hcent,hminimal,hnc⟩ := prime_section_equiv_transfer e Yb U
    ((V.subgroupOf N).map (QuotientGroup.mk' ((Bb.comap q).subgroupOf N)))
    hYc hYC hmin hout' hVU
  exact ⟨nn,Y,hY,hcard,hcent,hminimal,hnc⟩
end Theory.GroupTheory
