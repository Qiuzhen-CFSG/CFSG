module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.LiftedModule
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.OmegaLift
/-!
# The original C.1.27 block-lifting consumer

Starting with the actual Sylow T and locally subnormal short K inside
H≥T, let V be the full orbit of Ω₁Z(T). Given the preceding B.6.9 support
U(K)≤V and B.1.13's actual subnormal image B in G/C_G(V), form the
literal preimage conjugate span L=⟨K^(q⁻¹B)⟩. The earlier image alternatives
prove q(L)=B, and local core action supplies the exact displacement bound.
The ambient, kernel and module lifts then construct a genuine block L≥K
with U(L)≤V. No shortness or irreducibility of L is supplied as a premise.

The universal B.6.9 support and B.1.13 quotient-selection producers remain
separate source dependencies; this theorem does not assert their existence.
Source: Aschbacher–Smith C.1.27, printed pp.132–133.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct
variable {G : Type*} [Group G] [Finite G]

private theorem local_displacement {H K : Subgroup G} (hKH : K ≤ H)
    (hsub : (K.subgroupOf H).IsSubnormal) (hK : IsShort K)
    (hQH : pCore 2 G ≤ H) : ⁅K, pCore 2 G⁆ ≤ (blockU K).map K.subtype := by
  let A := K.subgroupOf H
  let R := (pCore 2 G).subgroupOf H
  let e : A ≃* K := subgroupOfEquivOfLe hKH
  have hpA : IsPPerfect 2 A :=
    hK.twoPerfect.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hc := commutator_le_core_commutator_of_isSubnormal A R hsub hpA
    (pCore_isPGroup (p := 2) (G := G)).comap_subtype le_normalizer_of_normal
  have hh := map_mono (f := H.subtype) hc
  rw [map_commutator, map_subgroupOf_eq_of_le hKH,
    map_subgroupOf_eq_of_le hQH] at hh
  have he : H.subtype.comp A.subtype = K.subtype.comp e.toMonoidHom := rfl
  have hu : (blockU A).map e.toMonoidHom = blockU K := by
    rw [blockU, blockU, map_commutator, pCore_map_iso,
      map_top_of_surjective _ e.surjective]
  change ⁅pCore 2 G, K⁆ ≤ ((blockU A).map A.subtype).map H.subtype at hh
  rw [map_map, he, ← map_map, hu, commutator_comm] at hh
  exact hh

/-- Full block lifting in C.1.27 from the actual earlier B.6.9 support
and B.1.13 selection. The image, core quotient, and seed stay literal. -/
theorem source_block_of_quotient_selection (T : Sylow 2 G)
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    {H K : Subgroup G} (hTH : (T : Subgroup G) ≤ H) (hKH : K ≤ H)
    (hsub : (K.subgroupOf H).IsSubnormal) (hK : IsShort K)
    (hU : (blockU K).map K.subtype ≤
      normalClosure (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (B : Subgroup (G ⧸ centralizer
      (normalClosure (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G)))
    (hB : B.IsSubnormal)
    (hKB : K.map (QuotientGroup.mk' (centralizer
      (normalClosure (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G))) ≤ B)
    (hkind : IsQuasisimple B ∨ Nat.card B = 3)
    (hselected : let q := QuotientGroup.mk' (centralizer
      (normalClosure (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G));
      K.map q = B ∨ ⁅K.map q, B⁆ = B) :
    ∃ L : Subgroup G, K ≤ L ∧ IsBlock L ∧
      (blockU L).map L.subtype ≤
        normalClosure (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) ∧
      L.map (QuotientGroup.mk' (centralizer
        (normalClosure (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G))) = B := by
  let V := normalClosure (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)
  let q := QuotientGroup.mk' (centralizer (V : Set G))
  let L := conjugateSpanBy K (B.comap q)
  obtain ⟨hKL, hpL, hsL, huL, hfL⟩ := source_omega_lift T hchar hTH hKH hsub hK hU B hB hKB
  change K ≤ L at hKL
  have hm : L.map q = B := by
    change (conjugateSpanBy K (B.comap q)).map q = B
    rw [map_conjugateSpanBy, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
    apply le_antisymm (conjugateSpanBy_le_self hKB)
    rcases hselected with he | he
    · rw [← he]
      exact le_conjugateSpanBy _ _
    · calc
        B = ⁅K.map q, B⁆ := he.symm
        _ ≤ conjugateSpanBy (K.map q) B := by
          rw [conjugateSpanBy_eq_iSup_conj]
          exact commutator_le_iSup_conjugates _ _
  let f := q.subgroupMap L
  have ha : ((K.subgroupOf L).map f).map (L.map q).subtype = K.map q := by
    have he : (L.map q).subtype.comp f = q.comp L.subtype := rfl
    rw [map_map, he, ← map_map, map_subgroupOf_eq_of_le hKL]
  have hi : (K.subgroupOf L).map f = ⊤ ∨
      ⁅(K.subgroupOf L).map f, (⊤ : Subgroup (L.map q))⁆ = ⊤ := by
    rcases hselected with he | he
    · left
      apply map_injective (f := (L.map q).subtype) (L.map q).subtype_injective
      rw [ha, ← MonoidHom.range_eq_map, range_subtype, hm]
      exact he
    · right
      apply map_injective (f := (L.map q).subtype) (L.map q).subtype_injective
      rw [map_commutator, ha, ← MonoidHom.range_eq_map, range_subtype, hm]
      exact he
  have hk : IsQuasisimple (L.map q) ∨ Nat.card (L.map q) = 3 := by
    rw [hm]
    exact hkind
  have hv := omegaCenter_normalClosure_reduced T hchar
  let : IsElementaryAbelian 2 V := hv.elementary
  have hQC : pCore 2 G ≤ centralizer (V : Set G) :=
    le_centralizer_iff.mp hv.le_centralizer_pCore
  have hd := local_displacement hKH hsub hK (pCore_isPGroup.le_sylow_of_normal T |>.trans hTH)
  exact ⟨L, hKL, lifted_isBlock_of_image V K L hKL hK hsL hpL hfL hU huL hQC hd hi hk,
    huL, hm⟩

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct
