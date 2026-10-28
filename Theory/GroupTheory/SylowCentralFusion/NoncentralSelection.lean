module

public import Theory.GroupTheory.SylowCentralFusion.Selection
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Group

/-!
# Normal-closure selection for a noncentral conjugate

Among Sylow two-subgroups containing z noncentrally, maximize the order of
D = C_S(z). Normalizer growth supplies a mover of z in N_G(D). Generating
z's conjugates under N_G(D) gives Q ≤ D ∩ ⟨zᴳ⟩ and N_G(D) ≤ N_G(Q).

Since z centralizes the given Sylow T, D lies properly in a Sylow subgroup
V of G contained in C_G(z). Thus N_V(D) has order greater than |D|. A Sylow
subgroup of N_G(Q) containing N_V(D) extends to a Sylow U of G. Maximality
forces U to centralize z; conjugacy inside C_G(z) aligns U with T while
fixing z. Transport preserves the exact Sylow normalizer map and the mover.

This proves the noncentral branch of the normal-closure consequence of
clause (e′) in G. Glauberman, “On the automorphism group of a finite group
having no non-identity normal subgroups of odd order”, Math. Z. 93 (1966),
Lemma 1, pp.155–156, DOI 10.1007/BF01111033. The odd-order adjustment is
provided separately by `NormalizerSelection.exists_witness`.
-/

open Subgroup
open scoped Pointwise
namespace SylowCentralFusion
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem transport_selection (U T : Sylow 2 G) (z : G)
    (e : MulAut G) (hez : e z = z)
    (hUT : (U : Subgroup G).map e.toMonoidHom = (T : Subgroup G))
    (s : NormalizerSelection U z)
    (hs : s.subgroup ≤ normalClosure ({z} : Set G)) :
    ∃ t : NormalizerSelection T z, t.subgroup ≤ normalClosure ({z} : Set G) := by
  let Q := s.subgroup.map e.toMonoidHom
  let N := normalizer (s.subgroup : Set G)
  let N' := normalizer (Q : Set G)
  have hN : N.map e.toMonoidHom = N' :=
    map_normalizer_eq_of_bijective _ e.bijective
  let eN : N ≃* N' := (e.subgroupMap N).trans (MulEquiv.subgroupCongr hN)
  obtain ⟨R, hR⟩ := s.normalizer_sylow
  let R' : Sylow 2 N' := R.mapSurjective (f := eN.toMonoidHom) eN.surjective
  have hR' : (R' : Subgroup N').map N'.subtype = (T : Subgroup G) ⊓ N' := by
    calc
      (R' : Subgroup N').map N'.subtype =
          ((R : Subgroup N).map N.subtype).map e.toMonoidHom := by
        change ((R : Subgroup N).map eN.toMonoidHom).map N'.subtype = _
        rw [map_map, map_map]
        rfl
      _ = (T : Subgroup G) ⊓ N' := by
        rw [hR, map_inf _ _ _ e.injective, hUT, hN]
  have hzQ : z ∈ Q := hez ▸ mem_map_of_mem e.toMonoidHom s.mem_subgroup
  obtain ⟨g, hg, hgm⟩ := s.moves
  have hegm : e g * z * (e g)⁻¹ ≠ z := by
    intro he
    apply hgm
    apply e.injective
    simpa only [map_mul, map_inv, hez] using he
  refine ⟨⟨Q, ?_, hzQ, ⟨R', hR'⟩, e g, ?_, hegm⟩, ?_⟩
  · exact (map_mono s.le_sylow).trans_eq hUT
  · exact le_normalizer_map e.toMonoidHom (mem_map_of_mem e.toMonoidHom hg)
  · exact (map_mono hs).trans (by
      simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom, hez] using
        map_normalClosure_le ({z} : Set G) e.toMonoidHom)

private theorem central_sylow_conjugacy (U T : Sylow 2 G) (z : G)
    (hU : (U : Subgroup G) ≤ centralizer ({z} : Set G))
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    ∃ e : MulAut G, e z = z ∧
      (U : Subgroup G).map e.toMonoidHom = (T : Subgroup G) := by
  let C := centralizer ({z} : Set G)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C (U.subtype hU) (T.subtype hT)
  have hambient : (c : G) • U = T := by
    apply Sylow.subtype_injective (hP := Sylow.smul_le hU c) (hQ := hT)
    rw [← Sylow.smul_subtype]
    exact hc
  refine ⟨MulAut.conj (c : G), ?_, ?_⟩
  · exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp c.property)
  · exact congrArg (fun S : Sylow 2 G => (S : Subgroup G)) hambient

private theorem normalizer_growth (V D : Subgroup G) (hV : IsPGroup 2 V)
    (hD : D < V) : D < V ⊓ normalizer (D : Set G) := by
  let : Group.IsNilpotent V := hV.isNilpotent
  have hproper : D.subgroupOf V < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
    exact not_le_of_gt hD
  obtain ⟨x, hx, hxn⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (D.subgroupOf V) hproper)
  have hxN : (x : G) ∈ normalizer (D : Set G) := by
    rw [← subgroupOf_normalizer_eq hD.le] at hx
    exact hx
  refine lt_of_le_of_ne (le_inf hD.le le_normalizer) ?_
  intro he
  apply hxn
  exact he ▸ (show (x : G) ∈ V ⊓ normalizer (D : Set G) from ⟨x.property, hxN⟩)

private theorem card_lt_of_lt {A B : Subgroup G} (h : A < B) :
    Nat.card A < Nat.card B := by
  exact Set.ncard_lt_ncard h

private theorem align_of_large_centralizer (T : Sylow 2 G) (z : G)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) (d : ℕ)
    (hmax : ∀ U : Sylow 2 G, z ∈ (U : Subgroup G) →
      ¬ (U : Subgroup G) ≤ centralizer ({z} : Set G) →
      Nat.card ↥((U : Subgroup G) ⊓ centralizer ({z} : Set G)) ≤ d)
    (Q A : Subgroup G) (hQ : IsPGroup 2 Q) (hzQ : z ∈ Q)
    (hQcl : Q ≤ normalClosure ({z} : Set G))
    (hm : ∃ g ∈ normalizer (Q : Set G), g * z * g⁻¹ ≠ z)
    (hA : IsPGroup 2 A) (hAN : A ≤ normalizer (Q : Set G))
    (hAC : A ≤ centralizer ({z} : Set G)) (hlarge : d < Nat.card A) :
    ∃ s : NormalizerSelection T z, s.subgroup ≤ normalClosure ({z} : Set G) := by
  let N := normalizer (Q : Set G)
  obtain ⟨R, hAR⟩ := (hA.comap_subtype (K := N)).exists_le_sylow
  obtain ⟨U, hUR⟩ := R.exists_comap_subtype_eq
  have hAU : A ≤ (U : Subgroup G) := by
    intro a ha
    have hmem : (⟨a, hAN ha⟩ : N) ∈ (R : Subgroup N) := hAR ha
    rw [← hUR] at hmem
    exact hmem
  let : (Q.comap N.subtype).Normal := by
    change (Q.subgroupOf (normalizer (Q : Set G))).Normal
    infer_instance
  have hQU : Q ≤ (U : Subgroup G) := by
    have hQR := (hQ.comap_subtype (K := N)).le_sylow_of_normal R
    intro q hq
    have hmem : (⟨q, le_normalizer hq⟩ : N) ∈ (R : Subgroup N) := hQR hq
    rw [← hUR] at hmem
    exact hmem
  have hUC : (U : Subgroup G) ≤ centralizer ({z} : Set G) := by
    by_contra hn
    exact (not_lt_of_ge ((card_le_of_le (le_inf hAU hAC)).trans
      (hmax U (hQU hzQ) hn))) hlarge
  have hR : (R : Subgroup N).map N.subtype = (U : Subgroup G) ⊓ N := by
    rw [← hUR]
    exact subgroupOf_map_subtype _ _
  obtain ⟨e, hez, he⟩ := central_sylow_conjugacy U T z hUC hT
  exact transport_selection U T z e hez he ⟨Q, hQU, hzQ, ⟨R, hR⟩, hm⟩ hQcl

omit [Finite G] in
private theorem exists_noncentral_sylow (T : Sylow 2 G) (z : G)
    (hf : ∃ g : G, g * z * g⁻¹ ∈ (T : Subgroup G) ∧
      g * z * g⁻¹ ∉ centralizer (T : Set G)) :
    ∃ S : Sylow 2 G, z ∈ (S : Subgroup G) ∧
      ¬ (S : Subgroup G) ≤ centralizer ({z} : Set G) := by
  obtain ⟨g, hgT, hgC⟩ := hf
  let e := MulAut.conj g⁻¹
  let S : Sylow 2 G := g⁻¹ • T
  have hez : e (g * z * g⁻¹) = z := by
    dsimp [e, MulAut.conj_apply]
    group
  have hzS : z ∈ (S : Subgroup G) :=
    hez ▸ mem_map_of_mem e.toMonoidHom hgT
  refine ⟨S, hzS, ?_⟩
  intro hSC
  apply hgC
  rw [mem_centralizer_iff]
  intro t ht
  have htS : e t ∈ (S : Subgroup G) := mem_map_of_mem e.toMonoidHom ht
  have htcomm := mem_centralizer_singleton_iff.mp (hSC htS)
  apply e.injective
  simpa only [map_mul, hez] using htcomm

private theorem exists_central_sylow_overgroup (T : Sylow 2 G) (z : G)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (D : Subgroup G) (hp : IsPGroup 2 D)
    (hDC : D ≤ centralizer ({z} : Set G)) :
    ∃ V : Sylow 2 G, D ≤ (V : Subgroup G) ∧
      (V : Subgroup G) ≤ centralizer ({z} : Set G) := by
  let C := centralizer ({z} : Set G)
  obtain ⟨V₀, hDV₀⟩ := (hp.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C (T.subtype hT) V₀
  let V : Sylow 2 G := (c : G) • T
  have hVC : (V : Subgroup G) ≤ C := Sylow.smul_le hT c
  have hV : V.subtype hVC = V₀ := (Sylow.smul_subtype hT c).symm.trans hc
  refine ⟨V, ?_, hVC⟩
  intro d hd
  have hmem : (⟨d, hDC hd⟩ : C) ∈ (V₀ : Subgroup C) := hDV₀ hd
  rw [← hV] at hmem
  exact hmem

omit [Finite G] in
private theorem generate_in_normalizer (D : Subgroup G) (z : G) (hzD : z ∈ D) :
    ∃ Q : Subgroup G, z ∈ Q ∧ Q ≤ D ∧
      normalizer (D : Set G) ≤ normalizer (Q : Set G) ∧
      Q ≤ normalClosure ({z} : Set G) := by
  let N := normalizer (D : Set G)
  let zn : N := ⟨z, le_normalizer hzD⟩
  let L : Subgroup N := normalClosure ({zn} : Set N)
  let Q := L.map N.subtype
  let : (D.subgroupOf N).Normal := by
    change (D.subgroupOf (normalizer (D : Set G))).Normal
    infer_instance
  have hLD : L ≤ D.subgroupOf N :=
    normalClosure_le_normal (Set.singleton_subset_iff.mpr hzD)
  refine ⟨Q, mem_map.mpr ⟨zn, subset_normalClosure (by simp), rfl⟩, ?_, ?_, ?_⟩
  · rintro q ⟨x, hx, rfl⟩
    exact hLD hx
  · intro n hn
    apply le_normalizer_map N.subtype
    refine mem_map.mpr ⟨⟨n, hn⟩, ?_, rfl⟩
    rw [L.normalizer_eq_top]
    exact mem_top _
  · simpa only [Set.image_singleton, subtype_apply, zn] using
      map_normalClosure_le ({zn} : Set N) N.subtype

private theorem exists_selection (T : Sylow 2 G) (z : G)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hf : ∃ g : G, g * z * g⁻¹ ∈ (T : Subgroup G) ∧
      g * z * g⁻¹ ∉ centralizer (T : Set G)) :
    ∃ s : NormalizerSelection T z, s.subgroup ≤ normalClosure ({z} : Set G) := by
  classical
  let C := centralizer ({z} : Set G)
  let bad : Set (Sylow 2 G) := {S | z ∈ (S : Subgroup G) ∧ ¬ (S : Subgroup G) ≤ C}
  have hbad : bad.Nonempty := exists_noncentral_sylow T z hf
  obtain ⟨S, hS, hmax⟩ := bad.exists_max_image
    (fun S : Sylow 2 G => Nat.card ↥((S : Subgroup G) ⊓ C)) bad.toFinite hbad
  let D : Subgroup G := (S : Subgroup G) ⊓ C
  have hzD : z ∈ D := ⟨hS.1, mem_centralizer_singleton_iff.mpr rfl⟩
  have hDp : IsPGroup 2 D := S.isPGroup'.to_le inf_le_left
  have hDS : D < (S : Subgroup G) := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro he
    exact hS.2 (he ▸ inf_le_right)
  obtain ⟨g, hg, hgD⟩ := SetLike.exists_of_lt
    (normalizer_growth (S : Subgroup G) D S.isPGroup' hDS)
  have hgm : g * z * g⁻¹ ≠ z := by
    intro he
    exact hgD ⟨hg.1, mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp he)⟩
  obtain ⟨V, hDV, hVC⟩ := exists_central_sylow_overgroup T z hT D hDp inf_le_right
  have hDVlt : D < (V : Subgroup G) := by
    refine lt_of_le_of_ne hDV ?_
    intro he
    have hVS : (V : Subgroup G) ≤ (S : Subgroup G) := he ▸ inf_le_left
    exact hDS.ne (he.trans (V.is_maximal' S.isPGroup' hVS).symm)
  let A : Subgroup G := (V : Subgroup G) ⊓ normalizer (D : Set G)
  have hDA : D < A := normalizer_growth (V : Subgroup G) D V.isPGroup' hDVlt
  obtain ⟨Q, hzQ, hQD, hNQ, hQcl⟩ := generate_in_normalizer D z hzD
  apply align_of_large_centralizer T z hT (Nat.card D)
    (fun U hzU hn => hmax U ⟨hzU, hn⟩) Q A (hDp.to_le hQD) hzQ hQcl
    ⟨g, hNQ hg.2, hgm⟩ (V.isPGroup'.to_le inf_le_left)
    (inf_le_right.trans hNQ) (inf_le_left.trans hVC)
  exact card_lt_of_lt hDA

/-- The noncentral-conjugate normal-closure selection in Glauberman's
Lemma 1. The chosen subgroup is generated by normalizer conjugates of z,
then aligned with the given Sylow by a conjugator centralizing z. -/
public theorem noncentralNormalClosureSelection : NoncentralNormalClosureSelection.{u} := by
  intro G _ _ T z _hz2 _hzT hz hf
  exact exists_selection T z (fun t ht => mem_centralizer_singleton_iff.mpr (hz t ht)) hf

end SylowCentralFusion
