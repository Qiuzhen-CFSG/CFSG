module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AdditionalFusion.Tables
public import Theory.GroupTheory.WeakClosureOvergroups

/-!
# Held's S under the contrary initial-fusion assumptions

If the marked central involution is separated from the four other local
classes in S, it is the unique element of S in its ambient conjugacy class.
Consequently N_G(S) is the displayed Sylow subgroup. A conjugate of S in that
Sylow is one of the four elementary sixteens. Its unique fused element is
again pi, so its normalizer lies in H. The four local normalizer orders
384, 128, 64, 64 then distinguish S and prove its weak closure.

These are the contrary-assumption tools of Held's Lemma 2.9. They are used
to exclude the remaining local fusion branches, rather than assuming the
required initial fusion.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.9, printed pp.229--230.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.InitialS
open Coordinates
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The contrary fusion assumption in Held 2.9, without a choice of lambda. -/
@[expose] public def Separated : Prop :=
  ¬ IsConj D.z (D.a10NoncentralInvolution e) ∧
  ¬ IsConj D.z (D.a10ModelEmbedding e tau) ∧
  ¬ IsConj D.z (D.a10ModelEmbedding e lam) ∧
  ¬ IsConj D.z (D.a10ModelEmbedding e (pi * lam))

public theorem eq_pi_of_mem_S (h : Separated D e) {x : G}
    (hx : x ∈ ambientElementary D e 1) (hf : IsConj D.z x) : x = D.z := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨a, rfl⟩ := (mem_elementary 1 y).mp hy
  have hc := hf.trans ((D.a10ModelEmbedding e).map_isConj (elementaryWord_isConj 1 a).symm)
  have hb : (elementaryClass 1 a).val < 6 := by
    have hh : ∀ a : BaseCode, (elementaryClass 1 a).val < 6 := by decide +kernel
    exact hh a
  have hpi : elementaryClass 1 a = 1 → elementaryWord 1 a = pi := by
    have hh : ∀ a : BaseCode, elementaryClass 1 a = 1 → elementaryWord 1 a = pi := by
      decide +kernel
    exact hh a
  generalize hi : elementaryClass 1 a = i at hc hb
  fin_cases i
  · exact (D.z_ne_one (isConj_one_left.mp (by simpa [localRepresentative] using hc))).elim
  · rw [hpi hi, D.a10ModelEmbedding_central e]
  · exact (h.1 hc).elim
  · exact (h.2.1 hc).elim
  · exact (h.2.2.1 hc).elim
  · exact (h.2.2.2 hc).elim
  all_goals norm_num at hb

omit [Finite G] in
private theorem normalizer_le_centralizer_of_unique (A : Subgroup G)
    (hz : D.z ∈ A) (hu : ∀ x ∈ A, IsConj D.z x → x = D.z) :
    normalizer (A : Set G) ≤ D.centralizer := by
  intro g hg
  have he := hu (g * D.z * g⁻¹) ((mem_normalizer_iff.mp hg _).mp hz)
    (isConj_iff.mpr ⟨g, rfl⟩)
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)

public theorem normalizer_S_eq (h : Separated D e) :
    normalizer (ambientElementary D e 1 : Set G) = ambientD D e := by
  have hn := normalizer_le_centralizer_of_unique D (ambientElementary D e 1)
    (z_mem_ambientElementary D e 1) (fun _ hx hf => eq_pi_of_mem_S D e h hx hf)
  rw [← normalizer_S_inf_centralizer D e, inf_eq_left.mpr hn]

public theorem normalizer_S_card (h : Separated D e) :
    Nat.card (normalizer (ambientElementary D e 1 : Set G)) = 128 := by
  rw [normalizer_S_eq D e h, ambientD_card]

public theorem S_weakly_closed (h : Separated D e) (g : G)
    (hg : (ambientElementary D e 1).map (MulAut.conj g).toMonoidHom ≤ ambientSylow D e) :
    (ambientElementary D e 1).map (MulAut.conj g).toMonoidHom = ambientElementary D e 1 := by
  let S := ambientElementary D e 1
  let a := MulAut.conj g
  let B := S.map a.toMonoidHom
  have hBe : IsElementaryAbelian 2 B := by
    let := ambientElementary_isElementaryAbelian D e 1
    exact IsElementaryAbelian.map a.toMonoidHom
  have hBc : Nat.card B = 16 := by
    rw [card_map_of_injective a.injective, ambientElementary_card]
  obtain ⟨k, hk⟩ := ambient_elementary_sixteen D e B hg hBe hBc
  have hzB : D.z ∈ B := hk.symm ▸ z_mem_ambientElementary D e k
  obtain ⟨w, hw, hwz⟩ := hzB
  change a w = D.z at hwz
  have hwf : IsConj D.z w := by
    have hh : IsConj w (a w) := isConj_iff.mpr ⟨g, rfl⟩
    rw [hwz] at hh
    exact hh.symm
  have hwpi : w = D.z := eq_pi_of_mem_S D e h hw hwf
  have haz : a D.z = D.z := hwpi ▸ hwz
  have hBunique (x : G) (hx : x ∈ B) (hf : IsConj D.z x) : x = D.z := by
    obtain ⟨v, hv, rfl⟩ := hx
    have hvf : IsConj D.z v := hf.trans (isConj_iff.mpr ⟨g, rfl⟩).symm
    change a v = D.z
    rw [eq_pi_of_mem_S D e h hv hvf, haz]
  have hBN : normalizer (B : Set G) ≤ D.centralizer :=
    normalizer_le_centralizer_of_unique D B (hk.symm ▸ z_mem_ambientElementary D e k) hBunique
  have hcard : Nat.card (normalizer (B : Set G)) = 128 := by
    rw [show normalizer (B : Set G) = (normalizer (S : Set G)).map a.toMonoidHom from
      (S.map_equiv_normalizer_eq a).symm,
      card_map_of_injective a.injective]
    exact normalizer_S_card D e h
  have hlocal := ambient_normalizer_intersection_card D e k
  rw [← hk, inf_eq_left.mpr hBN, hcard] at hlocal
  have hk1 : k = 1 := by
    fin_cases k
    · norm_num at hlocal
    · rfl
    · norm_num at hlocal
    · norm_num at hlocal
  exact hk.trans (congrArg (ambientElementary D e) hk1)

/-- Every two-subgroup containing S normalizes it under the contrary fusion assumption. -/
public theorem two_subgroup_le_normalizer_S (h : Separated D e)
    (R : Subgroup G) (hR : IsPGroup 2 R) (hSR : ambientElementary D e 1 ≤ R) :
    R ≤ normalizer (ambientElementary D e 1 : Set G) :=
  le_normalizer_of_isPGroup_of_weakly_closed (ambientSylow D e) _ R
    (S_weakly_closed D e h) hR hSR

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.InitialS
