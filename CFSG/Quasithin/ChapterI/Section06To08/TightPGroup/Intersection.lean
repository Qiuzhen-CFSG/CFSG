module

public import CFSG.Quasithin.ChapterI.Section06To08.Basic
public import Theory.GroupTheory.TightlyEmbedded
public import Mathlib.GroupTheory.Sylow

/-!
# Tightly embedded subgroups and their Sylow intersections

The setup is exactly the one preceding I.7.2: a nontrivial Sylow 2-subgroup
`Q` of `H ∩ K` lies in a 2-subgroup `S ≤ H`, with `K` tightly embedded.
Sylow maximality is only applied to overgroups of `Q`. Odd intersections of
conjugates of `K` force trivial intersections of the corresponding 2-subgroups.
Normality in a local overgroup is expressed by `subgroupOf`.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, printed pp. 425--427, Remark I.7.1 and I.7.2--I.7.5.
Conjugation sends `x` to `g * x * g⁻¹`; replacing source conjugators by inverses
converts its right-conjugation convention to this convention.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterI.Section06To08

open Subgroup

variable {G : Type*} [Group G]

/-- Left conjugation of a subgroup. -/
def conjSubgroup (X : Subgroup G) (g : G) : Subgroup G :=
  X.map (MulAut.conj g).toMonoidHom

@[simp] theorem mem_conjSubgroup_iff {X : Subgroup G} {g x : G} :
    x ∈ conjSubgroup X g ↔ g⁻¹ * x * g ∈ X := by
  exact Subgroup.mem_map_equiv

@[simp] theorem conjSubgroup_one (X : Subgroup G) : conjSubgroup X 1 = X := by
  ext x
  simp

theorem conjSubgroup_mono {X Y : Subgroup G} (hXY : X ≤ Y) (g : G) :
    conjSubgroup X g ≤ conjSubgroup Y g := Subgroup.map_mono hXY

theorem conjSubgroup_conjSubgroup (X : Subgroup G) (g k : G) :
    conjSubgroup (conjSubgroup X g) k = conjSubgroup X (k * g) := by
  ext x
  simp [mul_assoc]

@[simp] theorem conjSubgroup_inv (X : Subgroup G) (g : G) :
    conjSubgroup (conjSubgroup X g) g⁻¹ = X := by
  rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]

theorem card_conjSubgroup (X : Subgroup G) (g : G) :
    Nat.card (conjSubgroup X g) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

private theorem tight_map_equiv {G' : Type*} [Group G']
    {K : Subgroup G} (hK : Theory.GroupTheory.IsTightlyEmbedded K) (e : G ≃* G') :
    Theory.GroupTheory.IsTightlyEmbedded (K.map e.toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · simpa only [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective] using hK.1
  · intro g hg
    have hn : e.symm g ∉ normalizer (K : Set G) := by
      intro hn
      apply hg
      rw [← Subgroup.map_equiv_normalizer_eq K e]
      exact ⟨e.symm g, hn, e.apply_symm_apply g⟩
    have heq : (K.map e.toMonoidHom) ⊓
        (K.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom =
        (K ⊓ K.map (MulAut.conj (e.symm g)).toMonoidHom).map e.toMonoidHom := by
      rw [Subgroup.map_inf _ _ e.toMonoidHom e.injective]
      congr 1
      ext x
      simp only [Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
        map_mul, map_inv]
    rw [heq, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact hK.2 _ hn

/-- The source setup, with the Sylow condition expressed as p-group maximality
among overgroups inside `H ∩ K`. -/
structure TightPGroupSetup (K H Q S : Subgroup G) : Prop where
  hK : Theory.GroupTheory.IsTightlyEmbedded K
  hQp : IsPGroup 2 Q
  hQne : Q ≠ ⊥
  hQle : Q ≤ H ⊓ K
  hQmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ H ⊓ K → Q ≤ R → R ≤ Q
  hSp : IsPGroup 2 S
  hSH : S ≤ H
  hQS : Q ≤ S

/-- Actual Sylow subgroups give the source setup. -/
theorem TightPGroupSetup.of_sylow {K H S : Subgroup G}
    (hK : Theory.GroupTheory.IsTightlyEmbedded K) (P : Sylow 2 ↥(H ⊓ K))
    (hne : (P : Subgroup ↥(H ⊓ K)).map (H ⊓ K).subtype ≠ ⊥)
    (hSp : IsPGroup 2 S) (hSH : S ≤ H)
    (hPS : (P : Subgroup ↥(H ⊓ K)).map (H ⊓ K).subtype ≤ S) :
    TightPGroupSetup K H ((P : Subgroup ↥(H ⊓ K)).map (H ⊓ K).subtype) S := by
  refine ⟨hK, P.isPGroup'.map _, hne, Subgroup.map_subtype_le _, ?_, hSp, hSH, hPS⟩
  intro R hRp hR hPR
  have hp : IsPGroup 2 (R.subgroupOf (H ⊓ K)) :=
    hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hR).symm
  have heq := P.is_maximal' hp (Subgroup.map_le_iff_le_comap.mp hPR)
  rw [← Subgroup.map_subgroupOf_eq_of_le hR, heq]

/-- I.7.2(1): the chosen Sylow subgroup is the intersection with `K`. -/
theorem TightPGroupSetup.intersection_eq {K H Q S : Subgroup G}
    (h : TightPGroupSetup K H Q S) : S ⊓ K = Q := by
  apply le_antisymm
  · exact h.hQmax _ (h.hSp.to_le inf_le_left)
      (inf_le_inf_right K h.hSH) (le_inf h.hQS (h.hQle.trans inf_le_right))
  · exact le_inf h.hQS (h.hQle.trans inf_le_right)

/-- Remark I.7.1: transport by an element of `H`. The containing 2-subgroup
may be any subgroup of `H` containing the transported Sylow subgroup. -/
theorem TightPGroupSetup.conjugate {K H Q S : Subgroup G}
    (h : TightPGroupSetup K H Q S) {g : G} (hg : g ∈ H)
    {T : Subgroup G} (hTp : IsPGroup 2 T) (hTH : T ≤ H)
    (hQT : conjSubgroup Q g ≤ T) :
    TightPGroupSetup (conjSubgroup K g) H (conjSubgroup Q g) T := by
  have hgn : g ∈ normalizer (H : Set G) := H.le_normalizer hg
  have hcgH : conjSubgroup H g = H := mem_normalizer_iff_map_conj_eq.mp hgn
  have hcgiH : conjSubgroup H g⁻¹ = H :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (H : Set G)).inv_mem hgn)
  refine ⟨tight_map_equiv h.hK (MulAut.conj g), h.hQp.map _, ?_, ?_, ?_,
    hTp, hTH, hQT⟩
  · intro heq
    apply h.hQne
    have := congrArg (fun X => conjSubgroup X g⁻¹) heq
    rw [conjSubgroup_inv] at this
    simpa only [conjSubgroup, Subgroup.map_bot] using this
  · refine le_inf ?_ (conjSubgroup_mono (h.hQle.trans inf_le_right) g)
    rw [← hcgH]
    exact conjSubgroup_mono (h.hQle.trans inf_le_left) g
  · intro R hRp hR hQR
    have hiR : conjSubgroup R g⁻¹ ≤ H ⊓ K := by
      refine le_inf ?_ ?_
      · rw [← hcgiH]
        exact conjSubgroup_mono (hR.trans inf_le_left) _
      · simpa using conjSubgroup_mono (hR.trans inf_le_right) g⁻¹
    have hQiR : Q ≤ conjSubgroup R g⁻¹ := by
      simpa using conjSubgroup_mono hQR g⁻¹
    have hm := h.hQmax _ (hRp.map _) hiR hQiR
    have := conjSubgroup_mono hm g
    change conjSubgroup (conjSubgroup R g⁻¹) g ≤ conjSubgroup Q g at this
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at this
    exact this

theorem lemma_I_7_2_1 {K H Q S : Subgroup G}
    (h : TightPGroupSetup K H Q S) : S ⊓ K = Q := h.intersection_eq

variable [Finite G]

private theorem two_subgroup_eq_bot_of_odd {P L : Subgroup G}
    (hP : IsPGroup 2 P) (hle : P ≤ L) (hodd : Odd (Nat.card L)) : P = ⊥ := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have hc : (Nat.card P).Coprime (Nat.card L) := by
    rw [hn]
    exact hodd.coprime_two_left.pow_left n
  simpa only [inf_eq_left.mpr hle] using (Subgroup.disjoint_of_coprime_natCard hc).eq_bot

/-- I.7.2(2): distinct `H`-conjugates contained in the 2-subgroup are disjoint. -/
theorem lemma_I_7_2_2 {K H Q S : Subgroup G}
    (h : TightPGroupSetup K H Q S) {g : G} (hg : g ∈ H)
    (hQgS : conjSubgroup Q g ≤ S) (hne : conjSubgroup Q g ≠ Q) :
    Q ⊓ conjSubgroup Q g = ⊥ := by
  have hc := (h.conjugate hg h.hSp h.hSH hQgS).intersection_eq
  have hn : g ∉ normalizer (K : Set G) := by
    intro hn
    apply hne
    rw [show conjSubgroup K g = K from mem_normalizer_iff_map_conj_eq.mp hn,
      h.intersection_eq] at hc
    exact hc.symm
  exact two_subgroup_eq_bot_of_odd (h.hQp.to_le inf_le_left)
    (inf_le_inf (h.hQle.trans inf_le_right)
      (conjSubgroup_mono (h.hQle.trans inf_le_right) g)) (h.hK.2 g hn)

/-- I.7.2(3): TI under the entire ambient normalizer of `S`, which need not
be contained in `H`. -/
theorem lemma_I_7_2_3 {K H Q S : Subgroup G}
    (h : TightPGroupSetup K H Q S) {g : G}
    (hgS : g ∈ normalizer (S : Set G)) (hgQ : g ∉ normalizer (Q : Set G)) :
    Q ⊓ conjSubgroup Q g = ⊥ := by
  have hn : g ∉ normalizer (K : Set G) := by
    intro hgK
    apply hgQ
    rw [← h.intersection_eq]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hgS, hgK⟩
  exact two_subgroup_eq_bot_of_odd (h.hQp.to_le inf_le_left)
    (inf_le_inf (h.hQle.trans inf_le_right)
      (conjSubgroup_mono (h.hQle.trans inf_le_right) g)) (h.hK.2 g hn)

/-- I.7.2(4), stated inside the 2-group itself. -/
theorem lemma_I_7_2_4 (hG : IsPGroup 2 G) {T : Subgroup G}
    (hT : IsTISubgroup T) (hne : T ≠ ⊥) : Theory.GroupTheory.IsTightlyEmbedded T := by
  have hp := hG.to_subgroup T
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have hn0 : n ≠ 0 := by
    intro hz
    have hc : Nat.card T = 1 := by simp [hn, hz]
    exact hne (Subgroup.card_eq_one.mp hc)
  refine ⟨even_iff_two_dvd.mpr (hn ▸ dvd_pow_self 2 hn0), ?_⟩
  intro g hg
  have heq : T ⊓ conjSubgroup T g = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx.2
    exact hT g hg ⟨hx.1, ⟨y, hy, rfl⟩⟩
  change Odd (Nat.card ↥(T ⊓ conjSubgroup T g))
  rw [heq]
  simp

/-- I.7.2(5): ambient and relative normalizer control. -/
theorem lemma_I_7_2_5 {K H Q S X : Subgroup G}
    (h : TightPGroupSetup K H Q S) (hXne : X ≠ ⊥) (hXQ : X ≤ Q) :
    normalizer (X : Set G) ≤ normalizer (K : Set G) ∧
      S ⊓ normalizer (X : Set G) ≤ S ⊓ normalizer (Q : Set G) := by
  have hn := h.hK.normalizer_le (h.hQp.to_le hXQ) hXne
    (hXQ.trans (h.hQle.trans inf_le_right))
  refine ⟨hn, le_inf inf_le_left ?_⟩
  rw [← h.intersection_eq]
  exact (inf_le_inf S.le_normalizer hn).trans Subgroup.inf_normalizer_le_normalizer_inf

end CFSG.Quasithin.ChapterI.Section06To08
