module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.Containment.Local
public import Theory.GroupTheory.PResidual.NormalizedSupplement
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Setup

/-!
# Odd Sylow movement in the literal centralizer quotient

A Sylow p-subgroup supplements the two-core of the canonical radical X.
If it centralized the component image, then X would lie in the product of
that centralizer with the image of O₂(X). The latter normalizes the
centralizer, since X normalizes the component. Two-perfectness of X absorbs
this two-group supplement, contradicting the escape commutator.

Thus every chosen Sylow p-subgroup moves the component modulo O₂(C_G(u));
no commutator bound on O₂(X) is needed.

Source: Aschbacher--Smith, 13.1.12(3), printed p.874.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.RadicalNormalizers Chapter1.XiEmbedding Chapter1.RadicalActions
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L K : Subgroup G} {p : ℕ} [Fact p.Prime] {u : G}

/-- Full radical movement forces noncentrality of every odd Sylow complement. -/
theorem Context.odd_sylow_noncentral (h : Context T L p)
    (s : Selected T L u) (e : Escape T L p u K) (P : Sylow p (XiP p L)) :
    ¬ ⁅K,((P : Subgroup (XiP p L)).map (XiP p L).subtype)⁆ ≤
      (centralizer ({u} : Set G)).pCoreIn 2 := by
  let H := centralizer ({u} : Set G)
  let X := XiP p L
  let P₀ := (P : Subgroup X).map X.subtype
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := (K.subgroupOf H).map q
  let A := (X.subgroupOf H).map q
  let R := (X.pCoreIn 2).subgroupOf H |>.map q
  let C := centralizer (B : Set (XiQuotient H))
  have hXH : X ≤ H := (SourceNonquasisimple.XiP_le_moved_centralizer h.hypothesis h.many h.maximal.1
    h.nonquasisimple p s.mem).trans inf_le_right
  have hPH : P₀ ≤ H := (map_subtype_le _).trans hXH
  have hRH : X.pCoreIn 2 ≤ H := (pCoreIn_le 2 X).trans hXH
  have hsup : R ⊔ (P₀.subgroupOf H).map q = A := by
    rw [← Subgroup.map_sup, ← subgroupOf_sup hRH hPH,
      sylow_sup (XiP_quotient_isPGroup p h.odd L) P]
  have hn : X.subgroupOf H ≤ normalizer (K.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq e.component.1]
    exact subgroupOf_mono H e.normalized
  have hnA : A ≤ normalizer (B : Set (XiQuotient H)) :=
    (map_mono hn).trans ((K.subgroupOf H).le_normalizer_map q)
  have hnR : R ≤ normalizer (C : Set (XiQuotient H)) :=
    ((map_mono (subgroupOf_mono H (pCoreIn_le 2 X))).trans hnA).trans
      (normalizer_le_normalizer_centralizer B)
  have hpA : IsPPerfect 2 A :=
    ((XiP_isPPerfect p L).of_surjective (subgroupOfEquivOfLe hXH).symm.toMonoidHom
      (subgroupOfEquivOfLe hXH).symm.surjective).of_surjective
      (q.subgroupMap (X.subgroupOf H)) (q.subgroupMap_surjective _)
  intro hP
  have hcP : ⁅B,(P₀.subgroupOf H).map q⁆ = ⊥ := by
    rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [map_commutator, map_subgroupOf_eq_of_le e.component.1,
      map_subgroupOf_eq_of_le hPH]
    exact hP
  have hPC : (P₀.subgroupOf H).map q ≤ C := by
    rw [commutator_comm] at hcP
    exact commutator_eq_bot_iff_le_centralizer.mp hcP
  have hAC : A ≤ C := le_of_isPPerfect_of_le_sup_of_normalizes A C R hpA
    ((isPGroup_pCoreIn 2 X).comap_subtype.map q) hnR
    (hsup.symm.le.trans (sup_le le_sup_right (hPC.trans le_sup_left)))
  have hcX : ⁅B,A⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hAC
  have hc : ⁅K.subgroupOf H,X.subgroupOf H⁆ ≤ pCore 2 H := by
    rw [← QuotientGroup.ker_mk' (pCore 2 H), ← Subgroup.map_eq_bot_iff,
      map_commutator]
    exact hcX
  apply e.moved_mod_core
  have hh := map_mono (f := H.subtype) hc
  rwa [map_commutator, map_subgroupOf_eq_of_le e.component.1,
    map_subgroupOf_eq_of_le hXH] at hh

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
