module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.Elementary
public import Stellmacher.BaumannMap
public import Stellmacher.ElementaryAbelianMaxJFixedCenter
public import Theory.GroupTheory.MinimalParabolicCentral
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Thompson movement in the Baumann-fixed C.1.17 class

The marking transports Baumann-fixedness to its literal Sylow image. If
J(T) centralizes the moved subgroup, maximal elementary order puts that
subgroup in Ω₁(Z(J(T))). Baumann-fixedness then makes T centralize it, and
minimal-parabolic normal generation makes it central in H. Its natural
quotient would be trivial, a contradiction. This provides the actual
movement input for the semilinear natural-module Baumann theorem.

Source: Aschbacher–Smith C.1.17–18, printed p.126, using B.2.3 and the
minimal-parabolic condition of B.6.1. The quotient and actor are the
literal constructions in C.1.17.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}

theorem InLocalClass.baumann_range_eq_self (h : InLocalClass e) (hB : IsBaumannFixed B) :
    ChapterB.baumann e.range = e.range := by
  have hmap := baumann_map_injective e h.injective (⊤ : Subgroup B)
  change (ChapterB.baumann (⊤ : Subgroup B)).map e =
    ChapterB.baumann ((⊤ : Subgroup B).map e) at hmap
  rw [show ChapterB.baumann (⊤ : Subgroup B) = ⊤ from hB] at hmap
  have ht : (⊤ : Subgroup B).map e = e.range := by ext x; simp
  simpa only [ht] using hmap.symm

omit [Finite B] in
theorem InLocalClass.moved_not_centralizes_actor (h : InLocalClass e) :
    ¬ moved e ≤ centralizer (actorLift e : Set H) := by
  intro hc
  obtain ⟨n,hn,F,_,_,_,hF,⟨m⟩⟩ := h.natural
  have ht : movedFixed e = ⊤ := by
    apply top_unique
    intro x hx
    exact hc x.property
  have : Subsingleton (MovedModule e) := by
    change Subsingleton (moved e ⧸ movedFixed e)
    rw [ht]
    exact QuotientGroup.subsingleton_quotient_top
  let : Subsingleton (Multiplicative (Fin 2 → F)) :=
    m.moduleIso.symm.injective.subsingleton
  exact zero_ne_one (congrFun (Subsingleton.elim
    (Multiplicative.ofAdd (0 : Fin 2 → F)) (Multiplicative.ofAdd (1 : Fin 2 → F))) 0)

theorem InLocalClass.thompson_moves_moved (h : InLocalClass e) (hB : IsBaumannFixed B)
    (T : Sylow 2 H) (he : e.range = (T : Subgroup H)) :
    ¬ elementaryAbelianMaxJ (T : Subgroup H) ≤ centralizer (moved e : Set H) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 (localV e) := h.localV_elementary
  let : IsElementaryAbelian 2 (moved e) := IsElementaryAbelian.of_le (moved_le_localV e)
  have hMT : moved e ≤ T := (h.moved_le_coreOmegaCenter.trans
    (fun x hx => ((mem_omegaOneCenterAmbient_iff (pCore 2 H) x).mp hx).1)).trans (pCore_isPGroup.le_sylow_of_normal T)
  intro hJ
  have hMα := elementary_centralizer_maxJ_le_omegaCenter (T : Subgroup H) (moved e)
    hMT (Subgroup.le_centralizer_iff.mp hJ)
  have hBaum : ChapterB.baumann (T : Subgroup H) = T := by
    rw [← he]
    exact InLocalClass.baumann_range_eq_self h hB
  have hTC : (T : Subgroup H) ≤ centralizer (moved e : Set H) := by
    calc
      (T : Subgroup H) = ChapterB.baumann (T : Subgroup H) := hBaum.symm
      _ ≤ centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ (T : Subgroup H)) : Set H) := inf_le_right
      _ ≤ centralizer (moved e : Set H) := Subgroup.centralizer_le hMα
  obtain ⟨S,heS,hS⟩ := h.sylow
  have hST : S = T := Sylow.ext (heS.symm.trans he)
  subst S
  have hnT := (ChapterB.isMinimalParabolicOver_top_iff T).mp hS
  have hMC := T.le_center_of_normal_of_uniqueMaximal hS.1 hnT.2 (moved e) hTC
  apply InLocalClass.moved_not_centralizes_actor h
  intro x hx a ha
  exact (Subgroup.mem_center_iff.mp (hMC hx)) a
end CFSG.Quasithin.ChapterC.GlaubermanNiles
