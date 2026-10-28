module

public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearThree
public import Theory.GroupTheory.SylowImageIntersection
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Passing invariant parabolics to the faithful component quotient

Two proper Sylow-invariant subgroups of a normal supplement remain proper
under a homomorphism injective on that supplement. The supplied Sylow's
intersection maps to the intersection of its image with the supplement image,
by Sylow maximality. Their mapped pair therefore obstructs minimal
parabolicity whenever those images generate the target.

Source: Aschbacher--Smith B.6.9, printed p.116. This transport allows the
natural module to live on N_H(L), even when centralizer scalars prevent its
action from descending to N_H(L)/C_H(L).
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

/-- The two-parabolic obstruction survives an injective component image,
retaining the original Sylow and its literal image. -/
theorem not_minimalParabolic_quotient_of_two_overgroups
    {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (L : Subgroup H) [L.Normal]
    (q : H →* G) (hqL : Function.Injective (q.comp L.subtype))
    (T : Sylow 2 G) (hT : (T : Subgroup G) = (S : Subgroup H).map q)
    (hgen : L.map q ⊔ (T : Subgroup G) = ⊤)
    (P Q : Subgroup H) (hPQ : P ⊔ Q = L) (hP : P ≠ L) (hQ : Q ≠ L)
    (hnP : (S : Subgroup H) ≤ normalizer (P : Set H))
    (hnQ : (S : Subgroup H) ≤ normalizer (Q : Set H))
    (hiP : L ⊓ (S : Subgroup H) ≤ P) (hiQ : L ⊓ (S : Subgroup H) ≤ Q) :
    ¬ IsMinimalParabolicOver T ⊤ := by
  have hPL : P ≤ L := le_sup_left.trans hPQ.le
  have hQL : Q ≤ L := le_sup_right.trans hPQ.le
  have proper (A : Subgroup H) (hAL : A ≤ L) (hne : A ≠ L) : A.map q ≠ L.map q := by
    intro he
    apply hne
    apply le_antisymm hAL
    intro x hx
    have hxq : q x ∈ A.map q := he.symm ▸ mem_map_of_mem q hx
    obtain ⟨a,ha,hax⟩ := hxq
    have hax' : (⟨a,hAL ha⟩ : L) = ⟨x,hx⟩ := hqL hax
    have hav : a = x := congrArg (fun z : L => (z : H)) hax'
    exact hav ▸ ha
  have hnorm (A : Subgroup H) (hn : (S : Subgroup H) ≤ normalizer (A : Set H)) :
      (T : Subgroup G) ≤ normalizer (A.map q : Set G) := by
    rw [hT]
    exact (map_mono hn).trans (le_normalizer_map q)
  obtain ⟨R,hR⟩ := S.exists_sylow_map_eq_inf_of_normal L
  have him : (L ⊓ (S : Subgroup H)).map q = L.map q ⊓ (T : Subgroup G) := by
    rw [hT, inf_comm L, S.map_image_eq_inf L _ R hR inf_le_left q, inf_comm]
  apply not_minimalParabolic_of_two_overgroups T (L.map q) (P.map q) (Q.map q) hgen
  · rw [← Subgroup.map_sup, hPQ]
  · exact proper P hPL hP
  · exact proper Q hQL hQ
  · exact hnorm P hnP
  · exact hnorm Q hnQ
  · rw [← him]
    exact map_mono hiP
  · rw [← him]
    exact map_mono hiQ

end CFSG.Quasithin.ChapterB
