module
public import Theory.GroupTheory.CComponent.SimpleNormalCentralizer

/-!
# Commutator detection through a faithful simple image

If a normal subgroup P is abelian modulo a normal layer N, its centralizer
modulo N has normal image in any quotient. A subgroup outside the quotient
kernel forces that image to contain the faithful nonabelian simple normal
subgroup. Hence it detects the full commutator with that component.

Application: the non-Frattini step of Meierfrankenfeld--Stellmacher (1993),
(3.6), printed p.870. Outer automorphisms of the simple image are allowed.
-/

public section
open Subgroup
namespace Subgroup
variable {G J : Type*} [Group G] [Group J]

theorem commutator_le_of_faithful_simple_image
    (q : G →* J) (hq : Function.Surjective q)
    (P N E L : Subgroup G) [P.Normal] [N.Normal]
    [((L.map q)).Normal] [IsSimpleGroup (L.map q)]
    (ha : ¬ IsMulCommutative (L.map q))
    (hC : centralizer (L.map q : Set J) = ⊥)
    (hker : q.ker = P) (hPP : ⁅P,P⁆ ≤ N)
    (hE : ¬ E ≤ P) (hPE : ⁅P,E⁆ ≤ N) : ⁅P,L⁆ ≤ N := by
  let π := QuotientGroup.mk' N
  let C := (centralizer (P.map π : Set (G ⧸ N))).comap π
  have hc (A : Subgroup G) : A ≤ C ↔ ⁅P,A⁆ ≤ N := by
    change A ≤ (centralizer (P.map π : Set (G ⧸ N))).comap π ↔ _
    rw [← map_le_iff_le_comap, ← le_centralizer_iff,
      ← commutator_eq_bot_iff_le_centralizer, ← map_commutator,
      Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  let : (P.map π).Normal := Normal.map inferInstance π (QuotientGroup.mk'_surjective N)
  have hPC : P ≤ C := (hc P).mpr hPP
  have hEC : E ≤ C := (hc E).mpr hPE
  let : (C.map q).Normal := Normal.map inferInstance q hq
  have hCN : C.map q ≠ ⊥ := by
    intro hz
    exact hE (hEC.trans (hker ▸ (map_eq_bot_iff C).mp hz))
  have hLC : L.map q ≤ C.map q :=
    simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot (L.map q) ha hC (C.map q) hCN
  apply (hc L).mp
  have h := comap_mono (f := q) hLC
  rw [comap_map_eq,comap_map_eq,hker,sup_of_le_left hPC] at h
  exact le_sup_left.trans h
end Subgroup
