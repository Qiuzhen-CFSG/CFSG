module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.G2RadiusTwoFirstGenerators
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.GeneratedLocals
public import Theory.GroupTheory.ThreeConjugateInvolutionSubgroups

/-!
# Exhaustion of both original radius-two vertex groups

Modulo the original distance-two subgroup, the three arms give three
conjugate subgroups of order two whose permutation action is S₃. The
three-involution recognition gives the first source group order ninety-six.
The equal point stabilizers and local transitivity now supply local coverage;
two-perfectness and the original tree-generation theorem identify both
constructed groups with the full endpoint stabilizers.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.9),
printed pp.400–401.
-/

@[expose] public section
open Subgroup SimpleGraph Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.RadiusTwoFirstArms
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

private theorem perm_three_eq_swap : ∀ (p : Equiv.Perm (Fin 3)) (i j k : Fin 3),
    i ≠ j → i ≠ k → j ≠ k → p i = i → p j = k → p = Equiv.swap j k := by
  intro p i j k hij hik hjk hpi hpj
  have hall (x : Fin 3) : x = i ∨ x = j ∨ x = k :=
    (by decide : ∀ i j k x : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      x = i ∨ x = j ∨ x = k) i j k x hij hik hjk
  have hpk : p k = j := by
    rcases hall (p k) with he | he | he
    · exact (hik (p.injective (he.trans hpi.symm)).symm).elim
    · exact he
    · exact (hjk (p.injective (hpj.trans he.symm))).elim
  apply Equiv.ext
  intro x
  rcases hall x with rfl | rfl | rfl
  · rw [hpi, Equiv.swap_apply_of_ne_of_ne hij hik]
  · rw [hpj, Equiv.swap_apply_left]
  · rw [hpk, Equiv.swap_apply_right]

/-- The first literal source group has order ninety-six. -/
theorem group_card (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 4 ≤ s)
    (h : CubicTreeAction F) (a : RankTwo.Vertex F) (ha : a.type = c.side) :
    Nat.card (group c a) = 96 := by
  classical
  obtain ⟨f⟩ := h.exists_branchFrame a
  let H := group c a
  let Q : Subgroup H := (c.sphereLabelGroup a 2).subgroupOf H
  let A : Fin 3 → Subgroup H := fun i => (arm c a (f.e i).val).subgroupOf H
  let : Finite (RankTwo.stabilizer F a) := h.finite_stabilizer a
  let : Finite H := Finite.of_injective (Subgroup.inclusion (group_le_stabilizer c a))
    (Subgroup.inclusion_injective _)
  let : Q.Normal := sphere_two_normal_group c hr (by omega) h a
  let q := QuotientGroup.mk' Q
  let P : Fin 3 → Subgroup (H ⧸ Q) := fun i => (A i).map q
  have hAH (i : Fin 3) : arm c a (f.e i).val ≤ H := arm_le c (f.e i).property
  have hQA (i : Fin 3) : Q ≤ A i := fun x hx =>
    sphere_two_le_arm c hr (by omega) h (f.e i).property hx
  have hQcard : Nat.card Q = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe (sphere_two_le_group c hr (by omega) h a)).toEquiv).trans
      (c.radiusTwo_sphere_two_card hr hs h a ha)
  have hside (i : Fin 3) : (f.e i).val.type ≠ c.side := by
    rw [←ha]
    exact (f.e i).property.1.symm
  have hAcard (i : Fin 3) : Nat.card (A i) = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe (hAH i)).toEquiv).trans
      (arm_card c hr hs h (hside i) (f.e i).property)
  have hPcard (i : Fin 3) : Nat.card (P i) = 2 := by
    have hc := (Q.subgroupOf (A i)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (hQA i)).toEquiv, hQcard, hAcard] at hc
    have hi : Q.relIndex (A i) = Nat.card (P i) := by
      simpa only [q, QuotientGroup.ker_mk'] using (A i).relIndex_ker q
    change 16 * Q.relIndex (A i) = 32 at hc
    rw [hi] at hc
    omega
  have hAgen : iSup A = ⊤ := by
    apply (Subgroup.map_injective H.subtype_injective)
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, H.range_subtype]
    simp_rw [A, Subgroup.map_subgroupOf_eq_of_le (hAH _)]
    apply le_antisymm
    · exact iSup_le hAH
    · apply iSup_le
      intro β
      obtain ⟨i, rfl⟩ := f.e.surjective β
      exact le_iSup (fun i => arm c a (f.e i).val) i
  have hPgen : iSup P = ⊤ := by
    rw [show iSup P = (iSup A).map q from (Subgroup.map_iSup q A).symm,
      hAgen, Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective Q)]
  let ψ : H →* Equiv.Perm (Fin 3) :=
    f.branchAction.comp (Subgroup.inclusion (group_le_stabilizer c a))
  have hψeval (g : H) (i : Fin 3) :
      (f.e (ψ g i)).val = g.val • (f.e i).val :=
    f.branchAction_eval (Subgroup.inclusion (group_le_stabilizer c a) g) i
  have hQker : Q ≤ ψ.ker := by
    intro g hg
    change ψ g = 1
    apply Equiv.ext
    intro i
    apply f.e.injective
    apply Subtype.ext
    rw [hψeval]
    have hle : c.sphereLabelGroup a 2 ≤ RankTwo.stabilizer F (f.e i).val := by
      apply (closure_le _).mpr
      rintro _ ⟨w,⟨hw,ht⟩,rfl⟩
      have hd := h.tree.connected.dist_triangle (u := w) (v := a) (w := (f.e i).val)
      have hwa : (RankTwo.graph F).dist w a = 2 := by rwa [SimpleGraph.dist_comm]
      have hai : (RankTwo.graph F).dist a (f.e i).val = 1 :=
        dist_eq_one_iff_adj.mpr (f.e i).property
      rw [hwa,hai] at hd
      exact c.fixes_ball w ht _ (by omega) (by omega)
    exact hle hg
  let ρ : (H ⧸ Q) →* Equiv.Perm (Fin 3) := QuotientGroup.lift Q ψ hQker
  have hρq (g : H) : ρ (q g) = ψ g := rfl
  have hfixA (i : Fin 3) (g : H) (hg : g ∈ A i) : ψ g i = i := by
    apply f.e.injective
    apply Subtype.ext
    rw [hψeval]
    exact c.radiusTwo_second_le_stabilizer hr (by omega) (f.e i).val hg.1
  have hfix (i : Fin 3) (g : H ⧸ Q) (hg : g ∈ P i) : ρ g i = i := by
    obtain ⟨x, hx, rfl⟩ := hg
    exact hfixA i x hx
  have hmove (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) :
      ∃ g ∈ P i, ρ g j = k := by
    have hne (u w : Fin 3) (huw : u ≠ w) : (f.e u).val ≠ (f.e w).val :=
      fun he => huw (f.e.injective (Subtype.ext he))
    obtain ⟨x,hx,he⟩ := arm_neighbor_transitive c hr hs h
      (hside i) (f.e i).property (f.e j).property (f.e k).property
      (hne i j hij) (hne i k hik)
    let g : H := ⟨x, hAH i hx⟩
    refine ⟨q g, mem_map.mpr ⟨g, hx, rfl⟩, ?_⟩
    rw [hρq]
    apply f.e.injective
    apply Subtype.ext
    exact (hψeval g j).trans he
  have hρsurj : Function.Surjective ρ := by
    apply MonoidHom.range_eq_top.mp
    have hswap (j k : Fin 3) : Equiv.swap j k ∈ ρ.range := by
      by_cases hjk : j = k
      · subst k
        simpa only [Equiv.swap_self, ← Equiv.Perm.one_def] using ρ.range.one_mem
      obtain ⟨i, hij, hik⟩ := Fin.exists_ne_and_ne_of_two_lt j k (by decide : 2 < 3)
      obtain ⟨g, hg, he⟩ := hmove i j k hij hik
      exact ⟨g, perm_three_eq_swap (ρ g) i j k hij hik hjk (hfix i g hg) he⟩
    apply top_unique
    intro σ
    induction σ using Equiv.Perm.swap_induction_on with
    | one => intro _; exact ρ.range.one_mem
    | swap_mul σ i j hij hσ => intro _; exact ρ.range.mul_mem (hswap i j) (hσ (mem_top _))
  have hconj (g : H ⧸ Q) (i : Fin 3) :
      (P i).map (MulAut.conj g).toMonoidHom = P (ρ g i) := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q g
    have hconjA : (A i).map (MulAut.conj g).toMonoidHom = A (ψ g i) := by
      apply (Subgroup.map_injective H.subtype_injective)
      rw [Subgroup.map_map]
      have hm : H.subtype.comp (MulAut.conj g).toMonoidHom =
          (MulAut.conj g.val).toMonoidHom.comp H.subtype := rfl
      rw [hm, ← Subgroup.map_map]
      simp_rw [A, Subgroup.map_subgroupOf_eq_of_le (hAH _)]
      rw [arm_map_conj, show g.val • a = a from
        group_le_stabilizer c a g.property, ← hψeval]
    change ((A i).map q).map (MulAut.conj (q g)).toMonoidHom = (A (ψ g i)).map q
    rw [← hconjA, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hquot : Nat.card (H ⧸ Q) = 6 :=
    ThreeConjugateInvolutionSubgroups.card_eq_six P hPcard hPgen ρ hρsurj hconj hmove
  have hc := Q.card_mul_index
  rw [hQcard, Subgroup.index_eq_card, hquot] at hc
  exact hc.symm

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.RadiusTwoFirstArms

open Subgroup SimpleGraph
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

namespace RadiusTwoFirstArms

theorem pointStabilizer_index (c : CanonicalLabelSetup F s) (hr : c.radius = 2)
    (hs : 4 ≤ s) (h : CubicTreeAction F) {a β : RankTwo.Vertex F}
    (ha : a.type = c.side) (hadj : (RankTwo.graph F).Adj a β) :
    (group c a ⊓ RankTwo.stabilizer F β).relIndex (group c a) = 3 := by
  let H := group c a
  have ho : MulAction.orbit H β = (RankTwo.graph F).neighborSet a := by
    ext b
    constructor
    · rintro ⟨g, rfl⟩
      have he := (translationGraphIso F g.val).toHom.map_adj hadj
      change (RankTwo.graph F).Adj (g.val • a) (g.val • β) at he
      change (RankTwo.graph F).Adj a (g.val • β)
      simpa only [show g.val • a = a from group_le_stabilizer c a g.property] using he
    · intro hb
      obtain ⟨g, hg, he⟩ := group_neighbor_transitive c hr hs h ha hadj hb
      exact ⟨⟨g,hg⟩,he⟩
  have he : (H ⊓ RankTwo.stabilizer F β).subgroupOf H = MulAction.stabilizer H β := by
    ext g
    exact ⟨fun hg => hg.2, fun hg => ⟨g.property,hg⟩⟩
  change (H ⊓ RankTwo.stabilizer F β).relIndex H = 3
  rw [Subgroup.relIndex, he, MulAction.index_stabilizer, ho, ← Nat.card_coe_set_eq]
  exact h.card_neighbor a

theorem pointStabilizer_eq_arm (c : CanonicalLabelSetup F s) (hr : c.radius = 2)
    (hs : 4 ≤ s) (h : CubicTreeAction F) {a β : RankTwo.Vertex F}
    (ha : a.type = c.side) (hadj : (RankTwo.graph F).Adj a β) :
    group c a ⊓ RankTwo.stabilizer F β = arm c a β := by
  have hβ : β.type ≠ c.side := by rw [←ha]; exact hadj.1.symm
  let : Finite (group c a) := Nat.finite_of_card_ne_zero
    (by rw [group_card c hr hs h a ha]; decide)
  let : Finite (group c a ⊓ RankTwo.stabilizer F β : Subgroup G) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  symm
  apply eq_of_le_of_card_ge
  · exact le_inf (arm_le c hadj)
      (inf_le_left.trans (c.radiusTwo_second_le_stabilizer hr (by omega) β))
  · have hc := ((group c a ⊓ RankTwo.stabilizer F β).subgroupOf (group c a)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show group c a ⊓ RankTwo.stabilizer F β ≤
        group c a from inf_le_left)).toEquiv, group_card c hr hs h a ha] at hc
    change Nat.card (group c a ⊓ RankTwo.stabilizer F β : Subgroup G) *
      (group c a ⊓ RankTwo.stabilizer F β).relIndex (group c a) = 96 at hc
    rw [pointStabilizer_index c hr hs h ha hadj] at hc
    rw [arm_card c hr hs h hβ hadj]
    omega

end RadiusTwoFirstArms

private theorem local_coverage_of_neighbor_transitive
    {a b : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b) (P : Subgroup G)
    (hP : P ≤ RankTwo.stabilizer F a)
    (htrans : ∀ d, (RankTwo.graph F).Adj a d → ∃ p ∈ P, p • b = d) :
    RankTwo.stabilizer F a ≤ P ⊔ (RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b) := by
  intro g hg
  have had : (RankTwo.graph F).Adj a (g • b) := by
    have he := (translationGraphIso F g).toHom.map_adj hab
    change (RankTwo.graph F).Adj (g • a) (g • b) at he
    simpa only [show g • a = a from hg] using he
  obtain ⟨p,hp,he⟩ := htrans _ had
  have hd : p⁻¹*g ∈ RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b := by
    refine ⟨(RankTwo.stabilizer F a).mul_mem ((RankTwo.stabilizer F a).inv_mem (hP hp)) hg, ?_⟩
    change (p⁻¹*g) • b = b
    rw [mul_smul, ← he, inv_smul_smul]
  have hh := (P ⊔ (RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b)).mul_mem
    ((show P ≤ P ⊔ (RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b) from le_sup_left) hp)
    ((show RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b ≤
      P ⊔ (RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b) from le_sup_right) hd)
  simpa only [mul_inv_cancel_left] using hh

/-- Both groups constructed from the original labels exhaust their endpoint stabilizers. -/
theorem CanonicalLabelSetup.radiusTwo_source_groups_eq_stabilizers
    (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 4 ≤ s)
    (h : TwoPerfectTreeAction F) {a β : RankTwo.Vertex F}
    (ha : a.type = c.side) (hadj : (RankTwo.graph F).Adj a β) :
    c.radiusTwoFirstGroup a β = RankTwo.stabilizer F a ∧
      c.radiusTwoSecondGroup β = RankTwo.stabilizer F β := by
  have hβ : β.type ≠ c.side := by rw [←ha]; exact hadj.1.symm
  let P := RadiusTwoFirstArms.group c a
  let Q := c.radiusTwoSecondGroup β
  have hP := RadiusTwoFirstArms.group_le_stabilizer c a
  have hQ := c.radiusTwo_second_le_stabilizer hr (by omega) β
  have hPQ : P ⊓ Q = RadiusTwoFirstArms.arm c a β := by
    apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans hP)
    · exact le_inf (RadiusTwoFirstArms.arm_le c hadj) inf_le_left
  have hgen : P ⊔ Q = ⊤ := h.sup_eq_top_of_local_coverage hadj P Q
    (inf_le_left.trans (RadiusTwoFirstArms.group_normalized c h.toCubicTreeAction a))
    (inf_le_right.trans (c.radiusTwo_stabilizer_normalizes_second β))
    (local_coverage_of_neighbor_transitive hadj P hP
      (fun d hd => RadiusTwoFirstArms.group_neighbor_transitive c hr hs h.toCubicTreeAction ha hadj hd))
    (by
      rw [inf_comm]
      exact local_coverage_of_neighbor_transitive hadj.symm Q hQ
        (fun d hd => c.radiusTwo_second_neighbor_transitive hr hs h.toCubicTreeAction hβ hadj.symm hd))
  obtain ⟨heP,heQ⟩ := h.toCubicTreeAction.generated_locals_eq_stabilizers hadj P Q hP hQ
    ((RadiusTwoFirstArms.pointStabilizer_eq_arm c hr hs h.toCubicTreeAction ha hadj).trans hPQ.symm)
    hPQ.symm hgen
  exact ⟨(RadiusTwoFirstArms.group_eq_first c h.toCubicTreeAction hadj).symm.trans heP,heQ⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
