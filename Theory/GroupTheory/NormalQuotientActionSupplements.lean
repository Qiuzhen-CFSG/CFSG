module

public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect actors and simultaneous quotient kernels

Solvability of the actual outer automorphism group makes a perfect actor's
quotient action inner. Lifting an inner implementer gives a supplement by
the normal subgroup. A finite adjustment argument combines these supplements
when each correcting factor lies in every other kernel.

Source application: Aschbacher--Smith, Proposition A.3.9(1), printed p.46.
The kernel may be any characteristic subgroup; in particular it may be the
solvable radical, without an ordinary-cover classification.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- A perfect actor induces only inner automorphisms on a quotient with solvable outer group. -/
theorem sup_normalQuotientAction_ker_eq_top_of_perfect [Group.IsPerfect G] (L : Subgroup G) [L.Normal]
    (N : Subgroup L) [N.Characteristic] [Group.IsSolvable (MulAut.Outer (L ⧸ N))] :
    L ⊔ (normalQuotientAction L N).ker = ⊤ := by
  let Q := L ⧸ N
  let a := normalQuotientAction L N
  let f : G →* MulAut.Outer Q := (QuotientGroup.mk' (MulAut.innerSubgroup Q)).comp a
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  have hf (g : G) : f g = 1 := congrArg f.range.subtype
    (hs.elim (⟨f g, ⟨g, rfl⟩⟩ : f.range) 1)
  apply top_unique
  intro g _
  have hi : a g ∈ MulAut.innerSubgroup Q := (QuotientGroup.eq_one_iff _).mp (hf g)
  obtain ⟨q, hq⟩ := hi
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective N q
  have hl : a (l : G) = a g := (normalQuotientAction_inner L N l).trans hq
  have hk : (l : G)⁻¹ * g ∈ a.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hl, inv_mul_cancel]
  have hm := (L ⊔ a.ker).mul_mem (mem_sup_left l.property) (mem_sup_right hk)
  simpa only [mul_inv_cancel_left] using hm

/-- Pointwise centralization of the subgroup fixes every characteristic quotient. -/
theorem centralizer_le_normalQuotientAction_ker (L : Subgroup G) [L.Normal] (N : Subgroup L) [N.Characteristic] :
    centralizer (L : Set G) ≤ (normalQuotientAction L N).ker := by
  intro g hg
  apply MulEquiv.ext
  intro q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective N q
  rw [normalQuotientAction_apply_mk]
  change QuotientGroup.mk' N (MulAut.conjNormal g l) = QuotientGroup.mk' N l
  congr 1
  apply Subtype.ext
  change g * (l : G) * g⁻¹ = (l : G)
  rw [← hg l l.property, mul_inv_cancel_right]

/-- If the subgroup itself fixes its quotient, that quotient is abelian. -/
theorem isMulCommutative_of_le_normalQuotientAction_ker (L : Subgroup G) [L.Normal] (N : Subgroup L) [N.Characteristic]
    (h : L ≤ (normalQuotientAction L N).ker) : IsMulCommutative (L ⧸ N) := by
  apply center_eq_top_iff.mp
  apply top_unique
  intro q _
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective N q
  have he : MulAut.conj (QuotientGroup.mk' N l) = 1 :=
    (normalQuotientAction_inner L N l).symm.trans (h l.property)
  apply mem_center_iff.mpr
  intro r
  have hx := congrArg (fun a : MulAut (L ⧸ N) => a r) he
  change QuotientGroup.mk' N l * r * (QuotientGroup.mk' N l)⁻¹ = r at hx
  exact (mul_inv_eq_iff_eq_mul.mp hx).symm

/-- Successive adjustment by independent supplements puts every element in the common kernel modulo H. -/
theorem sup_iInf_eq_top_of_independent_supplements {ι : Type*} [Finite ι] (L C : ι → Subgroup G)
    (hCN : ∀ i, (C i).Normal) (hgen : ∀ i, L i ⊔ C i = ⊤)
    (hcross : ∀ i j, i ≠ j → L i ≤ C j) (H : Subgroup G) (hle : ∀ i, L i ≤ H) :
    H ⊔ (⨅ i, C i) = ⊤ := by
  classical
  let _ := Fintype.ofFinite ι
  have aux (s : Finset ι) (g : G) :
      ∃ h ∈ H, ∃ c : G, (∀ i ∈ s, c ∈ C i) ∧ h * c = g := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, H.one_mem, g, by simp, one_mul g⟩
    | @insert i s hi ih =>
      obtain ⟨h, hh, c, hc, he⟩ := ih
      let := hCN i
      have hci : c ∈ L i ⊔ C i := by rw [hgen]; trivial
      obtain ⟨l, hl, d, hd, hld⟩ := mem_sup_of_normal_right.mp hci
      refine ⟨h * l, H.mul_mem hh (hle i hl), d, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hd
        · have hlj : l ∈ C j := hcross i j (fun e => hi (e ▸ hj)) hl
          have hh := (C j).mul_mem ((C j).inv_mem hlj) (hc j hj)
          simpa only [← hld, inv_mul_cancel_left] using hh
      · rw [mul_assoc, hld, he]
  apply top_unique
  intro g _
  obtain ⟨h, hh, c, hc, rfl⟩ := aux Finset.univ g
  exact (H ⊔ ⨅ i, C i).mul_mem (mem_sup_left hh)
    (mem_sup_right (mem_iInf.mpr (fun i => hc i (Finset.mem_univ i))))
end Subgroup
