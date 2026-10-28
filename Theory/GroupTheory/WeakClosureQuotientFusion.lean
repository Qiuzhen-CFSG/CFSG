module
public import Theory.GroupTheory.WeakClosureSetFusion
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Weak closure and fusion after quotienting a contained subgroup

The Sylow correction can be performed inside any prescribed overgroup
containing both conjugates of a weakly closed subgroup. Applied inside the
image of an embedding, this gives fusion control in that image. If a normal
quotient kernel lies in an abelian weakly closed subgroup, a quotient
conjugacy lifts to a conjugacy back into that subgroup, so the same
correction controls fusion in its quotient image without discarding the
kernel.

Source: the Burnside fusion argument, Aschbacher–Smith A.1.35, and its
line-normalizer quotient application in F.4.42, printed pp.30,295.
-/

public section
open Subgroup
namespace Sylow.WeakClosure
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
private theorem exists_conj_map_le (P : Sylow p G) {H : Subgroup G}
    (hH : IsPGroup p H) : ∃ g : G, H.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g, ?_⟩
  rw [← hg]
  exact map_mono hQ

theorem normalizer_correction
    (P : Sylow p G) (W : Subgroup G)
    (hWP : W ≤ (P : Subgroup G))
    (hweak : ∀ g : G, W.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      g ∈ normalizer (W : Set G))
    (H : Subgroup G) (hWH : W ≤ H) (g : G)
    (hgWH : W.map (MulAut.conj g).toMonoidHom ≤ H) :
    ∃ c : H, (c : G) * g ∈ normalizer (W : Set G) := by
  let V := W.map (MulAut.conj g).toMonoidHom
  have hW : IsPGroup p W := P.isPGroup'.to_le hWP
  obtain ⟨Q, hQ⟩ := (hW.comap_subtype (K := H)).exists_le_sylow
  obtain ⟨c, hc⟩ := exists_conj_map_le Q
    ((hW.map (MulAut.conj g).toMonoidHom).comap_subtype (K := H))
  obtain ⟨k, hk⟩ := exists_conj_map_le P (Q.isPGroup'.map H.subtype)
  have hkW : k ∈ normalizer (W : Set G) := by
    apply hweak
    rintro _ ⟨w, hw, rfl⟩
    apply hk
    exact mem_map_of_mem _ ⟨⟨w, hWH hw⟩, hQ hw, rfl⟩
  have hkcgW : k * (c : G) * g ∈ normalizer (W : Set G) := by
    apply hweak
    rintro _ ⟨w, hw, rfl⟩
    have hwV : MulAut.conj g w ∈ V := mem_map_of_mem _ hw
    have hcQ := hc (mem_map_of_mem (MulAut.conj c).toMonoidHom
      (show (⟨MulAut.conj g w, hgWH hwV⟩ : H) ∈ V.subgroupOf H from hwV))
    have hkP := hk (mem_map_of_mem (MulAut.conj k).toMonoidHom
      (mem_map_of_mem H.subtype hcQ))
    change k * (↑c * (g * w * g⁻¹) * (↑c)⁻¹) * k⁻¹ ∈ (P : Subgroup G) at hkP
    change (k * ↑c * g) * w * (k * ↑c * g)⁻¹ ∈ (P : Subgroup G)
    simpa only [mul_inv_rev, mul_assoc] using hkP
  refine ⟨c, ?_⟩
  have := (normalizer (W : Set G)).mul_mem
    ((normalizer (W : Set G)).inv_mem hkW) hkcgW
  simpa only [← mul_assoc, inv_mul_cancel, one_mul] using this


/-- Fusion inside an embedded overgroup is controlled by its intersection
with the ambient normalizer of the weakly closed subgroup. -/
theorem embedding_fusion
    (P : Sylow p G) (Q : Subgroup G)
    (hQP : Q ≤ (P : Subgroup G))
    (hweak : ∀ g : G, Q.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      g ∈ normalizer (Q : Set G))
    {N : Type*} [Group N] (j : N →* G) (hj : Function.Injective j)
    (hQj : Q ≤ j.range) {x y : N}
    (hx : j x ∈ centralizer (Q : Set G))
    (hy : j y ∈ centralizer (Q : Set G))
    (g : N) (he : g*x*g⁻¹ = y) :
    ∃ a : N, j a ∈ normalizer (Q : Set G) ∧ a*x*a⁻¹ = y := by
  let C := j.range ⊓ centralizer ({j y} : Set G)
  have hQC : Q ≤ C := fun q hq =>
    ⟨hQj hq,mem_centralizer_singleton_iff.mpr (hy q hq)⟩
  have hjg : j g * j x * (j g)⁻¹ = j y := by rw [←map_inv,←map_mul,←map_mul,he]
  have hgQC : Q.map (MulAut.conj (j g)).toMonoidHom ≤ C := by
    rintro _ ⟨q,hq,rfl⟩
    refine ⟨j.range.mul_mem (j.range.mul_mem ⟨g,rfl⟩ (hQj hq))
      (j.range.inv_mem ⟨g,rfl⟩),?_⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (MulAut.conj (j g)) (hx q hq)
    change (j g*q*(j g)⁻¹)*j y = j y*(j g*q*(j g)⁻¹)
    simpa only [map_mul,MulAut.conj_apply,hjg] using hh
  obtain ⟨c,hc⟩ := normalizer_correction P Q hQP hweak C hQC (j g) hgQC
  obtain ⟨b,hb⟩ := c.property.1
  refine ⟨b*g,by simpa only [map_mul,hb] using hc,?_⟩
  apply hj
  simp only [map_mul,map_inv,hb]
  calc
    _ = c.val * (j g * j x * (j g)⁻¹) * c.val⁻¹ := by group
    _ = j y := by
      rw [hjg]
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp c.property.2)

/-- The original normal quotient kernel is retained when correcting fusion. -/
theorem quotient_fusion
    (P : Sylow p G) (Q : Subgroup G)
    (hQP : Q ≤ (P : Subgroup G))
    (hweak : ∀ g : G, Q.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      g ∈ normalizer (Q : Set G))
    (habel : Q ≤ centralizer (Q : Set G))
    {N : Type*} [Group N] (j : N →* G) (hj : Function.Injective j)
    (hQj : Q ≤ j.range) (U : Subgroup N) [U.Normal] (hU : U.map j ≤ Q)
    {x y : N ⧸ U}
    (hx : x ∈ (Q.comap j).map (QuotientGroup.mk' U))
    (hy : y ∈ (Q.comap j).map (QuotientGroup.mk' U))
    (hxy : IsConj x y) :
    ∃ a : N, j a ∈ normalizer (Q : Set G) ∧
      QuotientGroup.mk' U a * x * (QuotientGroup.mk' U a)⁻¹ = y := by
  obtain ⟨v,hv,rfl⟩ := hx
  obtain ⟨w,hw,rfl⟩ := hy
  obtain ⟨g,hg⟩ := isConj_iff.mp hxy
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective U g
  have he : QuotientGroup.mk' U (b*v*b⁻¹) = QuotientGroup.mk' U w := by
    simpa only [map_mul,map_inv] using hg
  have hk : w⁻¹ * (b*v*b⁻¹) ∈ U := by
    simpa only [mul_inv_rev,inv_inv] using U.inv_mem (QuotientGroup.eq.mp he)
  have ht : j (b*v*b⁻¹) ∈ Q := by
    have h := Q.mul_mem hw (hU (mem_map_of_mem j hk))
    simpa only [map_mul,map_inv,mul_inv_cancel_left] using h
  obtain ⟨a,ha,hea⟩ := embedding_fusion P Q hQP hweak j hj hQj
    (habel hv) (habel ht) b rfl
  refine ⟨a,ha,?_⟩
  rw [←map_inv,←map_mul,←map_mul,hea]
  exact he

/-- Simultaneous fusion of an arbitrary set in an embedded overgroup. -/
theorem embedding_set_fusion
    (P : Sylow p G) (Q : Subgroup G)
    (hQP : Q ≤ (P : Subgroup G))
    (hweak : ∀ g : G, Q.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      g ∈ normalizer (Q : Set G))
    {N : Type*} [Group N] (j : N →* G) (hj : Function.Injective j)
    (hQj : Q ≤ j.range) (s : Set N) (g : N)
    (hs : ∀ x ∈ s, j x ∈ centralizer (Q : Set G))
    (hgs : ∀ x ∈ s, j (g*x*g⁻¹) ∈ centralizer (Q : Set G)) :
    ∃ a : N, j a ∈ normalizer (Q : Set G) ∧
      ∀ x ∈ s, a*x*a⁻¹ = g*x*g⁻¹ := by
  let Y := (fun x => j (g*x*g⁻¹)) '' s
  let C := j.range ⊓ centralizer Y
  have hQC : Q ≤ C := by
    intro q hq
    refine ⟨hQj hq,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact (hgs x hx q hq).symm
  have hgQC : Q.map (MulAut.conj (j g)).toMonoidHom ≤ C := by
    rintro _ ⟨q,hq,rfl⟩
    refine ⟨j.range.mul_mem (j.range.mul_mem ⟨g,rfl⟩ (hQj hq))
      (j.range.inv_mem ⟨g,rfl⟩),?_⟩
    rintro _ ⟨x,hx,rfl⟩
    change j (g*x*g⁻¹) * (j g*q*(j g)⁻¹) =
      (j g*q*(j g)⁻¹) * j (g*x*g⁻¹)
    have hh := congrArg (MulAut.conj (j g)) (hs x hx q hq).symm
    simpa only [map_mul,map_inv,MulAut.conj_apply] using hh
  obtain ⟨c,hc⟩ := normalizer_correction P Q hQP hweak C hQC (j g) hgQC
  obtain ⟨b,hb⟩ := c.property.1
  refine ⟨b*g,by simpa only [map_mul,hb] using hc,?_⟩
  intro x hx
  apply hj
  have hcomm := c.property.2 (j (g*x*g⁻¹)) ⟨x,hx,rfl⟩
  calc
    j ((b*g)*x*(b*g)⁻¹) = c.val * j (g*x*g⁻¹) * c.val⁻¹ := by
      simp only [map_mul,map_inv,hb]
      group
    _ = j (g*x*g⁻¹) := mul_inv_eq_iff_eq_mul.mpr hcomm.symm

/-- Pointwise fusion of every subset of the actual quotient image is
controlled by the embedded normalizer. This retains all elements and
relations at once, rather than merely its individual conjugacy classes. -/
theorem quotient_set_fusion
    (P : Sylow p G) (Q : Subgroup G)
    (hQP : Q ≤ (P : Subgroup G))
    (hweak : ∀ g : G, Q.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      g ∈ normalizer (Q : Set G))
    (habel : Q ≤ centralizer (Q : Set G))
    {N : Type*} [Group N] (j : N →* G) (hj : Function.Injective j)
    (hQj : Q ≤ j.range) (U : Subgroup N) [U.Normal] (hU : U.map j ≤ Q)
    (s : Set (N ⧸ U))
    (hs : s ⊆ (Q.comap j).map (QuotientGroup.mk' U))
    (g : N ⧸ U)
    (hgs : ∀ x ∈ s, g*x*g⁻¹ ∈ (Q.comap j).map (QuotientGroup.mk' U)) :
    ∃ a : N, j a ∈ normalizer (Q : Set G) ∧
      ∀ x ∈ s, QuotientGroup.mk' U a*x*(QuotientGroup.mk' U a)⁻¹ = g*x*g⁻¹ := by
  let q := QuotientGroup.mk' U
  have hpre (v : N) (hv : q v ∈ (Q.comap j).map q) : j v ∈ Q := by
    obtain ⟨w,hw,he⟩ := hv
    have hk : w⁻¹*v ∈ U := QuotientGroup.eq.mp he
    have h := Q.mul_mem hw (hU (mem_map_of_mem j hk))
    simpa only [map_mul,map_inv,mul_inv_cancel_left] using h
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective U g
  obtain ⟨a,ha,he⟩ := embedding_set_fusion P Q hQP hweak j hj hQj
    (q ⁻¹' s) b (fun x hx => habel (hpre x (hs hx))) (by
      intro x hx
      apply habel
      apply hpre
      simpa only [map_mul,map_inv] using hgs (q x) hx)
  refine ⟨a,ha,?_⟩
  intro x hx
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective U x
  simpa only [map_mul,map_inv] using congrArg q (he v hx)

end Sylow.WeakClosure
