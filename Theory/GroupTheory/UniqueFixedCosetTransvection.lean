module
public import Theory.GroupTheory.StronglyClosedTIFour
public import Theory.GroupTheory.UniqueFixedCosetCommutingProducts

/-!
# An isolated elementary subgroup with a binary transvection

Unique fixed cosets make a normal elementary subgroup TI and strongly
closed. Inside an involution centralizer, the elementary TI transitivity
lemma then forces transitivity on its fixed subgroup unless the centralizer
stays in the original normalizer. A nontrivial displacement line prevents
that transitivity. The same obstruction applies after multiplying the
involution by a commuting element of the elementary subgroup. Fusion
control and the two-class commuting-product lemma force the normalizer to
be the whole group.

This is the transvection case of Aschbacher, *Sporadic Groups* (1994),
Exercise 2.7, p.33, used in Lemma 39.9, p.216. The actual marked-root
application is in `TransvectionFive.CoreFusionNormality`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace UniqueFixedCoset
variable {G : Type*} [Group G] [Finite G]

/-- Two fixed elements which cannot be fused by the local centralizer exclude an escaping centralizer. -/
theorem centralizer_le_of_fixed_pair (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hu : ∀ a ∈ A, a ≠ 1 → ∃! q : G ⧸ normalizer (A : Set G), a • q = q)
    (b z e : G) (hzA : z ∈ A) (heA : e ∈ A) (hz1 : z ≠ 1) (he1 : e ≠ 1)
    (hze : z ≠ e) (hzb : Commute z b) (heb : Commute e b)
    (hfix : ∀ g ∈ normalizer (A : Set G), Commute g b → Commute g z) :
    centralizer ({b} : Set G) ≤ normalizer (A : Set G) := by
  let C := centralizer ({b} : Set G)
  let D := A.subgroupOf C
  let zC : C := ⟨z,mem_centralizer_singleton_iff.mpr hzb.eq⟩
  let eC : C := ⟨e,mem_centralizer_singleton_iff.mpr heb.eq⟩
  let : IsElementaryAbelian 2 D := {
    toIsMulCommutative := Subgroup.subgroupOf_isMulCommutative C A
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      apply Subtype.ext
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian ((x : C) : G) x.property) }
  have htrans (g : G) (x : G) (hx : x ∈ A) (hx1 : x ≠ 1)
      (hg : g*x*g⁻¹ ∈ normalizer (A : Set G)) : g ∈ normalizer (A : Set G) :=
    transporter_mem (A.le_normalizer hx) (hu x hx hx1) hg
  have hn (g : C) (hg : g ∈ normalizer (D : Set C)) : (g:G) ∈ normalizer (A : Set G) := by
    apply htrans g z hzA hz1
    exact A.le_normalizer ((mem_normalizer_iff.mp hg zC).mp hzA)
  have hti (g x : C) (hx : x ∈ D) (hx1 : x ≠ 1) (hgx : g*x*g⁻¹ ∈ D) :
      g ∈ normalizer (D : Set C) := by
    have hg := htrans g x hx (fun h => hx1 (Subtype.ext h)) (A.le_normalizer hgx)
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp hg (a:G)
  have hs : IsStronglyClosedSet (D : Set C) (normalizer (D : Set C)) ⊤ := by
    refine ⟨D.le_normalizer,?_⟩
    intro x hx g _ hgx
    by_cases hx1 : x = 1
    · simp [hx1]
    have hg := htrans (g:G)⁻¹ x hx (fun h => hx1 (Subtype.ext h))
      (by simpa only [Subgroup.coe_mul,Subgroup.coe_inv,inv_inv] using hn _ hgx)
    change (g:G)⁻¹ * (x:G) * (g:G) ∈ A
    simpa only [inv_inv] using (mem_normalizer_iff.mp hg (x:G)).mp hx
  by_contra hle
  have hp : normalizer (D : Set C) ≠ ⊤ := by
    intro heq
    apply hle
    intro g hg
    exact hn ⟨g,hg⟩ (heq ▸ mem_top _)
  obtain ⟨g,hg,hge⟩ := ti_stronglyClosed_normalizer_transitive D inferInstance hti hs hp
    (e := zC) hzA (fun h => hz1 (congrArg Subtype.val h))
    (f := eC) heA (fun h => he1 (congrArg Subtype.val h))
  have hc := hfix g (hn g hg) (mem_centralizer_singleton_iff.mp g.property)
  have he := congrArg Subtype.val hge
  change (g:G)*z*(g:G)⁻¹ = e at he
  rw [hc.eq,mul_inv_cancel_right] at he
  exact hze he

end UniqueFixedCoset

namespace UniqueFixedCoset
variable {G : Type*} [Group G] [Finite G]

/-- The commuting-product criterion with the actual transvection coset and literal fusion control. -/
theorem normalizer_eq_top_of_transvection (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hu : ∀ a ∈ A, a ≠ 1 → ∃! q : G ⧸ normalizer (A : Set G), a • q = q)
    (z t : G) (hzA : z ∈ A) (hz1 : z ≠ 1)
    (htM : t ∈ normalizer (A : Set G)) (htA : t ∉ A) (hto : orderOf t = 2)
    (hfus : ∀ y ∈ normalizer (A : Set G), IsConj t y →
      ∃ m ∈ normalizer (A : Set G), m*t*m⁻¹ = y)
    (hcentral : ∀ a ∈ A, Commute a t →
      centralizer ({a*t} : Set G) ≤ normalizer (A : Set G)) :
    normalizer (A : Set G) = ⊤ := by
  let M := normalizer (A : Set G)
  have htC : centralizer ({t} : Set G) ≤ M := by
    simpa only [one_mul] using hcentral 1 A.one_mem (Commute.one_left t)
  have hut : ∃! q : G ⧸ M, t • q = q :=
    unique_of_fusion_and_centralizer htM htC (by
      intro g hg
      obtain ⟨m,hm,he⟩ := hfus _ hg (isConj_iff.mpr ⟨g,rfl⟩)
      exact ⟨m,hm,he.symm⟩)
  have hz2 : orderOf z = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian z hzA) hz1
  have memA {x : G} (hx : x ∈ M) (h : IsConj z x) : x ∈ A := by
    obtain ⟨g,hg⟩ := isConj_iff.mp h
    have hgM := transporter_mem (A.le_normalizer hzA) (hu z hzA hz1) (hg.symm ▸ hx)
    exact hg ▸ (mem_normalizer_iff.mp hgM z).mp hzA
  apply eq_top_of_commuting_products M ⟨z,A.le_normalizer hzA⟩ ⟨t,htM⟩
    (by simpa only [Subgroup.orderOf_mk] using hz2)
    (by simpa only [Subgroup.orderOf_mk] using hto)
    (fun h => htA (memA htM h))
  · intro x hx
    exact hx.elim (unique_of_isConj (hu z hzA hz1)) (unique_of_isConj hut)
  · intro x y hx hy hxy hcomm
    have hxA := memA x.property hx
    rcases hy with hy | hy
    · have hyA := memA y.property hy
      have hp : (x:G)*(y:G) ∈ A := A.mul_mem hxA hyA
      have hp1 : (x:G)*(y:G) ≠ 1 := by
        intro he
        apply hxy
        apply Subtype.ext
        have hx2 : (x:G)*(x:G) = 1 := by
          simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (x:G) hxA
        exact mul_left_cancel (hx2.trans he.symm)
      exact centralizer_le_of_unique (x*y).property (hu _ hp hp1)
    · obtain ⟨m,hm,hmy⟩ := hfus y y.property hy
      let a := m⁻¹*(x:G)*m
      have ha : a ∈ A := by
        simpa only [inv_inv] using (mem_normalizer_iff.mp (M.inv_mem hm) (x:G)).mp hxA
      have hat : Commute a t := by
        apply (commute_iff_eq _ _).mpr
        have hc := congrArg (MulAut.conj m⁻¹)
          (show (x:G)*(y:G) = (y:G)*(x:G) from congrArg Subtype.val hcomm.eq)
        have hyt : m⁻¹*(y:G)*m = t := by rw [← hmy]; group
        simpa only [map_mul,MulAut.conj_apply,inv_inv,hyt] using hc
      intro c hc
      have hc' : m⁻¹*c*m ∈ centralizer ({a*t} : Set G) := by
        apply mem_centralizer_singleton_iff.mpr
        have hh := congrArg (MulAut.conj m⁻¹) (mem_centralizer_singleton_iff.mp hc)
        have hyt : m⁻¹*(y:G)*m = t := by rw [← hmy]; group
        simpa only [map_mul,MulAut.conj_apply,inv_inv,Subgroup.coe_mul,hyt] using hh
      have hm' := hcentral a ha hat hc'
      have hh := M.mul_mem (M.mul_mem hm hm') (M.inv_mem hm)
      simpa only [a, mul_assoc,mul_inv_cancel,inv_mul_cancel,mul_one,one_mul,mul_inv_cancel_left] using hh
end UniqueFixedCoset

namespace UniqueFixedCoset
variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial binary displacement line forces the required local centralizer obstruction. -/
theorem centralizer_le_of_binary_displacement (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hu : ∀ a ∈ A, a ≠ 1 → ∃! q : G ⧸ normalizer (A : Set G), a • q = q)
    (b z e : G) (hzA : z ∈ A) (heA : e ∈ A) (hz1 : z ≠ 1) (he1 : e ≠ 1)
    (hze : z ≠ e) (hzb : Commute z b) (heb : Commute e b)
    (hd : ∀ x ∈ A, b*x*b⁻¹*x⁻¹ = 1 ∨ b*x*b⁻¹*x⁻¹ = z)
    (hr : ∃ r ∈ A, b*r*b⁻¹*r⁻¹ = z) :
    centralizer ({b} : Set G) ≤ normalizer (A : Set G) := by
  apply centralizer_le_of_fixed_pair A hu b z e hzA heA hz1 he1 hze hzb heb
  intro g hg hgb
  obtain ⟨r,hrA,hrz⟩ := hr
  have hgrA := (mem_normalizer_iff.mp hg r).mp hrA
  have hgb' : MulAut.conj g b = b := mul_inv_eq_iff_eq_mul.mpr hgb.eq
  have he : MulAut.conj g z = b*(MulAut.conj g r)*b⁻¹*(MulAut.conj g r)⁻¹ := by
    rw [← hrz]
    simp only [map_mul,map_inv,hgb']
  have hgz : MulAut.conj g z = z := by
    rcases hd _ hgrA with h | h
    · exact (hz1 ((MulAut.conj g).map_eq_one_iff.mp (he.trans h))).elim
    · exact he.trans h
  exact mul_inv_eq_iff_eq_mul.mp hgz

/-- A transvection with at least two nonzero fixed points rules out a proper normalizer under unique fixed cosets and fusion control. -/
theorem normalizer_eq_top_of_binary_displacement (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hu : ∀ a ∈ A, a ≠ 1 → ∃! q : G ⧸ normalizer (A : Set G), a • q = q)
    (z t e : G) (hzA : z ∈ A) (heA : e ∈ A) (hz1 : z ≠ 1) (he1 : e ≠ 1)
    (hze : z ≠ e) (hzt : Commute z t) (het : Commute e t)
    (htM : t ∈ normalizer (A : Set G)) (htA : t ∉ A) (hto : orderOf t = 2)
    (hfus : ∀ y ∈ normalizer (A : Set G), IsConj t y →
      ∃ m ∈ normalizer (A : Set G), m*t*m⁻¹ = y)
    (hd : ∀ x ∈ A, t*x*t⁻¹*x⁻¹ = 1 ∨ t*x*t⁻¹*x⁻¹ = z)
    (hr : ∃ r ∈ A, t*r*t⁻¹*r⁻¹ = z) :
    normalizer (A : Set G) = ⊤ := by
  apply normalizer_eq_top_of_transvection A hu z t hzA hz1 htM htA hto hfus
  intro a ha _
  have hcomm (x : G) (hx : x ∈ A) : Commute x a := setLike_mul_comm hx ha
  have hab (x : G) (hx : x ∈ A) : (a*t)*x*(a*t)⁻¹*x⁻¹ = t*x*t⁻¹*x⁻¹ := by
    have hc := hcomm (t*x*t⁻¹) ((mem_normalizer_iff.mp htM x).mp hx)
    calc
      _ = (a*(t*x*t⁻¹)*a⁻¹)*x⁻¹ := by group
      _ = _ := by rw [hc.symm.eq,mul_inv_cancel_right]
  apply centralizer_le_of_binary_displacement A hu (a*t) z e hzA heA hz1 he1 hze
    ((hcomm z hzA).mul_right hzt) ((hcomm e heA).mul_right het)
  · intro x hx
    rw [hab x hx]
    exact hd x hx
  · obtain ⟨r,hrA,hrz⟩ := hr
    exact ⟨r,hrA,(hab r hrA).trans hrz⟩
end UniqueFixedCoset
