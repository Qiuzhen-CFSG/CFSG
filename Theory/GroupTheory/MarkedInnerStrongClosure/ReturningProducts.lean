module

public import Theory.GroupTheory.MarkedInnerStrongClosure.CentralTwoQuotient

/-!
# Returning ratios for a marked inner action

Returning conjugates of the original marker have a common centralizing
factor. Taking their ratio cancels it and puts the corresponding component
element in the strongly closed subgroup. Its own returning conjugates are
then controlled by strong closure, without centrality in the Sylow.

Source: the component inspection in Aschbacher--Smith, Proposition 2.2.2,
printed pp.519--520, using 1.1.5(3)(a), pp.501--503 (1 March 2004 manuscript).
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.MarkedInnerStrongClosure
variable {G K Q : Type*} [Group G] [Group K] [Group Q]

/-- A noncommuting pair occurs either in the marked class or in the class
of a ratio of two returning marked elements. -/
@[expose] def ReturningProductObstruction (P : Subgroup K) (t : K) : Prop :=
  (∃ a b : P, IsConj t (a : K) ∧ IsConj t (b : K) ∧ ¬Commute a b) ∨
  ∃ a b x y : P, IsConj t (a : K) ∧ IsConj t (b : K) ∧
    IsConj ((a : K) * (b : K)⁻¹) (x : K) ∧
    IsConj ((a : K) * (b : K)⁻¹) (y : K) ∧ ¬Commute x y

theorem ReturningProductObstruction.of_isConj {P : Subgroup K} {s t : K}
    (h : ReturningProductObstruction P s) (hts : IsConj t s) :
    ReturningProductObstruction P t := by
  rcases h with ⟨a, b, ha, hb, hab⟩ | ⟨a, b, x, y, ha, hb, hx, hy, hxy⟩
  · exact Or.inl ⟨a, b, hts.trans ha, hts.trans hb, hab⟩
  · exact Or.inr ⟨a, b, x, y, hts.trans ha, hts.trans hb, hx, hy, hxy⟩

theorem ReturningProductObstruction.map {P : Subgroup K} {t : K}
    (h : ReturningProductObstruction P t) (e : K ≃* Q) :
    ReturningProductObstruction (P.map e.toMonoidHom) (e t) := by
  let j := P.equivMapOfInjective e.toMonoidHom e.injective
  have hn (a b : P) (hab : ¬Commute a b) : ¬Commute (j a) (j b) := by
    intro hc
    apply hab
    have hh := hc.map j.symm.toMonoidHom
    change Commute (j.symm (j a)) (j.symm (j b)) at hh
    simpa only [j.symm_apply_apply] using hh
  rcases h with ⟨a, b, ha, hb, hab⟩ | ⟨a, b, x, y, ha, hb, hx, hy, hxy⟩
  · exact Or.inl ⟨j a, j b, e.toMonoidHom.map_isConj ha,
      e.toMonoidHom.map_isConj hb, hn a b hab⟩
  · refine Or.inr ⟨j a, j b, j x, j y, e.toMonoidHom.map_isConj ha,
      e.toMonoidHom.map_isConj hb, ?_, ?_, hn x y hxy⟩
    · change IsConj (e.toMonoidHom (a : K) * (e.toMonoidHom (b : K))⁻¹)
        (e.toMonoidHom (x : K))
      simpa only [map_mul, map_inv] using e.toMonoidHom.map_isConj hx
    · change IsConj (e.toMonoidHom (a : K) * (e.toMonoidHom (b : K))⁻¹)
        (e.toMonoidHom (y : K))
      simpa only [map_mul, map_inv] using e.toMonoidHom.map_isConj hy

/-- Cancellation of the common factor uses ratios, with no condition on
the order or membership in U of that factor. -/
theorem returning_ratio_mem
    (S U : Subgroup G) (hU : IsStronglyClosedSet (U : Set G) S ⊤)
    (f : K →* G) (P : Subgroup K) (hPS : P.map f ≤ S)
    (z : G) (hzU : z ∈ U) (t : K) (htP : t ∈ P)
    (haction : ∀ x : K, f (t * x * t⁻¹) = z * f x * z⁻¹)
    (a b : K) (haP : a ∈ P) (hbP : b ∈ P)
    (ha : IsConj t a) (hb : IsConj t b) : f (a * b⁻¹) ∈ U := by
  let c : G := (f t)⁻¹ * z
  have hcS : c ∈ S :=
    S.mul_mem (S.inv_mem (hPS (mem_map_of_mem f htP))) (hU.1 hzU)
  have hcf (x : K) : Commute c (f x) := by
    apply mul_inv_eq_iff_eq_mul.mp
    change ((f t)⁻¹ * z) * f x * ((f t)⁻¹ * z)⁻¹ = f x
    calc
      _ = (f t)⁻¹ * (z * f x * z⁻¹) * f t := by group
      _ = (f t)⁻¹ * f (t * x * t⁻¹) * f t := by rw [haction]
      _ = f x := by simp only [map_mul, map_inv]; group
  have hz : z = f t * c := by dsimp [c]; group
  have hforced (a : K) (haP : a ∈ P) (ha : IsConj t a) : f a * c ∈ U := by
    obtain ⟨g, hg⟩ := isConj_iff.mp ha
    have he : f g * z * (f g)⁻¹ = f a * c := by
      rw [hz]
      calc
        _ = f g * f t * (c * (f g)⁻¹) := by group
        _ = f g * f t * ((f g)⁻¹ * c) := by rw [(hcf g).inv_right.eq]
        _ = f (g * t * g⁻¹) * c := by simp only [map_mul, map_inv]; group
        _ = f a * c := by rw [hg]
    have hs : f a * c ∈ S := S.mul_mem (hPS (mem_map_of_mem f haP)) hcS
    have hu := hU.2 z hzU (f g)⁻¹ (mem_top _)
      (by simpa only [inv_inv, he] using hs)
    change f a * c ∈ (U : Set G)
    simpa only [inv_inv, he] using hu
  have hu := U.mul_mem (hforced a haP ha) (U.inv_mem (hforced b hbP hb))
  have he : (f a * c) * (f b * c)⁻¹ = f (a * b⁻¹) := by
    simp only [map_mul, map_inv]
    group
  rwa [he] at hu

/-- The second-stage marker already belongs to U, so ordinary strong
closure applies to it without a Sylow-centrality requirement. -/
theorem false_of_returning_product_obstruction
    (S U : Subgroup G) [IsMulCommutative U]
    (hU : IsStronglyClosedSet (U : Set G) S ⊤)
    (f : K →* G) (hf : Function.Injective f)
    (P : Subgroup K) (hPS : P.map f ≤ S)
    (z : G) (hzU : z ∈ U) (t : K) (htP : t ∈ P)
    (haction : ∀ x : K, f (t * x * t⁻¹) = z * f x * z⁻¹)
    (h : ReturningProductObstruction P t) : False := by
  rcases h with ⟨a, b, ha, hb, hab⟩ | ⟨a, b, x, y, ha, hb, hx, hy, hxy⟩
  · exact hab (Subtype.ext (conjugates_commute_of_implementer_mem S U hU f hf P
      hPS z hzU t htP haction a b a.property b.property ha hb).eq)
  · have hd := returning_ratio_mem S U hU f P hPS z hzU t htP haction
      a b a.property b.property ha hb
    have hreturn (x : P) (hx : IsConj ((a : K) * (b : K)⁻¹) (x : K)) :
        f (x : K) ∈ U := by
      obtain ⟨g, hg⟩ := isConj_iff.mp hx
      have he : f g * f ((a : K) * (b : K)⁻¹) * (f g)⁻¹ = f (x : K) := by
        rw [← map_inv, ← map_mul, ← map_mul, hg]
      have hu := hU.2 _ hd (f g)⁻¹ (mem_top _)
        (by simpa only [inv_inv, he] using hPS (mem_map_of_mem f x.property))
      change f (x : K) ∈ (U : Set G)
      simpa only [inv_inv, he] using hu
    have hc := congrArg Subtype.val
      (mul_comm (⟨f (x : K), hreturn x hx⟩ : U) ⟨f (y : K), hreturn y hy⟩)
    change f (x : K) * f (y : K) = f (y : K) * f (x : K) at hc
    apply hxy
    apply Subtype.ext
    apply hf
    change f ((x : K) * (y : K)) = f ((y : K) * (x : K))
    simpa only [map_mul] using hc

end Theory.GroupTheory.MarkedInnerStrongClosure
