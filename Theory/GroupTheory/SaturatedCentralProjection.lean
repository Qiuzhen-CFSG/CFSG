module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Sylow

/-!
# Component projections under p-subgroup saturation

Let D be normal and let Z(D) be a p-group. The inverse image in D of
the image of a p-subgroup Q in G/C_G(D) is again a p-group: its kernel
is exactly Z(D). If every A-invariant p-subgroup lies in Q, this inverse
image equals D intersect Q. This retains the central overlap and does
not require an unjustified projection from D C_G(D) onto D.

Source application: Aschbacher--Smith 2.5.3(3--4), printed pp.552--553.
-/

public section
namespace Theory.GroupTheory
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] {p : ℕ}

/-- The actual centralizer-quotient inverse image is a p-group. -/
theorem isPGroup_inf_sup_centralizer (D Q : Subgroup G) [D.Normal]
    (hZ : IsPGroup p (center D)) (hQ : IsPGroup p Q) :
    IsPGroup p (D ⊓ (Q ⊔ centralizer (D : Set G)) : Subgroup G) := by
  let C := centralizer (D : Set G)
  let q := QuotientGroup.mk' C
  let f := q.comp D.subtype
  have hk : f.ker = center D := by
    ext d
    change ((d : G) : G ⧸ C) = 1 ↔ d ∈ center D
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hd
      exact mem_center_iff.mpr fun x => Subtype.ext (hd x x.property)
    · intro hd x hx
      exact congrArg Subtype.val (mem_center_iff.mp hd ⟨x, hx⟩)
  have hp := (hQ.map q).comap_of_ker_isPGroup f (hk ▸ hZ)
  have he : ((Q.map q).comap f).map D.subtype =
      D ⊓ (Q ⊔ C) := by
    change (((Q.map q).comap q).comap D.subtype).map D.subtype = _
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    ext x
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨d.property, hd⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  rw [← he]
  exact hp.map D.subtype

/-- Saturation identifies the centralizer-quotient projection with the
literal intersection in the original group. -/
theorem inf_sup_centralizer_eq_inf_of_saturation (D A Q : Subgroup G) [D.Normal]
    (hZ : IsPGroup p (center D)) (hQ : IsPGroup p Q)
    (hAQ : A ≤ normalizer (Q : Set G))
    (hsat : ∀ P : Subgroup G, IsPGroup p P →
      A ≤ normalizer (P : Set G) → P ≤ Q) :
    D ⊓ (Q ⊔ centralizer (D : Set G)) = D ⊓ Q := by
  have hn : A ≤ normalizer ((D ⊓ (Q ⊔ centralizer (D : Set G)) : Subgroup G) : Set G) :=
    (le_inf le_normalizer_of_normal
      (hAQ.trans normalizer_le_normalizer_sup_normal)).trans
      inf_normalizer_le_normalizer_inf
  exact le_antisymm (le_inf inf_le_left
    (hsat _ (isPGroup_inf_sup_centralizer D Q hZ hQ) hn))
    (inf_le_inf_left D le_sup_left)

/-- An inner nontrivial action of a marked element of Q gives a
noncentral element of the actual component intersection D intersect Q. -/
theorem exists_noncentral_mem_inf_of_saturation (D A Q : Subgroup G) [D.Normal]
    (hZ : IsPGroup p (center D)) (hQ : IsPGroup p Q)
    (hAQ : A ≤ normalizer (Q : Set G))
    (hsat : ∀ P : Subgroup G, IsPGroup p P →
      A ≤ normalizer (P : Set G) → P ≤ Q)
    {z : G} (hzQ : z ∈ Q)
    (hzinner : z ∈ D ⊔ centralizer (D : Set G))
    (hznc : z ∉ centralizer (D : Set G)) :
    ∃ d ∈ D ⊓ Q, d ∉ centralizer (D : Set G) := by
  have hzprod : z ∈ (D : Set G) * (centralizer (D : Set G) : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right D (centralizer (D : Set G))
      le_normalizer_of_normal]
    exact hzinner
  obtain ⟨d, hd, c, hc, hdc⟩ := hzprod
  have hdproj : d ∈ D ⊓ (Q ⊔ centralizer (D : Set G)) := by
    refine ⟨hd, ?_⟩
    have he : d = z * c⁻¹ := by rw [← hdc]; group
    rw [he]
    exact mul_mem (mem_sup_left hzQ) (mem_sup_right (inv_mem hc))
  rw [inf_sup_centralizer_eq_inf_of_saturation D A Q hZ hQ hAQ hsat] at hdproj
  refine ⟨d, hdproj, ?_⟩
  intro hdcen
  exact hznc (hdc ▸ (centralizer (D : Set G)).mul_mem hdcen hc)

/-- A uniquely determined Sylow overgroup is preserved by the actor.
Saturation then makes the original intersection that Sylow subgroup. -/
theorem exists_sylow_eq_inf_of_saturation [Finite G] [Fact p.Prime]
    (D A Q : Subgroup G) [D.Normal] (hQ : IsPGroup p Q)
    (hAQ : A ≤ normalizer (Q : Set G))
    (hsat : ∀ P : Subgroup G, IsPGroup p P →
      A ≤ normalizer (P : Set G) → P ≤ Q)
    (hunique : ∀ P R : Sylow p D, Q.subgroupOf D ≤ P →
      Q.subgroupOf D ≤ R → P = R) :
    ∃ P : Sylow p D, (P : Subgroup D).map D.subtype = D ⊓ Q := by
  obtain ⟨P, hQP⟩ := (hQ.comap_subtype (K := D)).exists_le_sylow
  have hnorm : A ≤ normalizer ((P : Subgroup D).map D.subtype : Set G) := by
    intro a ha
    let e : MulAut D := MulAut.conjNormal a
    let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
    have hQR : Q.subgroupOf D ≤ R := by
      intro q hq
      refine ⟨e.symm q, hQP ?_, e.apply_symm_apply q⟩
      change a⁻¹ * (q : G) * (a⁻¹)⁻¹ ∈ Q
      exact ((hAQ (A.inv_mem ha)) q).mp hq
    have hRP : R = P := (hunique P R hQP hQR).symm
    apply mem_normalizer_iff_map_conj_eq.mpr
    change ((P : Subgroup D).map D.subtype).map (MulAut.conj a).toMonoidHom = _
    have he : ((P : Subgroup D).map e.toMonoidHom).map D.subtype =
        ((P : Subgroup D).map D.subtype).map (MulAut.conj a).toMonoidHom := by
      rw [map_map, map_map]
      rfl
    rw [← he]
    exact congrArg (fun R : Sylow p D => (R : Subgroup D).map D.subtype) hRP
  refine ⟨P, le_antisymm (le_inf (map_subtype_le _)
    (hsat _ (P.isPGroup'.map D.subtype) hnorm)) ?_⟩
  intro x hx
  exact ⟨⟨x, hx.1⟩, hQP hx.2, rfl⟩

end Theory.GroupTheory
