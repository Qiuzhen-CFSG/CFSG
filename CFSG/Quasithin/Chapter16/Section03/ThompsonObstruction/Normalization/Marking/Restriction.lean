module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Normalization.Normality
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Restricting the chosen Sylow to the marked enlargement

Write X = K⟨z⟩ and H = C_G(t) ∩ C_G(z). Normality of K in C_G(t)
shows that H normalizes X. Thus X ∩ H is normal in H, and the supplied
Sylow C_T(t) restricts to it. The marked equivalence identifies X ∩ H
with the centralizer of (01) in S₈. Its Sylow image is exactly the image
of T ∩ X, since X lies in C_G(t) and T centralizes z.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the
paragraph preceding Lemma 16.3.12, printed p.1181 / PDF p.1198.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter16.ThompsonObstruction
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z t : G} {L : Subgroup G}

omit [Finite G] in
private theorem overgroup_le (s : Selected T z t L) :
    enlargement t L ⊔ zpowers z ≤ involutionCentralizer t := by
  refine sup_le s.marked.component.1 (zpowers_le.mpr ?_)
  exact mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp
      (s.counterexample.localSetup.sylow_centralizes s.counterexample.mem_commutingSylow.1)).symm

private theorem overgroup_normal (s : Selected T z t L) :
    ((enlargement t L ⊔ zpowers z).subgroupOf
      (involutionCentralizer t ⊓ involutionCentralizer z)).Normal := by
  have hn := (normal_subgroupOf_iff_le_normalizer s.marked.component.1).mp
    (s.marked.enlargement_normal s.counterexample.involution)
  refine ⟨fun x hx g => ?_⟩
  have he : (enlargement t L ⊔ zpowers z).map (MulAut.conj (g : G)).toMonoidHom =
      enlargement t L ⊔ zpowers z := by
    have hK : (enlargement t L).map (MulAut.conj (g : G)).toMonoidHom = enlargement t L :=
      mem_normalizer_iff_map_conj_eq.mp (hn g.property.1)
    rw [Subgroup.map_sup, hK, MonoidHom.map_zpowers]
    congr 1
    exact congrArg zpowers (mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_singleton_iff.mp g.property.2))
  have hm := mem_map_of_mem (MulAut.conj (g : G)).toMonoidHom
    (show (x : G) ∈ enlargement t L ⊔ zpowers z from hx)
  rw [he] at hm
  exact hm

private noncomputable def centralizerEquiv (s : Selected T z t L) :
    ↥((enlargement t L ⊔ zpowers z).subgroupOf
      (involutionCentralizer t ⊓ involutionCentralizer z)) ≃*
      ↥(centralizer ({Equiv.swap (0 : Fin 8) 1} : Set (Equiv.Perm (Fin 8)))) := by
  let X := enlargement t L ⊔ zpowers z
  let H := involutionCentralizer t ⊓ involutionCentralizer z
  let N := X.subgroupOf H
  let Z : X := ⟨z, (le_sup_right : zpowers z ≤ X) (mem_zpowers z)⟩
  let f : N →* ↥(centralizer ({Equiv.swap (0 : Fin 8) 1} : Set (Equiv.Perm (Fin 8)))) := {
    toFun := fun n => ⟨s.marked.equiv ⟨n, n.property⟩, by
      apply mem_centralizer_singleton_iff.mpr
      rw [← s.marked.involution_image, ← map_mul, ← map_mul]
      apply congrArg s.marked.equiv
      exact Subtype.ext (mem_centralizer_singleton_iff.mp n.val.property.2)⟩
    map_one' := by apply Subtype.ext; exact s.marked.equiv.map_one
    map_mul' := fun a b => by
      apply Subtype.ext
      exact s.marked.equiv.map_mul ⟨a, a.property⟩ ⟨b, b.property⟩ }
  exact MulEquiv.ofBijective f ⟨by
    intro a b hab
    have h := s.marked.equiv.injective (congrArg Subtype.val hab)
    exact Subtype.ext (Subtype.ext (congrArg (fun v : X => (v : G)) h)), by
    intro a
    let x := s.marked.equiv.symm a.val
    have hxz : (x : G) ∈ involutionCentralizer z := by
      apply mem_centralizer_singleton_iff.mpr
      have h : x * Z = Z * x := by
        apply s.marked.equiv.injective
        simp only [map_mul, x, s.marked.equiv.apply_symm_apply]
        rw [show s.marked.equiv Z = Equiv.swap 0 1 from s.marked.involution_image]
        exact mem_centralizer_singleton_iff.mp a.property
      exact congrArg Subtype.val h
    refine ⟨⟨⟨x, overgroup_le s x.property, hxz⟩, x.property⟩, ?_⟩
    apply Subtype.ext
    exact s.marked.equiv.apply_symm_apply a.val⟩

/-- The actual intersection T ∩ K⟨z⟩ maps to a Sylow subgroup of the
transposition centralizer under the supplied marking. -/
theorem Selected.exists_markingSylow (s : Selected T z t L) :
    ∃ S : Sylow 2 ↥(centralizer ({Equiv.swap (0 : Fin 8) 1} : Set (Equiv.Perm (Fin 8)))),
      (S : Subgroup _).map
        (centralizer ({Equiv.swap (0 : Fin 8) 1} : Set (Equiv.Perm (Fin 8)))).subtype =
        ((T : Subgroup G).subgroupOf (enlargement t L ⊔ zpowers z)).map
          s.marked.equiv.toMonoidHom := by
  let X := enlargement t L ⊔ zpowers z
  let H := involutionCentralizer t ⊓ involutionCentralizer z
  let N := X.subgroupOf H
  let : N.Normal := overgroup_normal s
  obtain ⟨S₀, hS₀⟩ := s.centralizer_sylow
  obtain ⟨R, hR⟩ := S₀.exists_subgroupOf_eq_of_normal N
  let e := centralizerEquiv s
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((R : Subgroup N).map e.toMonoidHom).map _ = _
  ext p
  constructor
  · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨⟨b.val.val, b.property⟩, ?_, rfl⟩
    have hbS : b.val ∈ (S₀ : Subgroup H) := by rw [hR] at hb; exact hb
    have hmem := mem_map_of_mem H.subtype hbS
    rw [hS₀] at hmem
    exact hmem.1
  · rintro ⟨x, hx, rfl⟩
    have hxH : (x : G) ∈ H :=
      ⟨overgroup_le s x.property, s.counterexample.localSetup.sylow_centralizes hx⟩
    let b : N := ⟨⟨x, hxH⟩, x.property⟩
    have hb : b ∈ (R : Subgroup N) := by
      rw [hR]
      change (⟨x, hxH⟩ : H) ∈ (S₀ : Subgroup H)
      have hmem : (x : G) ∈ (S₀ : Subgroup H).map H.subtype := by
        rw [hS₀]
        exact ⟨hx, hxH.1⟩
      obtain ⟨y, hy, he⟩ := hmem
      have hyx : y = ⟨x, hxH⟩ := Subtype.ext he
      exact hyx ▸ hy
    exact ⟨e b, mem_map_of_mem e.toMonoidHom hb, rfl⟩

end CFSG.Quasithin.Chapter16.ThompsonObstruction
