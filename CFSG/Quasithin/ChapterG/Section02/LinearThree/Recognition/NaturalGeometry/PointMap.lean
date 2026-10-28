module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Models
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.SylowLocalCore
public import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# The natural projective point map for the upper G.2.5 section

The full point stabilizer lies in H by its two-residual/Sylow supplement.
It therefore normalizes W. Extending the image of W along the natural
projective orbit gives a well-defined equivariant map. Right-conjugate
marks use the inverse starred actor. The product formula for S supplies
spanning; the pair-intersection formula for S₃ supplies disjointness at
the first two marks. The actual SL₃ projective two-transitivity then gives
disjointness at every pair of distinct points.

The argument works for the given conjugation section, and never assumes
that S₃ is contained in W or that any upper marked image is nonzero.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.5(7), printed pp.335–336, and G.1.4, printed p.328.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Projective
variable {F K V M : Type*} [Field F] [Group K] [AddCommGroup V] [Module F V]
  [AddCommGroup M] [Module (ZMod 2) M]
  (γ : Representation F K V) (ρ : Representation (ZMod 2) K M)
  (P : Point F V) (Q : Submodule (ZMod 2) M)

private theorem map_action_mul {R X : Type*} [Semiring R] [AddCommMonoid X] [Module R X]
    (σ : Representation R K X) (A : Submodule R X) (a b : K) :
    A.map (σ (a * b)) = (A.map (σ b)).map (σ a) := by
  rw [← Submodule.map_comp, map_mul]
  rfl

private theorem map_action_one {R X : Type*} [Semiring R] [AddCommMonoid X] [Module R X]
    (σ : Representation R K X) (A : Submodule R X) : A.map (σ 1) = A := by
  rw [map_one]
  exact Submodule.map_id A

theorem map_eq_of_stabilizer
    (hs : ∀ x, P.val.map (γ x) = P.val → Q.map (ρ x) = Q)
    {a b : K} (hab : P.val.map (γ a) = P.val.map (γ b)) :
    Q.map (ρ a) = Q.map (ρ b) := by
  have hp : P.val.map (γ (b⁻¹ * a)) = P.val := by
    rw [map_action_mul, hab, ← map_action_mul, inv_mul_cancel, map_action_one]
  have hq := congrArg (fun A : Submodule (ZMod 2) M => A.map (ρ b)) (hs _ hp)
  simpa only [← map_action_mul, mul_inv_cancel_left] using hq

/-- Extend a stabilizer-invariant marked subspace along the projective orbit. -/
noncomputable def orbitMap (A : Point F V) : Submodule (ZMod 2) M :=
  ⨆ (x : K) (_ : P.val.map (γ x) = A.val), Q.map (ρ x)

theorem orbitMap_eq
    (hs : ∀ x, P.val.map (γ x) = P.val → Q.map (ρ x) = Q)
    (A : Point F V) (x : K) (hx : P.val.map (γ x) = A.val) :
    orbitMap γ ρ P Q A = Q.map (ρ x) := by
  apply le_antisymm
  · exact iSup_le fun y => iSup_le fun hy =>
      (map_eq_of_stabilizer γ ρ P Q hs (hy.trans hx.symm)).le
  · exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)

theorem orbitMap_mark
    (hs : ∀ x, P.val.map (γ x) = P.val → Q.map (ρ x) = Q) :
    orbitMap γ ρ P Q P = Q := by
  rw [orbitMap_eq γ ρ P Q hs P 1 (map_action_one γ P.val), map_action_one]

theorem orbitMap_equivariant
    (ht : ∀ A : Point F V, ∃ x, P.val.map (γ x) = A.val)
    (hs : ∀ x, P.val.map (γ x) = P.val → Q.map (ρ x) = Q)
    (x : K) (A B : Point F V) (hAB : B.val = A.val.map (γ x)) :
    orbitMap γ ρ P Q B = (orbitMap γ ρ P Q A).map (ρ x) := by
  obtain ⟨y, hy⟩ := ht A
  have hxy : P.val.map (γ (x * y)) = B.val := by
    rw [map_action_mul, hy, ← hAB]
  rw [orbitMap_eq γ ρ P Q hs B (x * y) hxy,
    orbitMap_eq γ ρ P Q hs A y hy, map_action_mul]

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Projective

open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
open Projective
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)
include d

theorem naturalPoint_transitive (A : Point F (Fin 3 → F)) :
    ∃ x : D.star D.L, d.point.map (naturalAction d x) = A.val := by
  obtain ⟨v, hv, hv0⟩ := d.point.ne_bot_iff.mp
    (Submodule.isAtom_iff_finrank_eq_one.mpr d.point_dimension).ne_bot
  obtain ⟨w, hw, hw0⟩ := A.val.ne_bot_iff.mp
    (Submodule.isAtom_iff_finrank_eq_one.mpr A.property).ne_bot
  obtain ⟨a, ha⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three v w hv0 hw0
  refine ⟨d.model.symm a, ?_⟩
  rw [eq_span_singleton_of_mem_of_finrank_eq_one d.point_dimension hv hv0,
    eq_span_singleton_of_mem_of_finrank_eq_one A.property hw hw0,
    Submodule.map_span]
  simp only [Set.image_singleton]
  change Submodule.span F {((d.model (d.model.symm a)).val.mulVec v)} = _
  rw [d.model.apply_symm_apply, ha]

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis

open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)
include d

theorem point_normalizer_le_H : D.L ⊓ D.G₁ ≤ D.H := by
  let N := D.L ⊓ D.G₁
  let J := N ⊔ D.T
  have hNJ : N ≤ J := le_sup_left
  have hTJ : D.T ≤ J := le_sup_right
  have hJLT : J ≤ D.LT := sup_le (inf_le_left.trans le_sup_left) le_sup_right
  have hTN : D.T ≤ normalizer (N : Set G) :=
    (le_inf d.setup.T_normalizes_L
      (d.setup.T_normalizes_point.trans D.G₁.le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
  obtain ⟨P, hP⟩ := d.setup.sylow_LT
  obtain ⟨Q, hQ⟩ := P.exists_map_subtype_eq_of_le hJLT (by rw [hP]; exact hTJ)
  obtain ⟨R, hR⟩ := Q.exists_map_subtype_eq_inf_of_normalizes hNJ
    (sup_le N.le_normalizer hTN)
  have he := congrArg (fun A : Subgroup N => A.map N.subtype)
    (pResidual_sup_sylow_eq_top R)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype, hR, hQ, hP] at he
  change N ≤ D.H
  rw [← he]
  exact sup_le (le_sup_left.trans d.setup.local_le)
    (inf_le_left.trans (le_sup_right.trans d.setup.local_le))

theorem point_normalizer_normalizes_W (hLI : D.L ≤ I D g h) :
    D.L ⊓ D.G₁ ≤ normalizer (W D g h : Set G) :=
  (le_inf ((point_normalizer_le_H d).trans (le_normalizer_conjugateSpanBy _ _))
    ((inf_le_left.trans hLI).trans (I_normalizes_core D g h))).trans
      inf_normalizer_le_normalizer_inf


theorem natural_stabilizer_mem_G₁ (l : D.L)
    (hl : d.point.map (naturalAction d (starProjection D l)) = d.point) :
    (l : G) ∈ D.G₁ := by
  apply mem_normalizer_iff.mpr
  intro v
  have hV := mem_normalizer_iff.mp (normalizes_of_span D d.span_eq l.property) v
  constructor
  · intro hv
    let v' : D.V := ⟨v, d.setup.point_le hv⟩
    apply (d.point_mem ⟨(l : G) * v * (l : G)⁻¹, hV.mp v'.property⟩).mpr
    rw [d.equivariant l v']
    have hc := (d.point_mem v').mp hv
    have hm : naturalAction d (starProjection D l) (d.coordinates v').toAdd ∈
        d.point.map (naturalAction d (starProjection D l)) := ⟨_, hc, rfl⟩
    exact hl ▸ hm
  · intro hv
    let v' : D.V := ⟨v, hV.mpr (d.setup.point_le hv)⟩
    apply (d.point_mem v').mpr
    have hc := (d.point_mem ⟨(l : G) * v * (l : G)⁻¹, hV.mp v'.property⟩).mp hv
    rw [d.equivariant l v'] at hc
    change naturalAction d (starProjection D l) (d.coordinates v').toAdd ∈ d.point at hc
    rw [← hl] at hc
    obtain ⟨w, hw, he⟩ := hc
    exact ((naturalAction d).apply_bijective _).injective he ▸ hw

theorem natural_stabilizer_normalizes_W (hLI : D.L ≤ I D g h) (l : D.L)
    (hl : d.point.map (naturalAction d (starProjection D l)) = d.point) :
    (l : G) ∈ normalizer (W D g h : Set G) :=
  point_normalizer_normalizes_W d hLI ⟨l.property, natural_stabilizer_mem_G₁ d l hl⟩

theorem naturalPoint_ne_conjugate_g : naturalPoint d ≠ conjugatePoint d ⟨g, d.g_mem⟩ := by
  intro he
  have hp : d.point.map (naturalAction d (starProjection D ⟨g, d.g_mem⟩)⁻¹) = d.point :=
    (congrArg Subtype.val he).symm
  have hn := natural_stabilizer_mem_G₁ d (⟨g, d.g_mem⟩ : D.L)⁻¹
    (by simpa only [map_inv] using hp)
  have hc : Setup.conjugate D.V₁ g = D.V₁ := mem_normalizer_iff_map_conj_eq.mp hn
  have hd := d.points_disjoint
  rw [hc] at hd
  exact d.setup.point_ne_bot (disjoint_self.mp hd)

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
namespace SectionGeometry
variable {G : Type*} [Group G] {H S E : Subgroup G}
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  {ρ : Representation (ZMod 2) H M}
  (s : Representation.BinaryConjugationSection H S E ρ)

def image (A : Subgroup G) : Submodule (ZMod 2) M :=
  AddSubgroup.toZModSubmodule 2
    (Subgroup.toAddSubgroup' ((A.subgroupOf S).map s.coordinates))

theorem mem_image (A : Subgroup G) (v : M) :
    v ∈ image s A ↔ ∃ a : S, (a : G) ∈ A ∧ (s.coordinates a).toAdd = v := Iff.rfl

theorem image_conjugate (A : Subgroup G) (l : H) :
    image s (Setup.conjugate A (l : G)⁻¹) = (image s A).map (ρ l) := by
  apply le_antisymm
  · intro v hv
    obtain ⟨a, ha, rfl⟩ := (mem_image s _ _).mp hv
    obtain ⟨b, hb, hba⟩ := ha
    change (l : G)⁻¹⁻¹ * b * ((l : G)⁻¹⁻¹)⁻¹ = (a : G) at hba
    simp only [inv_inv] at hba
    have hbS : b ∈ S := by
      apply (mem_normalizer_iff.mp (s.normalized l.property) b).mpr
      rw [hba]
      exact a.property
    refine ⟨(s.coordinates ⟨b, hbS⟩).toAdd, (mem_image s A _).mpr ⟨_, hb, rfl⟩, ?_⟩
    rw [← s.equivariant l ⟨b, hbS⟩]
    exact congrArg (fun x : S => (s.coordinates x).toAdd) (Subtype.ext hba)
  · rintro v ⟨w, hw, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (mem_image s A _).mp hw
    let b : S := ⟨(l : G) * a * (l : G)⁻¹,
      (mem_normalizer_iff.mp (s.normalized l.property) a).mp a.property⟩
    apply (mem_image s _ _).mpr
    refine ⟨b, ?_, s.equivariant l a⟩
    refine ⟨a, ha, ?_⟩
    change (l : G)⁻¹⁻¹ * a * ((l : G)⁻¹⁻¹)⁻¹ = _
    simp only [inv_inv]
    rfl

theorem image_invariant (A : Subgroup G) (l : H)
    (hl : (l : G) ∈ normalizer (A : Set G)) :
    (image s A).map (ρ l) = image s A := by
  rw [← image_conjugate]
  congr 1
  exact mem_normalizer_iff_map_conj_eq.mp
    (show (l : G)⁻¹⁻¹ ∈ normalizer (A : Set G) by simpa using hl)

theorem image_sup (A B : Subgroup G) (hA : A ≤ S) (hB : B ≤ S) :
    image s (A ⊔ B) = image s A ⊔ image s B := by
  simp only [image, subgroupOf_sup hA hB, Subgroup.map_sup, SupHomClass.map_sup]

theorem image_self : image s S = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨a, ha⟩ := s.onto (Multiplicative.ofAdd v)
  exact (mem_image s S v).mpr ⟨a, a.property, ha⟩

end SectionGeometry
end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
open Subgroup Projective Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  {hLI : D.L ≤ I D g h} (e : StarComparison D g h hLI)
  (σ : Representation (ZMod 2) (D.star D.L) M)
  (s : Representation.BinaryConjugationSection (I D g h) (S D g h) (S₃ D g h)
    (σ.comp e.projection))

/-- The natural point map in the actual upper conjugation section. -/
noncomputable def naturalPointMap : Point F (Fin 3 → F) → Submodule (ZMod 2) M :=
  orbitMap (naturalAction d) σ (naturalPoint d) (SectionGeometry.image s (W D g h))

theorem upper_stabilizer_invariant (x : D.star D.L)
    (hx : d.point.map (naturalAction d x) = d.point) :
    (SectionGeometry.image s (W D g h)).map (σ x) = SectionGeometry.image s (W D g h) := by
  obtain ⟨l, rfl⟩ := starProjection_surjective D x
  have hn := natural_stabilizer_normalizes_W d hLI l hx
  have hi := SectionGeometry.image_invariant s (W D g h) (inclusion hLI l) hn
  simpa only [MonoidHom.comp_apply, e.projection_on_L] using hi

theorem naturalPointMap_mark :
    naturalPointMap d e σ s (naturalPoint d) = SectionGeometry.image s (W D g h) :=
  orbitMap_mark (naturalAction d) σ (naturalPoint d) _ (upper_stabilizer_invariant d e σ s)

theorem naturalPointMap_equivariant (x : D.star D.L) (A B : Point F (Fin 3 → F))
    (hAB : B.val = A.val.map (naturalAction d x)) :
    naturalPointMap d e σ s B = (naturalPointMap d e σ s A).map (σ x) :=
  orbitMap_equivariant (naturalAction d) σ (naturalPoint d) _
    (naturalPoint_transitive d) (upper_stabilizer_invariant d e σ s) x A B hAB

theorem naturalPointMap_conjugate (l : D.L) :
    naturalPointMap d e σ s (conjugatePoint d l) =
      SectionGeometry.image s (conjugate (W D g h) l) := by
  rw [naturalPointMap, orbitMap_eq (naturalAction d) σ (naturalPoint d) _
    (upper_stabilizer_invariant d e σ s) (conjugatePoint d l) (starProjection D l)⁻¹ rfl]
  have hc := SectionGeometry.image_conjugate s (W D g h) (inclusion hLI l⁻¹)
  simpa only [coe_inclusion, coe_inv, inv_inv, MonoidHom.comp_apply, e.projection_on_L, map_inv] using hc.symm

/-- The literal three upper marks span the section before recognition. -/
theorem naturalPointMap_spanning
    (hgen : S D g h = (W D g h ⊔ conjugate (W D g h) g) ⊔ conjugate (W D g h) h) :
    (⨆ A, naturalPointMap d e σ s A) = ⊤ := by
  have hW : W D g h ≤ S D g h := inf_le_right
  have hWg : conjugate (W D g h) g ≤ S D g h := by
    rw [conjugate_W D g h g (hLI d.g_mem)]
    exact inf_le_right
  have hWh : conjugate (W D g h) h ≤ S D g h := by
    rw [conjugate_W D g h h (hLI d.h_mem)]
    exact inf_le_right
  have hs := congrArg (SectionGeometry.image s) hgen
  rw [SectionGeometry.image_self, SectionGeometry.image_sup s _ _ (sup_le hW hWg) hWh,
    SectionGeometry.image_sup s _ _ hW hWg] at hs
  apply top_unique
  rw [hs]
  apply sup_le (sup_le ?_ ?_) ?_
  · rw [← naturalPointMap_mark d e σ s]
    exact le_iSup (naturalPointMap d e σ s) (naturalPoint d)
  · rw [← naturalPointMap_conjugate d e σ s ⟨g, d.g_mem⟩]
    exact le_iSup (naturalPointMap d e σ s) (conjugatePoint d ⟨g, d.g_mem⟩)
  · rw [← naturalPointMap_conjugate d e σ s ⟨h, d.h_mem⟩]
    exact le_iSup (naturalPointMap d e σ s) (conjugatePoint d ⟨h, d.h_mem⟩)

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
open scoped LinearAlgebra.Projectivization
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
open Projective
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)
include d

theorem naturalPoint_pair_transitive (A B C E : Point F (Fin 3 → F))
    (hAB : A ≠ B) (hCE : C ≠ E) :
    ∃ x : D.star D.L, A.val.map (naturalAction d x) = C.val ∧
      B.val.map (naturalAction d x) = E.val := by
  let t := (Projectivization.equivSubmodule F (Fin 3 → F)).symm
  have hAB' : t A ≠ t B := fun he => hAB (t.injective he)
  have hCE' : t C ≠ t E := fun he => hCE (t.injective he)
  obtain ⟨x, hxA, hxB⟩ := (MulAction.is_two_pretransitive_iff.mp
    (inferInstance : MulAction.IsMultiplyPretransitive
      (Matrix.SpecialLinearGroup (Fin 3) F) (ℙ F (Fin 3 → F)) 2)) hAB' hCE'
  have ht (P : Point F (Fin 3 → F)) : (t P).submodule = P.val :=
    congrArg Subtype.val ((Projectivization.equivSubmodule F (Fin 3 → F)).apply_symm_apply P)
  have hm (P : Point F (Fin 3 → F)) :
      (x • t P).submodule = P.val.map (naturalAction d (d.model.symm x)) := by
    rw [← ht P, ← Projectivization.mk_rep (t P), Projectivization.smul_mk,
      Projectivization.submodule_mk, Projectivization.submodule_mk, Submodule.map_span]
    simp only [Set.image_singleton]
    change F ∙ (x.val.mulVec (t P).rep) = F ∙ ((d.model (d.model.symm x)).val.mulVec (t P).rep)
    rw [d.model.apply_symm_apply]
  exact ⟨d.model.symm x,
    (hm A).symm.trans ((congrArg Projectivization.submodule hxA).trans (ht C)),
    (hm B).symm.trans ((congrArg Projectivization.submodule hxB).trans (ht E))⟩

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
open Subgroup Setup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  {hLI : D.L ≤ I D g h} (e : StarComparison D g h hLI)
  (σ : Representation (ZMod 2) (D.star D.L) M)
  (s : Representation.BinaryConjugationSection (I D g h) (S D g h) (S₃ D g h)
    (σ.comp e.projection))
include d

theorem upper_marked_pair_disjoint (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    Disjoint (SectionGeometry.image s (W D g h))
      (SectionGeometry.image s (conjugate (W D g h) g)) := by
  apply disjoint_iff.mpr
  apply le_antisymm _ bot_le
  intro v hv
  obtain ⟨a, ha, hav⟩ := (SectionGeometry.mem_image s _ _).mp hv.1
  obtain ⟨b, hb, hbv⟩ := (SectionGeometry.mem_image s _ _).mp hv.2
  have hab : (a : G) * (b : G)⁻¹ ∈ S₃ D g h := by
    apply (s.coordinates_eq_one_iff (a * b⁻¹)).mp
    rw [map_mul, map_inv]
    have he : s.coordinates a = s.coordinates b := hav.trans hbv.symm
    rw [he, mul_inv_cancel]
  have hab' : (a : G) * (b : G)⁻¹ ∈
      ((W D g h ⊓ conjugate (W D g h) g : Subgroup G) : Set G) *
        ((W D g h ⊓ conjugate (W D g h) h : Subgroup G) : Set G) *
        ((conjugate (W D g h) g ⊓ conjugate (W D g h) h : Subgroup G) : Set G) := by
    rw [← d.S₃_product hUT hf hLI]
    exact hab
  obtain ⟨pq, ⟨p, hp, q, hq, rfl⟩, r, hr, he⟩ := hab'
  change p * q * r = (a : G) * (b : G)⁻¹ at he
  let z : G := (p * q)⁻¹ * a
  have hz : z = r * b := by
    calc
      z = (p * q)⁻¹ * (((p * q) * r) * b) := by rw [he]; simp [z]
      _ = r * b := by group
  have hzW : z ∈ W D g h :=
    (W D g h).mul_mem ((W D g h).inv_mem ((W D g h).mul_mem hp.1 hq.1)) ha
  have hzWg : z ∈ conjugate (W D g h) g := by
    rw [hz]
    exact (conjugate (W D g h) g).mul_mem hr.1 hb
  have haE : (a : G) ∈ S₃ D g h := by
    have hpE : p ∈ S₃ D g h := mem_sup_left (mem_sup_left hp)
    have hqE : q ∈ S₃ D g h := mem_sup_left (mem_sup_right hq)
    have hzE : z ∈ S₃ D g h := mem_sup_left (mem_sup_left ⟨hzW, hzWg⟩)
    have hm := (S₃ D g h).mul_mem ((S₃ D g h).mul_mem hpE hqE) hzE
    simpa only [z, mul_inv_cancel_left] using hm
  have hav0 := (s.coordinates_eq_one_iff a).mpr haE
  change v = 0
  exact hav.symm.trans hav0

theorem naturalPointMap_disjoint (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (A B : Projective.Point F (Fin 3 → F)) (hAB : A ≠ B) :
    Disjoint (naturalPointMap d e σ s A) (naturalPointMap d e σ s B) := by
  obtain ⟨x, hxA, hxB⟩ := naturalPoint_pair_transitive d (naturalPoint d)
    (conjugatePoint d ⟨g, d.g_mem⟩) A B (naturalPoint_ne_conjugate_g d) hAB
  rw [naturalPointMap_equivariant d e σ s x _ A hxA.symm,
    naturalPointMap_equivariant d e σ s x _ B hxB.symm,
    naturalPointMap_mark, naturalPointMap_conjugate]
  exact Submodule.disjoint_map (σ.apply_bijective x).injective
    (upper_marked_pair_disjoint d e σ s hUT hf)

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
