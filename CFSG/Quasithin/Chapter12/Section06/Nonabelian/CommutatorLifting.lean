module
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup
public import Theory.Representation.BinaryPermutation.EightGeometry
public import Theory.LinearAlgebra.QuadraticSingularLine

/-!
# Singular-line commutator lifting on the actual six-space

An actor with commutators in the singular point line is trivial, since
its permutation action preserves the nondegenerate quadratic form.
Conjugating one of the two mixed commutators back to V therefore proves
both conclusions of F.9.1(e). The same geometry shows that the literal
perpendicular and V have the same centralizer once its normalizer
preserves V. All subgroup maps use left conjugation consistently.

Source: Aschbacher--Smith, 12.6.24(6--7), printed pp.830--831. This
is a direct isometry proof of the lifting clause, avoiding the printed
intermediate parabolic classification in 12.6.20(4).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section06
namespace Nonabelian.Setup
open BinaryPermutation BinaryPermutation.TerminalOrthogonal.Eight
open scoped commutatorElement
variable {G : Type*} [Group G] (E : Setup G)

private theorem coordinates_mem_line (v : E.V) (hv : v.val ∈ E.V₁) :
    (E.coordinates v).toAdd ∈ Submodule.span (ZMod 2) {(E.coordinates E.z).toAdd} := by
  obtain ⟨n,hn⟩ := mem_zpowers_iff.mp hv
  have he : E.z ^ n = v := Subtype.ext hn
  rw [←he,map_zpow]
  change n • (E.coordinates E.z).toAdd ∈ _
  exact (Submodule.span (ZMod 2) {(E.coordinates E.z).toAdd}).toAddSubgroup.zsmul_mem
    (Submodule.mem_span_singleton_self _) n

/-- An actor normalizing the marked six-space cannot have nontrivial
commutators in a singular point line. -/
theorem commutator_eq_bot_of_singular_line
    (hz : E.z ≠ 1) (hs : form (E.coordinates E.z).toAdd = 0)
    (hact : ∀ a : normalizer (E.V : Set G), ∃ p : Equiv.Perm (Fin 8),
      ∀ v : E.V, (E.coordinates (E.V.normalizerMonoidHom a v)).toAdd =
        naturalRepresentation (Fin 8) p (E.coordinates v).toAdd)
    (A : Subgroup G) (hn : A ≤ normalizer (E.V : Set G))
    (hc : ⁅A,E.V⁆ ≤ E.V₁) : ⁅A,E.V⁆ = ⊥ := by
  have hz0 : (E.coordinates E.z).toAdd ≠ 0 := by
    intro he
    exact hz (E.coordinates.injective (he.trans E.coordinates.map_one.symm))
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro a ha v hv
  let an : normalizer (E.V : Set G) := ⟨a,hn ha⟩
  obtain ⟨p,hp⟩ := hact an
  let t := LinearEquiv.ofBijective (naturalRepresentation (Fin 8) p)
    ((naturalRepresentation (Fin 8)).apply_bijective p)
  have hrange : (t.toLinearMap - LinearMap.id).range ≤
      Submodule.span (ZMod 2) {(E.coordinates E.z).toAdd} := by
    rintro _ ⟨w,rfl⟩
    obtain ⟨u,hu⟩ := E.coordinates.surjective (Multiplicative.ofAdd w)
    let d := E.V.normalizerMonoidHom an u * u⁻¹
    have hd : d.val ∈ E.V₁ := hc (commutator_mem_commutator ha u.property)
    have he := coordinates_mem_line E d hd
    change t w-w ∈ _
    simp only [d,map_mul,map_inv,toAdd_mul,toAdd_inv,←sub_eq_add_neg] at he
    change (E.coordinates (E.V.normalizerMonoidHom an u)).toAdd -
      (E.coordinates u).toAdd ∈
        Submodule.span (ZMod 2) {(E.coordinates E.z).toAdd} at he
    rw [hp u,hu] at he
    exact he
  have hr : Module.finrank (ZMod 2) (t.toLinearMap - LinearMap.id).range ≤ 1 := by
    have hh := Submodule.finrank_mono hrange
    rwa [finrank_span_singleton hz0] at hh
  have hzero : ∀ w, t w=w := by
    intro w
    have hw : t w-w ∈ (t.toLinearMap - LinearMap.id).range := ⟨w,rfl⟩
    obtain ⟨c,he⟩ := Submodule.mem_span_singleton.mp (hrange hw)
    rcases (by decide : ∀ c : ZMod 2, c=0 ∨ c=1) c with h | h
    · rw [h,zero_smul] at he
      exact sub_eq_zero.mp he.symm
    · rw [h,one_smul] at he
      exact False.elim ((form.singular_not_mem_displacement EightGeometry.polar_nondegenerate.1
        t (form_invariant p) hr _ hz0 hs) (he.symm ▸ hw))
  have hfix : E.V.normalizerMonoidHom an ⟨v,hv⟩ = ⟨v,hv⟩ := by
    apply E.coordinates.injective
    exact (hp ⟨v,hv⟩).trans (hzero _)
  have hh := congrArg Subtype.val hfix
  change a*v*a⁻¹=v at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- Conjugating the second mixed commutator back reduces both clauses of
F.9.1(e) to the same singular-line isometry obstruction. -/
theorem commutator_lifting_of_permutation_action
    (hz : E.z ≠ 1) (hs : form (E.coordinates E.z).toAdd = 0)
    (hact : ∀ a : normalizer (E.V : Set G), ∃ p : Equiv.Perm (Fin 8),
      ∀ v : E.V, (E.coordinates (E.V.normalizerMonoidHom a v)).toAdd =
        naturalRepresentation (Fin 8) p (E.coordinates v).toAdd)
    (g : G) (hg : g ∈ E.Gz)
    (hVV : ⁅E.V,E.V.map (MulAut.conj g).toMonoidHom⁆ ≤
      E.V ⊓ E.V.map (MulAut.conj g).toMonoidHom)
    (h₁ : ⁅E.V₅,E.V.map (MulAut.conj g).toMonoidHom⁆ ≤ E.V₁)
    (h₂ : ⁅E.V₅.map (MulAut.conj g).toMonoidHom,E.V⁆ ≤ E.V₁) :
    ⁅E.V₅,E.V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∧
      ⁅E.V₅.map (MulAut.conj g).toMonoidHom,E.V⁆ = ⊥ := by
  have hinv (W : Subgroup G) :
      (W.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom=W := by
    rw [map_map]
    have hh : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom=MonoidHom.id G := by
      ext x
      change g⁻¹*(g*x*g⁻¹)*(g⁻¹)⁻¹=x
      group
    rw [hh,map_id]
  have hn : E.V.map (MulAut.conj g).toMonoidHom ≤ normalizer (E.V : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hVV.trans inf_le_left)
  have hsecond := E.commutator_eq_bot_of_singular_line hz hs hact _
    ((map_mono E.V₅_le).trans hn) h₂
  have hnback : (E.V.map (MulAut.conj g⁻¹).toMonoidHom) ≤ normalizer (E.V : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (hVV.trans inf_le_right)
    rwa [map_commutator,hinv] at hh
  have hpoint : E.V₁.map (MulAut.conj g⁻¹).toMonoidHom=E.V₁ :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (E.V₁ : Set G)).inv_mem
      (Subgroup.centralizer_le_normalizer _ hg))
  have hcback : ⁅E.V₅.map (MulAut.conj g⁻¹).toMonoidHom,E.V⁆ ≤ E.V₁ := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h₁
    rwa [map_commutator,hinv,hpoint] at hh
  have hfirst := E.commutator_eq_bot_of_singular_line hz hs hact _
    ((map_mono E.V₅_le).trans hnback) hcback
  refine ⟨?_,hsecond⟩
  apply (map_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective)
  rw [map_commutator,hinv,Subgroup.map_bot]
  exact hfirst
end Nonabelian.Setup

namespace Nonabelian.Setup
open BinaryPermutation BinaryPermutation.TerminalOrthogonal.Eight
variable {G : Type*} [Group G] (E : Setup G)

/-- The perpendicular to a nonzero singular point has the same ambient
centralizer as the entire marked module, once its normalizer preserves V. -/
theorem perpendicular_centralizer_eq
    (hz : E.z ≠ 1) (hs : form (E.coordinates E.z).toAdd = 0)
    (hact : ∀ a : normalizer (E.V : Set G), ∃ p : Equiv.Perm (Fin 8),
      ∀ v : E.V, (E.coordinates (E.V.normalizerMonoidHom a v)).toAdd =
        naturalRepresentation (Fin 8) p (E.coordinates v).toAdd)
    (hcontrol : E.G₅ ≤ normalizer (E.V : Set G)) :
    centralizer (E.V₅ : Set G) = centralizer (E.V : Set G) := by
  apply le_antisymm _ (centralizer_le E.V₅_le)
  intro a ha
  have han : a ∈ normalizer (E.V : Set G) :=
    hcontrol (Subgroup.centralizer_le_normalizer _ ha)
  let an : normalizer (E.V : Set G) := ⟨a,han⟩
  obtain ⟨p,hp⟩ := hact an
  let t := LinearEquiv.ofBijective (naturalRepresentation (Fin 8) p)
    ((naturalRepresentation (Fin 8)).apply_bijective p)
  have hz0 : (E.coordinates E.z).toAdd ≠ 0 := by
    intro he
    exact hz (E.coordinates.injective (he.trans E.coordinates.map_one.symm))
  have ht : t=1 := form.eq_one_of_fixed_singular_perpendicular
    EightGeometry.polar_nondegenerate t (form_invariant p) _ hz0 hs (by
      intro x hx
      obtain ⟨v,hv⟩ := E.coordinates.surjective (Multiplicative.ofAdd x)
      have hv5 : v.val ∈ E.V₅ := (E.mem_V₅_iff v).mpr (by rwa [hv])
      have hfix : E.V.normalizerMonoidHom an v=v := by
        apply Subtype.ext
        change a*v.val*a⁻¹=v.val
        rw [←ha v.val hv5,mul_inv_cancel_right]
      have hh := hp v
      rw [hfix,hv] at hh
      exact hh.symm)
  intro v hv
  have hfix : E.V.normalizerMonoidHom an ⟨v,hv⟩=⟨v,hv⟩ := by
    apply E.coordinates.injective
    have hh := hp ⟨v,hv⟩
    change (E.coordinates _).toAdd=t (E.coordinates ⟨v,hv⟩).toAdd at hh
    rw [ht] at hh
    exact hh
  have hh := congrArg Subtype.val hfix
  change a*v*a⁻¹=v at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm
end Nonabelian.Setup

end CFSG.Quasithin.Chapter12.Section06
