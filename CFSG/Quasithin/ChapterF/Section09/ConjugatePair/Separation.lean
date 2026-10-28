module
public import CFSG.Quasithin.ChapterF.Section09.Commutator
public import Theory.GroupTheory.ConjugatePairSeed.Separation

/-!
# The original fixed-seed separation in F.9.5(5)

For an original F.9.1 configuration satisfying the intersecting-pair
condition, every non-two pair has intersection exactly V₁. Its first
seed has no further vectors centralizing the opposite module modulo V₁.
The argument uses relative Baer–Suzuki inside that very pair.
Source: Aschbacher–Smith F.9.5(5), printed p.319.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} (h : D.Hypothesis)
include h

omit [Finite G] h in
/-- The left-conjugate form of the original intersecting-pair assumption. -/
theorem pair_condition_left
    (hp : ∀ g ∈ D.H, D.V₁ < D.V ⊓ ChapterG.Section02.Setup.conjugate D.V g →
      IsPGroup 2 (D.V ⊔ ChapterG.Section02.Setup.conjugate D.V g : Subgroup G)) :
    ∀ g ∈ D.H, D.V₁ < D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom →
      IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  intro g hg hi
  have ht := hp g⁻¹ (D.H.inv_mem hg) (by
    simpa only [ChapterG.Section02.Setup.conjugate, inv_inv] using hi)
  change IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g⁻¹⁻¹).toMonoidHom : Subgroup G) at ht
  rw [inv_inv] at ht
  exact ht

/-- The two original modules meet precisely in the fixed point. -/
theorem pair_intersection_eq_point
    (hp : ∀ g ∈ D.H, D.V₁ < D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom →
      IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G))
    (g : G) (hg : g ∈ D.H)
    (hn : ¬ IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom = D.V₁ := by
  have hz : D.V₁.map (MulAut.conj g).toMonoidHom = D.V₁ :=
    mem_normalizer_iff_map_conj_eq.mp
      ((h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) hg)
  have hle : D.V₁ ≤ D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom :=
    le_inf (h.point_lt.le.trans h.plus_le)
      (hz.symm.le.trans (map_mono (h.point_lt.le.trans h.plus_le)))
  apply le_antisymm _ hle
  by_contra hh
  exact hn (hp g hg (lt_of_le_of_ne hle (Ne.symm (fun he => hh he.le))))

/-- The first moved seed has zero fixed quotient on the opposite module. -/
theorem pair_seed_fixed_eq_point
    (hp : ∀ g ∈ D.H, D.V₁ < D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom →
      IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G))
    (g : G) (hg : g ∈ D.H)
    (hn : ¬ IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    commutatorPreimage D.Vplus (D.V.map (MulAut.conj g).toMonoidHom) D.V₁ = D.V₁ := by
  let := h.elementary
  exact commutatorPreimage_eq_of_conjugate_pair_not_isPGroup
    D.H D.V D.Vplus D.V₁ h.V_le_H h.plus_le h.point_lt.le
    (IsElementaryAbelian.isPGroup 2 D.V) inferInstance h.H_centralizes hp g hg hn

omit h [Finite G] in
private theorem conjugate_inverse (A : Subgroup G) (g : G) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_inv, MonoidHom.id_apply]
    group
  rw [he, map_id]

/-- The same separation for the second, literally conjugated, seed. -/
theorem pair_conjugate_seed_fixed_eq_point
    (hp : ∀ g ∈ D.H, D.V₁ < D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom →
      IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G))
    (g : G) (hg : g ∈ D.H)
    (hn : ¬ IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    commutatorPreimage (D.Vplus.map (MulAut.conj g).toMonoidHom) D.V D.V₁ = D.V₁ := by
  let f := (MulAut.conj g).toMonoidHom
  let fi := (MulAut.conj g⁻¹).toMonoidHom
  have hz : D.V₁.map fi = D.V₁ := mem_normalizer_iff_map_conj_eq.mp
    ((h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) (D.H.inv_mem hg))
  have hnf : ¬ IsPGroup 2 (D.V ⊔ D.V.map fi : Subgroup G) := by
    intro hh
    apply hn
    have hm := hh.map f
    rw [Subgroup.map_sup] at hm
    have he := conjugate_inverse D.V g⁻¹
    simp only [inv_inv] at he
    rw [he, sup_comm] at hm
    exact hm
  let F := commutatorPreimage (D.Vplus.map f) D.V D.V₁
  have hW : D.Vplus.map f ≤ D.H := by
    rintro _ ⟨a, ha, rfl⟩
    exact D.H.mul_mem (D.H.mul_mem hg (h.plus_le_H ha)) (D.H.inv_mem hg)
  have hZF : D.V₁ ≤ F := le_commutatorPreimage
    (by
      have hz' : D.V₁.map f = D.V₁ := mem_normalizer_iff_map_conj_eq.mp
        ((h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) hg)
      exact hz'.symm.le.trans (map_mono h.point_lt.le))
    (by
      have hc : ⁅D.V₁,D.V⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp (h.V_le_H.trans h.H_centralizes))
      exact hc.le.trans bot_le)
  apply le_antisymm _ hZF
  have hF : F.map fi ≤ commutatorPreimage D.Vplus (D.V.map fi) D.V₁ := by
    apply le_commutatorPreimage
    · exact (map_mono (commutatorPreimage_le (D.Vplus.map f) D.V D.V₁)).trans_eq
        (conjugate_inverse D.Vplus g)
    · have hc := map_mono (f := fi) (commutator_commutatorPreimage_le
        (D.Vplus.map f) D.V D.V₁
        (hW.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))))
      rwa [map_commutator, hz] at hc
  have he := h.pair_seed_fixed_eq_point hp g⁻¹ (D.H.inv_mem hg) hnf
  have hmap : F.map fi ≤ D.V₁.map fi := hz.symm ▸ hF.trans he.le
  exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hmap
end CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
