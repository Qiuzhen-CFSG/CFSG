module
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Overgroups
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Rank-one generation from solvable Mathieu local subgroups

A generating family of Sylow overgroups passes its intrinsic E-generation to
its ambient group by the corrected local-tau inheritance theorem. In particular,
an actual S₃ two-core quotient gives a solvable group and hence rank-one
E-generation. The ambient reductions use self-centralization of F*(G): a
centerless model makes its conjugation action faithful, and an inner-only
automorphism group makes F*(G) equal G.

These are the reductions used for the Mathieu cases of Aschbacher–Smith,
*The Classification of Quasithin Groups*, E.1.12–14, printed p.214.
The model modules discharge the local-family and automorphism premises.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.MathieuOne
variable {G M : Type*} [Group G] [Finite G] [Group M]

/-- E.1.12 at rank one, using intrinsic E-members with the corrected local tau. -/
theorem isEGenerated_of_family (T : Sylow 2 G) (Δ : Set (Subgroup G))
    (hgen : sSup Δ = ⊤)
    (hlocal : ∀ H ∈ Δ, (T : Subgroup G) ≤ H ∧ IsEGenerated 1 H) :
    IsEGenerated 1 G := by
  apply IsEGeneratedAt.isEGenerated (T := T)
  intro Ω hΩ
  apply top_unique
  change ⊤ ≤ ChiefOrbit.generationTarget 1 T Ω
  rw [← hgen]
  exact sSup_le fun H hH => ChiefOrbit.overgroup_le_generationTarget T H
    (hlocal H hH).1 hΩ (hlocal H hH).2

/-- An S₃ quotient above the intrinsic two-core makes the whole group solvable. -/
theorem isSolvable_of_symmetricThree_twoCore_quotient
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) : Group.IsSolvable G := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      (by rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker])
  let : Group.IsSolvable (G ⧸ pCore 2 G) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsNilpotent (pCore 2 G) := (pCore_isPGroup (p := 2) (G := G)).isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 G)).mpr ⟨inferInstance, inferInstance⟩

/-- Two generating Sylow overgroups with S₃ two-core quotients give the bound. -/
theorem isEGenerated_of_symmetricThree_pair (T : Sylow 2 G) (H J : Subgroup G)
    (hH : (T : Subgroup G) ≤ H) (hJ : (T : Subgroup G) ≤ J) (hj : H ⊔ J = ⊤)
    (eH : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))
    (eJ : (J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3)) : IsEGenerated 1 G := by
  apply isEGenerated_of_family T {H,J}
  · simpa only [sSup_pair] using hj
  · intro A hA
    rcases hA with rfl | hA
    · let := isSolvable_of_symmetricThree_twoCore_quotient eH
      exact ⟨hH, isEGenerated_one_of_solvable⟩
    · have he : A = J := hA
      subst A
      let := isSolvable_of_symmetricThree_twoCore_quotient eJ
      exact ⟨hJ, isEGenerated_one_of_solvable⟩

/-- A centerless model of F*(G) makes its ambient conjugation action faithful. -/
theorem centralizer_generalizedFitting_eq_bot_of_equiv
    (e : generalizedFitting G ≃* M) (hz : center M = ⊥) :
    centralizer (generalizedFitting G : Set G) = ⊥ := by
  apply le_bot_iff.mp
  intro g hg
  let l : generalizedFitting G := ⟨g, centralizer_generalizedFitting_le G hg⟩
  have he : e l ∈ center M := by
    apply mem_center_iff.mpr
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    simpa only [map_mul] using congrArg e
      (show y * l = l * y from Subtype.ext (hg y y.property))
  rw [hz, mem_bot] at he
  have hl : l = 1 := e.injective (he.trans e.map_one.symm)
  exact congrArg Subtype.val hl

/-- Innerness of all model automorphisms rules out a proper ambient extension. -/
theorem ambient_equiv_of_inner_automorphisms
    (e : generalizedFitting G ≃* M)
    (hi : Function.Surjective (MulAut.conj : M →* MulAut M)) :
    Nonempty (G ≃* M) := by
  have htop : generalizedFitting G = ⊤ := by
    apply top_unique
    intro g _
    let a := MulAut.conjNormal (H := generalizedFitting G) g
    obtain ⟨m, hm⟩ := hi ((MulAut.congr e) a)
    have hl : MulAut.conj (e.symm m) = a := by
      apply (MulAut.congr e).injective
      rw [MulAut.congr_conj, e.apply_symm_apply]
      exact hm
    have hc : (e.symm m : G)⁻¹ * g ∈ centralizer (generalizedFitting G : Set G) := by
      intro x hx
      have he := congrArg Subtype.val (DFunLike.congr_fun hl ⟨x,hx⟩)
      change (e.symm m : G) * x * (e.symm m : G)⁻¹ = g * x * g⁻¹ at he
      calc
        x * ((e.symm m : G)⁻¹ * g) =
            (e.symm m : G)⁻¹ * ((e.symm m : G) * x * (e.symm m : G)⁻¹) * g := by group
        _ = (e.symm m : G)⁻¹ * (g * x * g⁻¹) * g := by rw [he]
        _ = ((e.symm m : G)⁻¹ * g) * x := by group
    have hmem := centralizer_generalizedFitting_le G hc
    simpa only [mul_inv_cancel_left] using
      (generalizedFitting G).mul_mem (e.symm m).property hmem
  exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans e⟩
end CFSG.Quasithin.ChapterE.MathieuOne
