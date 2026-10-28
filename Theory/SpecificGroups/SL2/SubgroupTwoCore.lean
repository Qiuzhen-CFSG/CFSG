module

public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic
public import Theory.PGroupCore

/-!
# Two-core control in subgroups of SL₂

Over a finite field of characteristic two, every two-subgroup of a subgroup
with nontrivial intrinsic two-core lies in that core.

Sylow conjugacy puts the core inside the upper unipotent group. The lower-left
entry of a conjugated nonidentity root element forces every normalizer of the
core to be upper triangular. The inverse image of the upper unipotent group is
therefore a normal two-subgroup of the original subgroup. Every two-subgroup
lies in this inverse image, by the Sylow normalizer theorem, and hence lies in
the intrinsic core. Normality is used only inside the original subgroup.

The root-normalizer calculation works over any field. The two-core consequence
supplies the rank-one local input for Aschbacher–Smith, `refs/quasithin.pdf`,
E.1.14(1), printed p.214, citing Aschbacher [Asc82a], Lemma 4.7.
-/

open Matrix
open scoped MatrixGroups Pointwise
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F]
local notation "u" => transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one

/-- A normalizer of a nontrivial subgroup of the upper root group preserves
its fixed line, and therefore normalizes the whole upper root group. -/
public theorem normalizer_le_rankOneBorel_of_le_upperUnipotent
    (W : Subgroup (SL(2, F))) (hWU : W ≤ upperUnipotent F)
    (hne : W ≠ ⊥) : Subgroup.normalizer (W : Set (SL(2, F))) ≤ rankOneBorel F := by
  rcases W.bot_or_exists_ne_one with h | ⟨w, hw, hw1⟩
  · exact (hne h).elim
  obtain ⟨t, rfl⟩ := (mem_upperUnipotent F w).mp (hWU hw)
  have ht : t ≠ 0 := by
    intro h
    subst t
    exact hw1 (transvection_coeff_zero _)
  intro g hg
  apply (mem_rankOneBorel_iff g).mpr
  have hu : g * u t * g⁻¹ ∈ upperUnipotent F :=
    hWU ((Subgroup.mem_normalizer_iff.mp hg _).mp hw)
  obtain ⟨s, hs⟩ := (mem_upperUnipotent F _).mp hu
  have he := congrArg (fun A : SL(2, F) => A.val 1 0) hs
  simp [adjugate_fin_two, mul_apply, Fin.sum_univ_two, transvection_coe] at he
  have hz : t * (g.val 1 0 * g.val 1 0) = 0 := by linear_combination he
  exact mul_self_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left ht)

variable [Finite F] [CharP F 2]

/-- If a subgroup of SL₂ has nontrivial intrinsic two-core, all its
two-subgroups lie in that core. This includes the field with two elements. -/
public theorem isPGroup_le_twoCore_of_ne_bot (R : Subgroup (SL(2, F))) (hne : pCore 2 R ≠ ⊥)
    (B : Subgroup R) (hB : IsPGroup 2 B) : B ≤ pCore 2 R := by
  let N := (pCore 2 R).map R.subtype
  obtain ⟨P, hNP⟩ := (pCore_isPGroup (p := 2) (G := R)).map R.subtype |>.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL(2, F)) P (upperUnipotentSylow F 2)
  let f : R →* SL(2, F) := (MulAut.conj g).toMonoidHom.comp R.subtype
  have hf : Function.Injective f := (MulAut.conj g).injective.comp Subtype.coe_injective
  let W := (pCore 2 R).map f
  have hWU : W ≤ upperUnipotent F := by
    calc
      W = N.map (MulAut.conj g).toMonoidHom := (Subgroup.map_map _ _ _).symm
      _ ≤ (P : Subgroup (SL(2, F))).map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hNP
      _ = upperUnipotent F := by
        change (g • P : Sylow 2 (SL(2, F))).toSubgroup = _
        rw [hg]
        rfl
  have hW : W ≠ ⊥ := fun h => hne (((pCore 2 R).map_eq_bot_iff_of_injective hf).mp h)
  have hfn : f.range ≤ Subgroup.normalizer (W : Set (SL(2, F))) := by
    have h := Subgroup.le_normalizer_map (H := pCore 2 R) f
    simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map] using h
  have hfb : f.range ≤ rankOneBorel F :=
    hfn.trans (normalizer_le_rankOneBorel_of_le_upperUnipotent W hWU hW)
  let D := (upperUnipotent F).comap f
  have hDnormal : D.Normal := by
    refine ⟨?_⟩
    intro x hx y
    change f (y * x * y⁻¹) ∈ upperUnipotent F
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hfb ⟨y, rfl⟩) _).mp hx
  have hDtwo : IsPGroup 2 D :=
    (upperUnipotentSylow F 2).isPGroup'.comap_of_injective f hf
  have hDc : D ≤ pCore 2 R := le_sSup ⟨hDnormal, hDtwo⟩
  apply le_trans ?_ hDc
  have hBn : B.map f ≤ Subgroup.normalizer (upperUnipotent F : Set (SL(2, F))) :=
    (Subgroup.map_le_range f B).trans hfb
  have hBU : B.map f ≤ upperUnipotent F := by
    calc
      B.map f = B.map f ⊓ Subgroup.normalizer (upperUnipotent F : Set (SL(2, F))) :=
        (inf_eq_left.mpr hBn).symm
      _ = B.map f ⊓ (upperUnipotentSylow F 2 : Subgroup (SL(2, F))) :=
        (hB.map f).inf_normalizer_sylow (upperUnipotentSylow F 2)
      _ ≤ upperUnipotent F := inf_le_right
  exact Subgroup.map_le_iff_le_comap.mp hBU

end Matrix.SpecialLinearGroup
