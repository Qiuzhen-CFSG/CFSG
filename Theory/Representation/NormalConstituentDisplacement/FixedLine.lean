module

public import Theory.Representation.NormalConstituentDisplacement
public import Theory.Representation.Clifford
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod

/-!
# Normal constituents detected by a fixed displacement plane

Let an irreducible binary representation restrict to a normal subgroup whose
simple constituents have degree greater than the displacement rank of `v`.
Clifford theory makes the restriction semisimple, and the small-displacement
lemma makes every subrepresentation invariant under `v`. The sum of those
fixed pointwise by `v` has an invariant complement disjoint from the moved
space. If a two-subgroup centralizing `v` has all its fixed vectors in that
moved space, orbit counting forces this sum to vanish.

For displacement rank two, at most two simple summands remain. Distinct
Clifford conjugates give the complementary summands of equal degree, and
rank additivity gives displacement rank one on each.

This supplies the missing nonzero-displacement justification in
Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.57(2), p.1148.
-/

public section

open scoped MonoidAlgebra
open Representation
namespace Representation.NormalConstituentDisplacement

variable {k H W : Type*} [Field k] [Group H] [AddCommGroup W] [Module k W]

private theorem submodule_iSup {ρ : Representation k H W} {ι : Sort*}
    (A : ι → Subrepresentation ρ) :
    (⨆ i, A i).toSubmodule = ⨆ i, (A i).toSubmodule := by
  let B : Subrepresentation ρ := ⟨⨆ i, (A i).toSubmodule, by
    intro g v hv
    exact Submodule.iSup_induction _ (motive := fun w => ρ g w ∈ ⨆ i, (A i).toSubmodule)
      hv (fun i w hw => le_iSup (fun i => (A i).toSubmodule) i
        ((A i).apply_mem_toSubmodule g hw))
      (by simp) (fun _ _ h h' => by simpa only [map_add] using Submodule.add_mem _ h h')⟩
  exact le_antisymm
    (iSup_le fun i => show A i ≤ B from le_iSup (fun i => (A i).toSubmodule) i)
    (iSup_le fun i => show A i ≤ ⨆ j, A j from le_iSup A i)

/-- Clifford semisimplicity, with the actual group algebra module. -/
theorem restriction_semisimple [FiniteDimensional k W]
    (ρ : Representation k H W) (hρ : ρ.IsIrreducible)
    (K : Subgroup H) [K.Normal] :
    IsSemisimpleModule k[K] (Representation.asModule (ρ.comp K.subtype)) := by
  let := hρ
  let := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨J, hJ⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp K.subtype)
  let e : Subrepresentation (ρ.comp K.subtype) ≃o
      Submodule k[K] (Representation.asModule (ρ.comp K.subtype)) :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  apply IsSemisimpleModule.of_sSup_simples_eq_top
  apply top_unique
  have htop := congrArg e (iSup_conjugateSubrepresentations_eq_top ρ K hρ J hJ)
  rw [e.map_iSup, e.map_top] at htop
  rw [← htop]
  refine iSup_le fun g => le_sSup ?_
  apply isSimpleModule_iff_isAtom.mpr
  apply (e.isAtom_iff _).mpr
  simpa using ((conjugateSubrepresentationOrderIso ρ K g⁻¹).isAtom_iff J).mpr
    ((Subrepresentation.irreducible_iff_isAtom J).mp hJ)

private theorem all_invariant [FiniteDimensional k W]
    (ρ : Representation k H W) (hρ : ρ.IsIrreducible)
    (K : Subgroup H) [K.Normal] (v : H)
    (hsmall : ∀ J : Subrepresentation (ρ.comp K.subtype), J.toRepresentation.IsIrreducible →
      Module.finrank k (LinearMap.range (ρ v - LinearMap.id)) <
        Module.finrank k J.toSubmodule)
    (A : Subrepresentation (ρ.comp K.subtype)) :
    A.toSubmodule.map (ρ v) = A.toSubmodule := by
  let := restriction_semisimple ρ hρ K
  let e : Subrepresentation (ρ.comp K.subtype) ≃o
      Submodule k[K] (Representation.asModule (ρ.comp K.subtype)) :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  let : IsAtomistic (Subrepresentation (ρ.comp K.subtype)) :=
    e.symm.isAtomistic_of_isAtomistic inferInstance
  let c := conjugateSubrepresentationOrderIso ρ K v
  have hc (J : Subrepresentation (ρ.comp K.subtype)) (hJ : IsAtom J) : c J = J := by
    apply Subrepresentation.toSubmodule_injective
    rw [show c = conjugateSubrepresentationOrderIso ρ K v from rfl,
      conjugateSubrepresentationOrderIso_toSubmodule]
    exact map_constituent_eq_self_of_displacement_lt ρ K v J
      ((Subrepresentation.irreducible_iff_isAtom J).mpr hJ)
      (hsmall J ((Subrepresentation.irreducible_iff_isAtom J).mpr hJ))
  have hs : c '' {J | IsAtom J ∧ J ≤ A} = {J | IsAtom J ∧ J ≤ A} := by
    ext J
    constructor
    · rintro ⟨B, hB, rfl⟩
      rwa [hc B hB.1]
    · intro hJ
      exact ⟨J, hJ, hc J hJ.1⟩
  have he : c A = A := calc
    c A = c (sSup {J | IsAtom J ∧ J ≤ A}) := congrArg c (sSup_atoms_le_eq A).symm
    _ = sSup (c '' {J | IsAtom J ∧ J ≤ A}) := by rw [c.map_sSup, sSup_image]
    _ = A := by rw [hs, sSup_atoms_le_eq]
  simpa only [c, conjugateSubrepresentationOrderIso_toSubmodule] using
    congrArg Subrepresentation.toSubmodule he

private theorem invariant_displacement_le (ρ : Representation k H W) (v : H)
    (A : Submodule k W) (hA : A.map (ρ v) = A) :
    A.map (ρ v - LinearMap.id) ≤ A := by
  rintro _ ⟨w, hw, rfl⟩
  exact A.sub_mem (hA ▸ (Submodule.mem_map_of_mem hw)) hw

private theorem compl_submodules (ρ : Representation k H W)
    (A B : Subrepresentation ρ) (h : IsCompl A B) :
    IsCompl A.toSubmodule B.toSubmodule := by
  let e : Subrepresentation ρ ≃o Submodule k[H] ρ.asModule :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  have hs := congrArg (fun P : Submodule k[H] ρ.asModule => P.restrictScalars k)
    ((e.isCompl_iff.mp h).sup_eq_top)
  rw [Submodule.restrictScalars_sup] at hs
  exact ⟨disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule h.inf_eq_bot),
    codisjoint_iff.mpr hs⟩

/-- The sum of all submodules on which the marked involution is trivial is zero.
The earlier source input is that every Sylow-fixed vector lies in its displacement plane. -/
theorem nonzero_displacement [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) H W) (hρ : ρ.IsIrreducible)
    (K T : Subgroup H) [K.Normal] (v : H)
    (hT : IsPGroup 2 T) (hcomm : ∀ t : T, Commute v (t : H))
    (hfixed : ∀ w : W, (∀ t : T, ρ t w = w) → w ∈ LinearMap.range (ρ v - LinearMap.id))
    (hsmall : ∀ J : Subrepresentation (ρ.comp K.subtype), J.toRepresentation.IsIrreducible →
      Module.finrank (ZMod 2) (LinearMap.range (ρ v - LinearMap.id)) <
        Module.finrank (ZMod 2) J.toSubmodule)
    (A : Subrepresentation (ρ.comp K.subtype)) (hA : A ≠ ⊥) :
    A.toSubmodule.map (ρ v - LinearMap.id) ≠ ⊥ := by
  let δ := ρ v - LinearMap.id
  let S : Subrepresentation (ρ.comp K.subtype) :=
    ⨆ B : {B : Subrepresentation (ρ.comp K.subtype) // B.toSubmodule ≤ LinearMap.ker δ}, B.val
  have hSker : S.toSubmodule ≤ LinearMap.ker δ := by
    dsimp only [S]
    rw [submodule_iSup]
    exact iSup_le fun B => B.property
  have hSstable (t : T) (w : W) (hw : w ∈ S.toSubmodule) : ρ t w ∈ S.toSubmodule := by
    have hc : conjugateSubrepresentationOrderIso ρ K t S ≤ S := by
      dsimp only [S]
      rw [OrderIso.map_iSup]
      refine iSup_le fun B => ?_
      let C := conjugateSubrepresentationOrderIso ρ K t B.val
      have hC : C.toSubmodule ≤ LinearMap.ker δ := by
        rw [conjugateSubrepresentationOrderIso_toSubmodule]
        rintro _ ⟨x, hx, rfl⟩
        have hx' : ρ v x = x := sub_eq_zero.mp (B.property hx)
        have hm := congrArg (fun g => ρ g x) (hcomm t).eq
        simp only [map_mul, Module.End.mul_apply] at hm
        change ρ v (ρ t x) - ρ t x = 0
        rw [hm, hx', sub_self]
      exact le_iSup_of_le ⟨C, hC⟩ le_rfl
    apply hc
    change ρ t w ∈ (conjugateSubrepresentationOrderIso ρ K t S).toSubmodule
    rw [conjugateSubrepresentationOrderIso_toSubmodule]
    exact ⟨w, hw, rfl⟩
  let : IsSemisimpleModule (ZMod 2)[K] (Representation.asModule (ρ.comp K.subtype)) :=
    restriction_semisimple ρ hρ K
  let e : Subrepresentation (ρ.comp K.subtype) ≃o
      Submodule (ZMod 2)[K] (Representation.asModule (ρ.comp K.subtype)) :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  let : ComplementedLattice (Subrepresentation (ρ.comp K.subtype)) := e.symm.complementedLattice
  obtain ⟨C, hSC⟩ := exists_isCompl S
  have hSC' := compl_submodules (ρ.comp K.subtype) S C hSC
  have hDC : LinearMap.range δ ≤ C.toSubmodule := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
      (show w ∈ S.toSubmodule ⊔ C.toSubmodule by rw [hSC'.sup_eq_top]; trivial)
    rw [map_add, show δ a = 0 from hSker ha, zero_add]
    exact invariant_displacement_le ρ v C.toSubmodule (all_invariant ρ hρ K v hsmall C)
      (Submodule.mem_map_of_mem hb)
  have hSbot : S = ⊥ := by
    by_contra hne
    have hne' : S.toSubmodule ≠ ⊥ := fun h => hne (Subrepresentation.toSubmodule_injective h)
    let : Nontrivial S.toSubmodule := (Submodule.nontrivial_iff_ne_bot).mpr hne'
    let : MulAction T S.toSubmodule := {
      smul t w := ⟨ρ t w, hSstable t w w.property⟩
      one_smul w := by apply Subtype.ext; exact congrArg (fun f => f w.val) ρ.map_one
      mul_smul t u w := by apply Subtype.ext; exact congrArg (fun f => f w.val) (ρ.map_mul t u) }
    have hcard : 2 ∣ Nat.card S.toSubmodule := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
      exact dvd_pow_self 2 (ne_of_gt (Module.finrank_pos_iff.mpr inferInstance))
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨w, hw, hne⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (α := S.toSubmodule) hcard
      (show (0 : S.toSubmodule) ∈ MulAction.fixedPoints T S.toSubmodule by
        intro t; apply Subtype.ext; exact map_zero (ρ t))
    have hwD : w.val ∈ LinearMap.range δ := hfixed w.val (fun t => congrArg Subtype.val (hw t))
    exact hne (Subtype.ext ((Submodule.disjoint_def.mp hSC'.disjoint)
      w.val w.property (hDC hwD)).symm)
  intro hzero
  have hle : A.toSubmodule ≤ LinearMap.ker δ := by
    intro w hw
    have hm := Submodule.mem_map_of_mem (f := δ) hw
    rw [show A.toSubmodule.map δ = ⊥ from hzero] at hm
    exact hm
  have hAS : A ≤ S := le_iSup_of_le ⟨A, hle⟩ le_rfl
  exact hA (le_bot_iff.mp (hAS.trans_eq hSbot))

private theorem sup_submodule (ρ : Representation k H W)
    (A B : Subrepresentation ρ) :
    (A ⊔ B).toSubmodule = A.toSubmodule ⊔ B.toSubmodule := by
  let e : Subrepresentation ρ ≃o Submodule k[H] ρ.asModule :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  have h := congrArg (fun P : Submodule k[H] ρ.asModule => P.restrictScalars k)
    (e.map_sup A B)
  rw [Submodule.restrictScalars_sup] at h
  exact h

private theorem displacement_rank_sup [FiniteDimensional k W]
    (ρ : Representation k H W) (v : H) (A B : Submodule k W)
    (hAB : Disjoint A B) (hA : A.map (ρ v) = A) (hB : B.map (ρ v) = B) :
    Module.finrank k (A.map (ρ v - LinearMap.id)) +
      Module.finrank k (B.map (ρ v - LinearMap.id)) =
        Module.finrank k ((A ⊔ B).map (ρ v - LinearMap.id)) := by
  have hd := hAB.mono (invariant_displacement_le ρ v A hA)
    (invariant_displacement_le ρ v B hB)
  have hr := (A.map (ρ v - LinearMap.id)).finrank_sup_add_finrank_inf_eq
    (B.map (ρ v - LinearMap.id))
  rw [hd.eq_bot, finrank_bot, add_zero, ← Submodule.map_sup] at hr
  exact hr.symm

/-- The complete constituent alternative from the genuine fixed-plane input.
Clifford conjugates have equal degree; three independent nonzero displacements
would exceed the rank-two plane. -/
theorem constituent_alternative [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) H W) (hρ : ρ.IsIrreducible)
    (K T : Subgroup H) [K.Normal] (v : H) (d : ℕ)
    (hT : IsPGroup 2 T) (hcomm : ∀ t : T, Commute v (t : H))
    (hfixed : ∀ w : W, (∀ t : T, ρ t w = w) → w ∈ LinearMap.range (ρ v - LinearMap.id))
    (hsmall : ∀ J : Subrepresentation (ρ.comp K.subtype), J.toRepresentation.IsIrreducible →
      3 ≤ Module.finrank (ZMod 2) J.toSubmodule)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (ρ v - LinearMap.id)) = 2)
    (hdim : Module.finrank (ZMod 2) W = 2 * d) :
    ⁅K, Subgroup.zpowers v⁆ ≠ ⊥ ∧
      (Representation.IsIrreducible (ρ.comp K.subtype) ∨
        ∃ J L : Subrepresentation (ρ.comp K.subtype),
          IsCompl J.toSubmodule L.toSubmodule ∧
          J.toRepresentation.IsIrreducible ∧ L.toRepresentation.IsIrreducible ∧
          Module.finrank (ZMod 2) J.toSubmodule = d ∧
          Module.finrank (ZMod 2) L.toSubmodule = d ∧
          J.toSubmodule.map (ρ v) = J.toSubmodule ∧
          L.toSubmodule.map (ρ v) = L.toSubmodule ∧
          Module.finrank (ZMod 2)
            (LinearMap.range ((ρ v - LinearMap.id).comp J.toSubmodule.subtype)) = 1 ∧
          Module.finrank (ZMod 2)
            (LinearMap.range ((ρ v - LinearMap.id).comp L.toSubmodule.subtype)) = 1) := by
  have hsmall' (J : Subrepresentation (ρ.comp K.subtype)) (hJ : J.toRepresentation.IsIrreducible) :
      Module.finrank (ZMod 2) (LinearMap.range (ρ v - LinearMap.id)) <
        Module.finrank (ZMod 2) J.toSubmodule := by rw [hrank]; exact hsmall J hJ
  refine ⟨commutator_zpowers_ne_bot_of_small_displacement ρ K v hsmall'
    (by rw [hrank]; decide), ?_⟩
  let := hρ
  let := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨J, hJ⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp K.subtype)
  have hJa := (Subrepresentation.irreducible_iff_isAtom J).mp hJ
  by_cases hJtop : J = ⊤
  · exact Or.inl (isSimpleOrder_iff_isAtom_top.mpr (hJtop ▸ hJa))
  right
  obtain ⟨g, hg⟩ : ∃ g : H, conjugateSubrepresentation ρ K J g ≠ J := by
    by_contra! h
    apply hJtop
    apply top_unique
    rw [← iSup_conjugateSubrepresentations_eq_top ρ K hρ J hJ]
    exact iSup_le fun g => (h g).le
  let L := conjugateSubrepresentation ρ K J g
  have hLa : IsAtom L := by
    simpa [L] using ((conjugateSubrepresentationOrderIso ρ K g⁻¹).isAtom_iff J).mpr hJa
  have hL := (Subrepresentation.irreducible_iff_isAtom L).mpr hLa
  have hdJL : Disjoint J.toSubmodule L.toSubmodule :=
    disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule (hJa.disjoint_of_ne hLa hg.symm).eq_bot)
  have hi (A : Subrepresentation (ρ.comp K.subtype)) := all_invariant ρ hρ K v hsmall' A
  have hp (A : Subrepresentation (ρ.comp K.subtype)) (hA : A ≠ ⊥) :
      0 < Module.finrank (ZMod 2) (A.toSubmodule.map (ρ v - LinearMap.id)) := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact nonzero_displacement ρ hρ K T v hT hcomm hfixed hsmall' A hA
      (Submodule.finrank_eq_zero.mp hz)
  have hpJ := hp J hJa.ne_bot
  have hpL := hp L hLa.ne_bot
  have hsumJL := displacement_rank_sup ρ v J.toSubmodule L.toSubmodule hdJL (hi J) (hi L)
  have hJLtop : J ⊔ L = ⊤ := by
    let : IsSemisimpleModule (ZMod 2)[K] (Representation.asModule (ρ.comp K.subtype)) :=
      restriction_semisimple ρ hρ K
    let e : Subrepresentation (ρ.comp K.subtype) ≃o
        Submodule (ZMod 2)[K] (Representation.asModule (ρ.comp K.subtype)) :=
      Subrepresentation.subrepresentationSubmoduleOrderIso
    let : ComplementedLattice (Subrepresentation (ρ.comp K.subtype)) := e.symm.complementedLattice
    obtain ⟨C, hC⟩ := exists_isCompl (J ⊔ L)
    have hC' := compl_submodules (ρ.comp K.subtype) (J ⊔ L) C hC
    have hsum := displacement_rank_sup ρ v (J ⊔ L).toSubmodule C.toSubmodule
      hC'.disjoint (hi (J ⊔ L)) (hi C)
    rw [hC'.sup_eq_top, Submodule.map_top, hrank, sup_submodule] at hsum
    by_cases hCbot : C = ⊥
    · simpa only [hCbot, sup_bot_eq] using hC.sup_eq_top
    · have hpC := hp C hCbot
      omega
  have hcompl : IsCompl J.toSubmodule L.toSubmodule := by
    refine ⟨hdJL, codisjoint_iff.mpr ?_⟩
    rw [← sup_submodule, hJLtop]; rfl
  have heq : Module.finrank (ZMod 2) J.toSubmodule =
      Module.finrank (ZMod 2) L.toSubmodule :=
    (Submodule.equivMapOfInjective (ρ g⁻¹) (ρ.apply_bijective g⁻¹).injective J.toSubmodule).finrank_eq
  have hsumdim := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [hdim] at hsumdim
  have hrange (A : Submodule (ZMod 2) W) :
      LinearMap.range ((ρ v - LinearMap.id).comp A.subtype) = A.map (ρ v - LinearMap.id) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [hcompl.sup_eq_top, Submodule.map_top, hrank] at hsumJL
  refine ⟨J, L, hcompl, hJ, hL, ?_, ?_, hi J, hi L, ?_, ?_⟩
  · omega
  · omega
  · rw [hrange]; omega
  · rw [hrange]; omega

/-- A nontrivial normal subgroup generates the whole moved space in a faithful
irreducible representation. The commutator is the literal sum of action differences. -/
theorem normal_commutator_span_eq_top
    (ρ : Representation k H W) (hρ : ρ.IsIrreducible) (hfaith : Function.Injective ρ)
    (K : Subgroup H) [K.Normal] (hne : K ≠ ⊥) :
    (⨆ a : K, LinearMap.range (ρ a - LinearMap.id)) = ⊤ := by
  let D : Subrepresentation ρ := {
    toSubmodule := ⨆ a : K, LinearMap.range (ρ a - LinearMap.id)
    apply_mem_toSubmodule h w hw := by
      apply Submodule.iSup_induction _ (motive := fun w =>
        ρ h w ∈ ⨆ a : K, LinearMap.range (ρ a - LinearMap.id)) hw
      · intro a w hw
        obtain ⟨x, rfl⟩ := hw
        let b : K := ⟨h * a * h⁻¹, (inferInstance : K.Normal).conj_mem a a.property h⟩
        apply le_iSup (fun a : K => LinearMap.range (ρ a - LinearMap.id)) b
        refine ⟨ρ h x, ?_⟩
        change ρ (h * a * h⁻¹) (ρ h x) - ρ h x = ρ h (ρ a x - x)
        simp [map_mul, map_sub, Module.End.mul_apply]
      · simp
      · intro a b ha hb
        simpa only [map_add] using Submodule.add_mem _ ha hb }
  let := hρ
  have hD : D ≠ ⊥ := by
    intro hbot
    apply hne
    apply bot_unique
    intro a ha
    apply hfaith
    apply LinearMap.ext
    intro x
    have hm : ρ a x - x ∈ D.toSubmodule :=
      le_iSup (fun a : K => LinearMap.range (ρ a - LinearMap.id)) ⟨a, ha⟩ ⟨x, rfl⟩
    have hd := congrArg Subrepresentation.toSubmodule hbot
    rw [hd] at hm
    simpa only [map_one, Module.End.one_apply] using sub_eq_zero.mp hm
  have ht := (IsSimpleOrder.eq_bot_or_eq_top D).resolve_left hD
  exact congrArg Subrepresentation.toSubmodule ht


end Representation.NormalConstituentDisplacement
