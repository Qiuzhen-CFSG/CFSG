module

public import Theory.Representation.Mathieu.SmallModules.M23Recognition.PointRestriction
public import Theory.Representation.MathieuCodeRestriction.Duality.Absolute.Irreducibility
public import Theory.Representation.MathieuCodeRestriction.Duality

/-!
# Recognition of the native eleven-dimensional binary M23 modules

Restrict an arbitrary eleven-dimensional representation to the actual M22
point stabilizer. Its simple-degree gap gives a fixed vector or a fixed
covector, even for a nonsplit restriction. The orbit sum of a fixed vector
constructs an equivariant map from the native permutation module.

The Golay filtration of that permutation module has, apart from trivial
lines, exactly the native eleven-dimensional code and cocode factors.
Irreducibility therefore identifies the given module with one of these
factors. The native coordinate pairing interchanges the alternatives in
the fixed-covector case. Both the linear equivalence and its pointwise
equivariance are retained, with the identity marking of the actual M23.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), K.4 opening,
printed p.457 (PDF p.468), and the definitions H.13.1--2, printed p.395;
Guralnick--Malle, Classification of 2F-modules I, Theorem 6.6/Table 6.7;
G. D. James, J. Algebra 27 (1973), 57--111. Only native completeness is
proved here; the Chapter K reduction to dimension eleven is separate.
-/

public section
open Representation Sporadic.Mathieu MathieuCode
noncomputable section

namespace Representation.MathieuSmall.M23Recognition

private theorem comp_ne_zero_of_codim_lt
    {G A B V : Type*} [Group G] [AddCommGroup A] [Module (ZMod 2) A]
    [AddCommGroup B] [Module (ZMod 2) B] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) A] [FiniteDimensional (ZMod 2) B]
    [FiniteDimensional (ZMod 2) V]
    {σ : Representation (ZMod 2) G A} {τ : Representation (ZMod 2) G B}
    {ρ : Representation (ZMod 2) G V} [ρ.IsIrreducible]
    (f : σ.IntertwiningMap ρ) (hf : f ≠ 0)
    (j : τ.IntertwiningMap σ) (hj : Function.Injective j)
    (hd : Module.finrank (ZMod 2) A <
      Module.finrank (ZMod 2) B + Module.finrank (ZMod 2) V) : f.comp j ≠ 0 := by
  intro hz
  have hs := (IsIrreducible.surjective_or_eq_zero f).resolve_right hf
  have hr := f.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at hr
  have hle : LinearMap.range j.toLinearMap ≤ LinearMap.ker f.toLinearMap := by
    rintro _ ⟨b, rfl⟩
    exact congrArg (fun k : τ.IntertwiningMap ρ => k b) hz
  have hk := Submodule.finrank_mono hle
  rw [LinearMap.finrank_range_of_inj hj] at hk
  omega

private theorem map_eq_zero_of_dim_lt
    {G A V : Type*} [Group G] [AddCommGroup A] [Module (ZMod 2) A]
    [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) A] [FiniteDimensional (ZMod 2) V]
    {σ : Representation (ZMod 2) G A} {ρ : Representation (ZMod 2) G V}
    [ρ.IsIrreducible] (f : σ.IntertwiningMap ρ)
    (hd : Module.finrank (ZMod 2) A < Module.finrank (ZMod 2) V) : f = 0 := by
  rcases IsIrreducible.surjective_or_eq_zero f with hs | hz
  · exact (not_le_of_gt hd (LinearMap.finrank_le_finrank_of_surjective hs)).elim
  · exact hz

/-- The native M23 action on all twenty-four coordinates. -/
abbrev ambient : Representation (ZMod 2) M23 Full := fullRepresentation.comp pointEmbedding

/-- A nonzero map from the native permutation module to an irreducible of
 dimension greater than one identifies the native code or cocode. -/
theorem of_ambient_quotient {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) M23 V)
    [ρ.IsIrreducible] (hd : 1 < Module.finrank (ZMod 2) V)
    (f : ambient.IntertwiningMap ρ) (hf : f ≠ 0) :
    Nonempty (ρ.Equiv m23CodeRepresentation) ∨
      Nonempty (ρ.Equiv m23CocodeRepresentation) := by
  let coreR : Representation (ZMod 2) M23 Core := coreRepresentation.comp pointEmbedding
  let golayR : Representation (ZMod 2) M23 golay := golayRepresentation.comp pointEmbedding
  let codeR : Representation (ZMod 2) M23 Code := codeRepresentation.comp pointEmbedding
  let cocodeR : Representation (ZMod 2) M23 Cocode := cocodeRepresentation.comp pointEmbedding
  let coreIncl : coreR.IntertwiningMap ambient := ⟨Core.subtype, fun _ => rfl⟩
  let golayIncl : golayR.IntertwiningMap coreR :=
    ⟨Submodule.inclusion golay_le_core, fun _ => rfl⟩
  let fc := f.comp coreIncl
  have hfc : fc ≠ 0 := comp_ne_zero_of_codim_lt f hf coreIncl Subtype.val_injective (by
    simp only [BinaryPermutation.finrank_full, Fintype.card_fin,
      BinaryPermutation.finrank_core]
    omega)
  let fg := fc.comp golayIncl
  by_cases hfg : fg = 0
  · have hk : codeInCore ≤ LinearMap.ker fc.toLinearMap := by
      intro v hv
      exact congrArg (fun k : golayR.IntertwiningMap ρ => k ⟨v.val, hv⟩) hfg
    let q : cocodeR.IntertwiningMap ρ :=
      ⟨codeInCore.liftQ fc.toLinearMap hk, by
        intro g
        apply LinearMap.ext
        intro v
        induction v using Submodule.Quotient.induction_on with
        | _ v => exact LinearMap.congr_fun (fc.isIntertwining' g) v⟩
    have hq : q ≠ 0 := by
      intro hz
      apply hfc
      ext v
      exact congrArg (fun k : cocodeR.IntertwiningMap ρ => k (codeInCore.mkQ v)) hz
    let : cocodeR.IsIrreducible := m23Cocode_isIrreducible
    exact Or.inr ⟨(q.ofBijective
      ((IsIrreducible.bijective_or_eq_zero q).resolve_right hq)).symm⟩
  · let lineR : Representation (ZMod 2) M23 codeLine :=
      codeLineSubrepresentation.toRepresentation.comp pointEmbedding
    let lineIncl : lineR.IntertwiningMap golayR := ⟨codeLine.subtype, fun _ => rfl⟩
    have hl : fg.comp lineIncl = 0 := map_eq_zero_of_dim_lt _ (by
      simpa only [finrank_codeLine] using hd)
    have hkl : codeLine ≤ LinearMap.ker fg.toLinearMap := by
      intro v hv
      exact congrArg (fun k : lineR.IntertwiningMap ρ => k ⟨v, hv⟩) hl
    let q : codeR.IntertwiningMap ρ :=
      ⟨codeLine.liftQ fg.toLinearMap hkl, by
        intro g
        apply LinearMap.ext
        intro v
        induction v using Submodule.Quotient.induction_on with
        | _ v => exact LinearMap.congr_fun (fg.isIntertwining' g) v⟩
    have hq : q ≠ 0 := by
      intro hz
      apply hfg
      ext v
      exact congrArg (fun k : codeR.IntertwiningMap ρ => k (codeLine.mkQ v)) hz
    let : codeR.IsIrreducible := m23Code_isIrreducible
    exact Or.inl ⟨(q.ofBijective
      ((IsIrreducible.bijective_or_eq_zero q).resolve_right hq)).symm⟩

private def dualEquiv {G V W : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) G W}
    (E : ρ.Equiv σ) : ρ.dual.Equiv σ.dual :=
  Representation.Equiv.mk E.symm.toLinearEquiv.dualMap (by
    intro g
    ext f v
    exact congrArg f (LinearMap.congr_fun (E.symm.toIntertwiningMap.isIntertwining' g⁻¹) v).symm)

private def evalEquiv {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) : ρ.Equiv ρ.dual.dual :=
  Representation.Equiv.mk (Module.evalEquiv (ZMod 2) V) (by
    intro g
    ext v f
    change f (ρ g v) = f (ρ (g⁻¹)⁻¹ v)
    rw [inv_inv])

private theorem irreducible_dual {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ] : IsIrreducible ρ.dual := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  refine ⟨fun W => ?_⟩
  let U : Subrepresentation ρ :=
    { toSubmodule := W.toSubmodule.dualCoannihilator
      apply_mem_toSubmodule g v hv := by
        rw [Submodule.mem_dualCoannihilator] at hv ⊢
        intro f hf
        have h := hv (ρ.dual g⁻¹ f) (W.apply_mem_toSubmodule g⁻¹ hf)
        simpa only [dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, inv_inv] using h }
  have hd : U.toSubmodule.dualAnnihilator = W.toSubmodule :=
    Subspace.dualCoannihilator_dualAnnihilator_eq
  rcases eq_bot_or_eq_top U with h | h
  · right
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, h]
    exact Submodule.dualAnnihilator_bot
  · left
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, h]
    exact Submodule.dualAnnihilator_top

/-- A fixed vector for the actual point stabilizer produces a map from the
 native permutation module, hence identifies a code or cocode module. -/
theorem of_point_fixed {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) M23 V)
    [ρ.IsIrreducible] (hd : 1 < Module.finrank (ZMod 2) V)
    (hfixed : Representation.invariants (ρ.comp (MulAction.stabilizer M23 (9 : Fin 23)).subtype) ≠ ⊥) :
    Nonempty (ρ.Equiv m23CodeRepresentation) ∨
      Nonempty (ρ.Equiv m23CocodeRepresentation) := by
  classical
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfixed
  let : MulAction.IsPretransitive M23 (Fin 23) := m23_isPretransitive
  have htrans (i : Fin 23) : ∃ g : M23, g • (9 : Fin 23) = i :=
    MulAction.exists_smul_eq M23 9 i
  let lift (i : Fin 23) : M23 := Classical.choose (htrans i)
  have hlift (i : Fin 23) : lift i • (9 : Fin 23) = i := Classical.choose_spec (htrans i)
  let value (i : Fin 23) : V := ρ (lift i) v
  have hvalue (g : M23) (i : Fin 23) (hg : g • (9 : Fin 23) = i) : value i = ρ g v := by
    have hm : (lift i)⁻¹ * g ∈ MulAction.stabilizer M23 (9 : Fin 23) := by
      change ((lift i)⁻¹ * g) • (9 : Fin 23) = 9
      rw [mul_smul, hg]
      exact (congrArg (fun j => (lift i)⁻¹ • j) (hlift i).symm).trans (inv_smul_smul _ _)
    have hh := hv ⟨(lift i)⁻¹ * g, hm⟩
    change ρ ((lift i)⁻¹ * g) v = v at hh
    have he := congrArg (ρ (lift i)) hh
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at he
    exact he.symm
  have hvalue_o : value 9 = v := by simpa using hvalue 1 9 (one_smul _ _)
  have hvalue_act (g : M23) (i : Fin 23) : value (g • i) = ρ g (value i) := by
    rw [hvalue (g * lift i) _ (by rw [mul_smul, hlift]), map_mul]
    rfl
  let perm : Representation (ZMod 2) M23 (Fin 23 → ZMod 2) :=
    (BinaryPermutation.representation (Fin 23)).comp M23.subtype
  let f : perm.IntertwiningMap ρ := {
    toLinearMap := {
      toFun a := ∑ i : Fin 23, a i • value i
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [mul_smul, Finset.smul_sum] }
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro a
      change (∑ i : Fin 23, a (g.val.symm i) • value i) =
        ρ g (∑ i : Fin 23, a i • value i)
      rw [map_sum]
      simp only [map_smul, ← hvalue_act]
      exact (Equiv.sum_comp g.val
        (fun i => a (g.val.symm i) • value i)).symm.trans (by
          simp only [_root_.Equiv.symm_apply_apply, MulAction.subgroup_smul_def, Equiv.Perm.smul_def]) }
  have hf : f (Pi.single 9 1) = v := by
    change (∑ i : Fin 23, (Pi.single 9 (1 : ZMod 2) : Fin 23 → ZMod 2) i • value i) = v
    simp [hvalue_o]
  let r : ambient.IntertwiningMap perm := {
    toLinearMap := {
      toFun a i := a (m23PointEmbedding i)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro a
      funext i
      change a ((pointEmbedding g).val.symm (m23PointEmbedding i)) =
        a (m23PointEmbedding (g.val.symm i))
      have he := pointEmbedding_apply g⁻¹ i
      rw [map_inv] at he
      exact congrArg a he }
  have r_apply (a : Full) (i : Fin 23) : r a i = a (m23PointEmbedding i) := rfl
  have hr : r (Pi.single (m23PointEmbedding 9) 1) = Pi.single 9 1 := by
    funext i
    rw [r_apply]
    simp only [Pi.single_apply, m23PointEmbedding.injective.eq_iff]
  apply of_ambient_quotient ρ hd (f.comp r)
  intro hz
  have he := congrArg (fun t : ambient.IntertwiningMap ρ =>
    t (Pi.single (m23PointEmbedding 9) 1)) hz
  change f (r _) = 0 at he
  rw [hr, hf] at he
  exact hv0 he

/-- Native equivariant recognition in dimension eleven, with the identity
marking of M23. The restriction argument does not require faithfulness. -/
theorem equiv_code_or_cocode_of_degree_eleven
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) M23 V)
    [ρ.IsIrreducible] (hd : Module.finrank (ZMod 2) V = 11) :
    Nonempty (ρ.Equiv m23CodeRepresentation) ∨
      Nonempty (ρ.Equiv m23CocodeRepresentation) := by
  rcases PointRestriction.fixed_or_dual
      (ρ.comp (MulAction.stabilizer M23 (9 : Fin 23)).subtype) hd with h | h
  · exact of_point_fixed ρ (by omega) h
  · let : IsIrreducible ρ.dual := irreducible_dual ρ
    rcases of_point_fixed ρ.dual (by simpa only [Subspace.dual_finrank_eq] using
      (show 1 < Module.finrank (ZMod 2) V by omega)) h with hE | hE
    · obtain ⟨E⟩ := hE
      exact Or.inr ⟨(evalEquiv ρ).trans ((dualEquiv E).trans m23CocodeDuality.symm)⟩
    · obtain ⟨E⟩ := hE
      exact Or.inl ⟨(evalEquiv ρ).trans ((dualEquiv E).trans m23CodeDuality.symm)⟩

/-- Every faithful irreducible binary representation of M23 of dimension eleven
is the native restriction of the M24 code or cocode, with actual equivariance. -/
theorem of_degree_eleven
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) M23 V)
    (_hfaithful : Function.Injective ρ) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V = 11) : IsM23Code ρ ∨ IsM23Cocode ρ := by
  rcases equiv_code_or_cocode_of_degree_eleven ρ hd with hE | hE
  · obtain ⟨E⟩ := hE
    exact Or.inl ⟨MulEquiv.refl _, E.toLinearEquiv,
      fun g v => LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' g) v⟩
  · obtain ⟨E⟩ := hE
    exact Or.inr ⟨MulEquiv.refl _, E.toLinearEquiv,
      fun g v => LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' g) v⟩

end Representation.MathieuSmall.M23Recognition
