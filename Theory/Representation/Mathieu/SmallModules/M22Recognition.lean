module

public import Theory.Representation.Mathieu.SmallModules.Models
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.PointRestriction
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Irreducibility
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Pairing
public import Theory.Representation.SubrepresentationLattice

/-!
# Recognition of small faithful binary M22 modules

A nontrivial irreducible quotient of the native permutation module must occur
in its Golay filtration. The constant line, augmentation quotient, pair line
and code-hyperplane quotient have dimension one. The remaining factors are
exactly the ten-dimensional code hyperplane and pair-line cocode quotient.
Schur's lemma therefore gives an actual representation equivalence to one of
these two modules.

A vector fixed by the native point stabilizer extends along its orbit to an
equivariant permutation-module map. The native coordinate pairing handles the
contragredient alternative without changing the group marking. Faithfulness
and the order-eleven lower bound force the degree-ten-to-twelve window.
The point-stabilizer theorem supplies a fixed vector in the restricted module
or its dual throughout that window, using the proved binary PSL(3,4)
simple-degree gap and retaining nonsplit extensions. Thus `of_small_degree`
recognizes every faithful irreducible binary M22 module of degree at most
twelve as one of the two literal ten-dimensional modules.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.7.3(2),
printed p.348, and H.13.1, printed p.395. The completeness assertion cited
there is G. D. James, J. Algebra 27 (1973), 57--111.
-/

public section
open Representation Sporadic.Mathieu MathieuCode
noncomputable section
namespace Representation.MathieuSmall.M22Recognition

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

/-- The native M22 action on all twenty-four coordinates. -/
abbrev ambient : Representation (ZMod 2) M22 Full := fullRepresentation.comp m22Embedding

/-- A nonzero map from the native permutation module to an irreducible of
 dimension greater than one identifies one of the two literal ten-spaces. -/
theorem of_ambient_quotient {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) M22 V)
    [ρ.IsIrreducible] (hd : 1 < Module.finrank (ZMod 2) V)
    (f : ambient.IntertwiningMap ρ) (hf : f ≠ 0) : IsM22ToddOrDual ρ := by
  let coreR : Representation (ZMod 2) M22 Core := coreRepresentation.comp m22Embedding
  let golayR : Representation (ZMod 2) M22 golay := golayRepresentation.comp m22Embedding
  let codeR : Representation (ZMod 2) M22 Code := codeRepresentation.comp m22Embedding
  let cocodeR : Representation (ZMod 2) M22 Cocode := cocodeRepresentation.comp m22Embedding
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
    let lineR : Representation (ZMod 2) M22 m22PairLine := m22PairLineSubrepresentation.toRepresentation.comp m22ToPairStabilizer
    let lineIncl : lineR.IntertwiningMap cocodeR := ⟨m22PairLine.subtype, fun _ => rfl⟩
    have hl : q.comp lineIncl = 0 := map_eq_zero_of_dim_lt _ (by
      simpa only [finrank_m22PairLine] using hd)
    have hkl : m22PairLine ≤ LinearMap.ker q.toLinearMap := by
      intro v hv
      exact congrArg (fun k : lineR.IntertwiningMap ρ => k ⟨v, hv⟩) hl
    let t : m22CocodeRepresentation.IntertwiningMap ρ :=
      ⟨m22PairLine.liftQ q.toLinearMap hkl, by
        intro g
        apply LinearMap.ext
        intro v
        induction v using Submodule.Quotient.induction_on with
        | _ v => exact LinearMap.congr_fun (q.isIntertwining' g) v⟩
    have ht : t ≠ 0 := by
      intro hz
      apply hq
      ext v
      exact congrArg (fun k : m22CocodeRepresentation.IntertwiningMap ρ =>
        k (m22PairLine.mkQ v)) hz
    let : m22CocodeRepresentation.IsIrreducible := m22Cocode_isIrreducible
    exact ⟨MulEquiv.refl _, Or.inl ⟨(t.ofBijective
      ((IsIrreducible.bijective_or_eq_zero t).resolve_right ht)).symm⟩⟩
  · let lineR : Representation (ZMod 2) M22 codeLine := codeLineSubrepresentation.toRepresentation.comp m22Embedding
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
    let j : m22CodeRepresentation.IntertwiningMap codeR :=
      ⟨m22CodeInclusion, fun _ => rfl⟩
    have ht : q.comp j ≠ 0 := comp_ne_zero_of_codim_lt q hq j
      m22CodeInclusion_injective (by rw [finrank_code, finrank_m22Code]; omega)
    let : m22CodeRepresentation.IsIrreducible := m22Code_isIrreducible
    exact ⟨MulEquiv.refl _, Or.inr ⟨((q.comp j).ofBijective
      ((IsIrreducible.bijective_or_eq_zero _).resolve_right ht)).symm⟩⟩


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

private def codeDuality {G : Type*} [Group G] (e : G →* M22) :
    Representation.Equiv (m22CodeRepresentation.comp e) (Representation.dual (m22CocodeRepresentation.comp e)) :=
  Representation.Equiv.mk m22CodeCocodeDuality (by
    intro g
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro u
    change m22CodeCocodeDuality (m22CodeRepresentation (e g) v) u =
      m22CodeCocodeDuality v (m22CocodeRepresentation (e g⁻¹) u)
    rw [map_inv]
    exact LinearMap.congr_fun (m22CodeCocodeDuality_equivariant_native (e g) v) u)

/-- Recognition is stable under the genuine contragredient action, using
 the native coordinate pairing and the original group marking. -/
theorem of_dual {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (h : IsM22ToddOrDual ρ.dual) :
    IsM22ToddOrDual ρ := by
  obtain ⟨e, h⟩ := h
  rcases h with h | h
  · obtain ⟨E⟩ := h
    exact ⟨e, Or.inr ⟨(evalEquiv ρ).trans ((dualEquiv E).trans
      (codeDuality e.toMonoidHom).symm)⟩⟩
  · obtain ⟨E⟩ := h
    exact ⟨e, Or.inl ⟨(evalEquiv ρ).trans ((dualEquiv E).trans
      ((dualEquiv (codeDuality e.toMonoidHom)).trans
        (evalEquiv (m22CocodeRepresentation.comp e.toMonoidHom)).symm))⟩⟩

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
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) M22 V)
    [ρ.IsIrreducible] (hd : 1 < Module.finrank (ZMod 2) V)
    (hfixed : Representation.invariants (ρ.comp (MulAction.stabilizer M22 (0 : Fin 22)).subtype) ≠ ⊥) :
    IsM22ToddOrDual ρ := by
  classical
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfixed
  let : MulAction.IsPretransitive M22 (Fin 22) := m22_isPretransitive
  have htrans (i : Fin 22) : ∃ g : M22, g • (0 : Fin 22) = i :=
    MulAction.exists_smul_eq M22 0 i
  let lift (i : Fin 22) : M22 := Classical.choose (htrans i)
  have hlift (i : Fin 22) : lift i • (0 : Fin 22) = i := Classical.choose_spec (htrans i)
  let value (i : Fin 22) : V := ρ (lift i) v
  have hvalue (g : M22) (i : Fin 22) (hg : g • (0 : Fin 22) = i) : value i = ρ g v := by
    have hm : (lift i)⁻¹ * g ∈ MulAction.stabilizer M22 (0 : Fin 22) := by
      change ((lift i)⁻¹ * g) • (0 : Fin 22) = 0
      rw [mul_smul, hg]
      exact (congrArg (fun j => (lift i)⁻¹ • j) (hlift i).symm).trans (inv_smul_smul _ _)
    have hh := hv ⟨(lift i)⁻¹ * g, hm⟩
    change ρ ((lift i)⁻¹ * g) v = v at hh
    have he := congrArg (ρ (lift i)) hh
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at he
    exact he.symm
  have hvalue_o : value 0 = v := by simpa using hvalue 1 0 (one_smul _ _)
  have hvalue_act (g : M22) (i : Fin 22) : value (g • i) = ρ g (value i) := by
    rw [hvalue (g * lift i) _ (by rw [mul_smul, hlift]), map_mul]
    rfl
  let perm : Representation (ZMod 2) M22 (Fin 22 → ZMod 2) :=
    (BinaryPermutation.representation (Fin 22)).comp M22.subtype
  let f : perm.IntertwiningMap ρ := {
    toLinearMap := {
      toFun a := ∑ i : Fin 22, a i • value i
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [mul_smul, Finset.smul_sum] }
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro a
      change (∑ i : Fin 22, a (g.val.symm i) • value i) =
        ρ g (∑ i : Fin 22, a i • value i)
      rw [map_sum]
      simp only [map_smul, ← hvalue_act]
      exact (Equiv.sum_comp g.val
        (fun i => a (g.val.symm i) • value i)).symm.trans (by
          simp only [_root_.Equiv.symm_apply_apply, MulAction.subgroup_smul_def, Equiv.Perm.smul_def]) }
  have hf : f (Pi.single 0 1) = v := by
    change (∑ i : Fin 22, (Pi.single 0 (1 : ZMod 2) : Fin 22 → ZMod 2) i • value i) = v
    simp [hvalue_o]
  let r : ambient.IntertwiningMap perm := {
    toLinearMap := {
      toFun a i := a (m22Coordinates i)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro a
      funext i
      change a ((m22Embedding g).val.symm (m22Coordinates i)) =
        a (m22Coordinates (g.val.symm i))
      have he := m22Embedding_apply g⁻¹ i
      rw [map_inv] at he
      exact congrArg a he }
  have r_apply (a : Full) (i : Fin 22) : r a i = a (m22Coordinates i) := rfl
  have hr : r (Pi.single (m22Coordinates 0) 1) = Pi.single 0 1 := by
    funext i
    rw [r_apply]
    simp only [Pi.single_apply, m22Coordinates.injective.eq_iff]
  apply of_ambient_quotient ρ hd (f.comp r)
  intro hz
  have he := congrArg (fun t : ambient.IntertwiningMap ρ =>
    t (Pi.single (m22Coordinates 0) 1)) hz
  change f (r _) = 0 at he
  rw [hr, hf] at he
  exact hv0 he

/-- The remaining local recognition input is fixedness for the original
 point-stabilizer action or its contragredient. No character table is assumed. -/
theorem of_point_fixed_or_dual {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) M22 V)
    [ρ.IsIrreducible] (hd : 1 < Module.finrank (ZMod 2) V)
    (hfixed : Representation.invariants (ρ.comp (MulAction.stabilizer M22 (0 : Fin 22)).subtype) ≠ ⊥ ∨
      Representation.invariants (ρ.dual.comp (MulAction.stabilizer M22 (0 : Fin 22)).subtype) ≠ ⊥) :
    IsM22ToddOrDual ρ := by
  rcases hfixed with h | h
  · exact of_point_fixed ρ hd h
  · let : IsIrreducible ρ.dual := irreducible_dual ρ
    exact of_dual ρ (of_point_fixed ρ.dual (by simpa only [Subspace.dual_finrank_eq] using hd) h)


/-- Conditional assembly for the precise small-degree source window. The sole
remaining premise is a local fixed-vector theorem for arbitrary modules of the
actual point stabilizer; it is not a Mathieu recognition assumption. -/
theorem of_small_degree_of_local_fixed_vectors
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) M22 V)
    (hfaithful : Function.Injective ρ) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 12)
    (hlocal : ∀ τ : Representation (ZMod 2) (MulAction.stabilizer M22 (0 : Fin 22)) V,
      10 ≤ Module.finrank (ZMod 2) V → Module.finrank (ZMod 2) V ≤ 12 →
        τ.invariants ≠ ⊥ ∨ τ.dual.invariants ≠ ⊥) : IsM22ToddOrDual ρ := by
  have hlo := BinaryPrimeDegree.orderOf_le_finrank ρ hfaithful
    (by decide : Nat.Prime 11) (by decide : 11 ≠ 2) (by rw [m22_order]; norm_num)
  rw [BinaryPrimeDegree.orderOf_two_mod_eleven] at hlo
  apply of_point_fixed_or_dual ρ (by omega)
  exact hlocal (ρ.comp (MulAction.stabilizer M22 (0 : Fin 22)).subtype) hlo hd

/-- Every faithful irreducible binary representation of the actual M22 of
degree at most twelve is the native Todd module or its code dual. This proves
the simple-M22 recognition input to G.7.3(2), with no local classification
premise remaining. -/
theorem of_small_degree
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) M22 V)
    (hfaithful : Function.Injective ρ) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 12) : IsM22ToddOrDual ρ :=
  of_small_degree_of_local_fixed_vectors ρ hfaithful hd PointRestriction.fixed_or_dual

end Representation.MathieuSmall.M22Recognition
