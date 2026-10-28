module
public import Theory.Representation.FixedIsotypicCentralizer
public import Theory.Representation.IsotypicCopies
public import Theory.Representation.SubrepresentationLattice
public import Theory.Representation.Quotient
public import Theory.Representation.NormalPairSupport

/-!
# Homogeneous coordinates for a separated normal simple pair

The two factor pullbacks of an automorphism-invariant simple type have spans
whose sum is invariant under the ambient actor. Ambient irreducibility makes
that sum the full module. Complementary fixed-space supports then identify
each span with one support. Canonical isotypic coordinates and an actual
exchange give equal positive multiplicity, with the literal factor actions.

The binary A₅ application uses G.9.3 to discharge invariance of each simple
type and marks the resulting copies by the natural or deleted module.
Source: Aschbacher–Smith D.3.5–6 and the separated branch of 10.2,
combined manuscript, D.3.5–6 and §10.2.
-/

public noncomputable section
open Representation Module Theory.GroupTheory
open scoped MonoidAlgebra
namespace Representation.NormalPairHomogeneous
variable {k S Q V E : Type*} [Field k] [Group S] [Group Q]
  [AddCommGroup V] [Module k V] [AddCommGroup E] [Module k E]

/-- The span of all copies is the canonical isotypic component. -/
theorem typeSpan_eq_isotypic (τ : Representation k S V)
    (σ : Representation k S E) [σ.IsIrreducible] :
    typeSpan τ σ = Subrepresentation.ofSubmodule'
      (isotypicComponent k[S] τ.asModule σ.asModule) := by
  apply le_antisymm (typeSpan_le_isotypicComponent τ σ)
  change isotypicComponent k[S] τ.asModule σ.asModule ≤ (typeSpan τ σ).asSubmodule
  apply sSup_le
  intro A hA
  obtain ⟨e⟩ := hA
  let l : σ.asModule →ₗ[k[S]] τ.asModule := A.subtype.comp e.symm.toLinearMap
  let f : σ.IntertwiningMap τ := (IntertwiningMap.equivLinearMapAsModule σ τ).symm l
  intro v hv
  exact (show f.range ≤ typeSpan τ σ from le_iSup _ f)
    ⟨σ.asModuleEquiv (e ⟨v,hv⟩), by
      change A.subtype (e.symm (e ⟨v,hv⟩)) = v
      rw [e.symm_apply_apply]
      rfl⟩

/-- A marked conjugating operator transports the literal span of model copies. -/
theorem typeSpan_map_of_covariance
    (τ υ : Representation k S V) (σ η : Representation k S E)
    (T : V →ₗ[k] V) (a : MulAut S) (c : E ≃ₗ[k] E)
    (hT : ∀ s v, T (τ s v) = υ (a s) (T v))
    (hc : ∀ s v, c (σ s v) = η (a s) (c v)) :
    (typeSpan τ σ).toSubmodule.map T ≤ (typeSpan υ η).toSubmodule := by
  let R := typeSpan υ η
  let P : Subrepresentation τ := {
    toSubmodule := R.toSubmodule.comap T
    apply_mem_toSubmodule s v hv := by
      change T (τ s v) ∈ R.toSubmodule
      rw [hT]
      exact R.apply_mem_toSubmodule (a s) hv }
  have hle : typeSpan τ σ ≤ P := by
    apply iSup_le
    intro f
    let f' : η.IntertwiningMap υ := {
      toLinearMap := T.comp (f.toLinearMap.comp c.symm.toLinearMap)
      isIntertwining' s := by
        apply LinearMap.ext
        intro v
        change T (f (c.symm (η s v))) = υ s (T (f (c.symm v)))
        have he : c.symm (η s v) = σ (a.symm s) (c.symm v) := by
          apply c.injective
          rw [c.apply_symm_apply, hc, a.apply_symm_apply, c.apply_symm_apply]
        rw [he, f.isIntertwining, hT, a.apply_symm_apply] }
    rintro v ⟨w,rfl⟩
    exact (show f'.range ≤ R from le_iSup _ f')
      ⟨c w, by change T (f (c.symm (c w))) = T (f w); rw [c.symm_apply_apply]⟩
  rintro _ ⟨v,hv,rfl⟩
  exact hle hv

section Pair
variable [Finite S] [IsQuasisimple S]
  (ρ : Representation k Q V) (i : S × S →* Q)
  (σ : Representation k S E)

abbrev leftType : Representation k (S × S) E := σ.comp (MonoidHom.fst S S)
abbrev rightType : Representation k (S × S) E := σ.comp (MonoidHom.snd S S)

theorem pair_typeSpan_sup_eq_top (hi : Function.Injective i) [i.range.Normal]
    (hZ : Subgroup.center S = ⊥) [ρ.IsIrreducible]
    (htwist : ∀ a : MulAut S, ∃ c : E ≃ₗ[k] E,
      ∀ s v, c (σ s v) = σ (a s) (c v))
    (f : (leftType σ).IntertwiningMap (ρ.comp i)) (hf : f ≠ 0) :
    (typeSpan (ρ.comp i) (leftType σ)).toSubmodule ⊔
      (typeSpan (ρ.comp i) (rightType σ)).toSubmodule = ⊤ := by
  let A := typeSpan (ρ.comp i) (leftType σ)
  let B := typeSpan (ρ.comp i) (rightType σ)
  have hcov (g : Q) (a : MulAut (S × S))
      (ha : ∀ z, g * i z * g⁻¹ = i (a z)) (z : S × S) (v : V) :
      ρ g ((ρ.comp i) z v) = (ρ.comp i) (a z) (ρ g v) := by
    change ρ g (ρ (i z) v) = ρ (i (a z)) (ρ g v)
    rw [←ha]
    simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]
  have hstable (g : Q) :
      (A.toSubmodule.map (ρ g) ≤ A.toSubmodule ∧
        B.toSubmodule.map (ρ g) ≤ B.toSubmodule) ∨
      (A.toSubmodule.map (ρ g) ≤ B.toSubmodule ∧
        B.toSubmodule.map (ρ g) ≤ A.toSubmodule) := by
    rcases NormalPairSupport.covariance_alternatives i hi hZ g with
      ⟨a,b,hab⟩ | ⟨a,b,hab⟩
    · obtain ⟨c,hc⟩ := htwist a
      obtain ⟨d,hd⟩ := htwist b
      let α : MulAut (S × S) := MulEquiv.prodCongr a b
      have hα : ∀ z, g * i z * g⁻¹ = i (α z) := fun z => hab z.1 z.2
      exact Or.inl ⟨typeSpan_map_of_covariance (ρ.comp i) (ρ.comp i)
        (leftType σ) (leftType σ) (ρ g) α c (hcov g α hα)
          (fun z v => hc z.1 v),
        typeSpan_map_of_covariance (ρ.comp i) (ρ.comp i)
        (rightType σ) (rightType σ) (ρ g) α d (hcov g α hα)
          (fun z v => hd z.2 v)⟩
    · obtain ⟨c,hc⟩ := htwist b
      obtain ⟨d,hd⟩ := htwist a
      let α : MulAut (S × S) := MulEquiv.prodComm.trans (MulEquiv.prodCongr a b)
      have hα : ∀ z, g * i z * g⁻¹ = i (α z) := fun z => hab z.1 z.2
      exact Or.inr ⟨typeSpan_map_of_covariance (ρ.comp i) (ρ.comp i)
        (leftType σ) (rightType σ) (ρ g) α c (hcov g α hα)
          (fun z v => hc z.1 v),
        typeSpan_map_of_covariance (ρ.comp i) (ρ.comp i)
        (rightType σ) (leftType σ) (ρ g) α d (hcov g α hα)
          (fun z v => hd z.2 v)⟩
  let U : Subrepresentation ρ := {
    toSubmodule := A.toSubmodule ⊔ B.toSubmodule
    apply_mem_toSubmodule g v hv := by
      obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add]
      rcases hstable g with h | h
      · exact Submodule.add_mem_sup (h.1 ⟨x,hx,rfl⟩) (h.2 ⟨y,hy,rfl⟩)
      · simpa only [add_comm] using
          Submodule.add_mem_sup (h.2 ⟨y,hy,rfl⟩) (h.1 ⟨x,hx,rfl⟩) }
  have hU : U ≠ ⊥ := by
    intro h
    apply hf
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    have hv : f v ∈ U.toSubmodule :=
      (show A.toSubmodule ≤ A.toSubmodule ⊔ B.toSubmodule from le_sup_left)
        ((show f.range ≤ A from le_iSup _ f) ⟨v,rfl⟩)
    have hz : U.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h
    have hm : f v ∈ (⊥ : Submodule k V) := hz ▸ hv
    exact hm
  exact congrArg Subrepresentation.toSubmodule
    ((IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hU)

@[expose] def leftSupport : Subrepresentation (ρ.comp i) := {
    toSubmodule := NormalPairSupport.left ρ i
    apply_mem_toSubmodule z v hv := by
      intro s
      change ρ (i (1,s)) (ρ (i z) v) = ρ (i z) v
      have hz : (1,s) * z = z * (1,z.2⁻¹*s*z.2) := by
        ext <;> simp [mul_assoc]
      rw [←Module.End.mul_apply,←map_mul,←map_mul,hz,map_mul,map_mul,Module.End.mul_apply]
      exact congrArg (ρ (i z)) (hv (z.2⁻¹*s*z.2)) }

@[expose] def rightSupport : Subrepresentation (ρ.comp i) := {
    toSubmodule := NormalPairSupport.right ρ i
    apply_mem_toSubmodule z v hv := by
      intro s
      change ρ (i (s,1)) (ρ (i z) v) = ρ (i z) v
      have hz : (s,1) * z = z * (z.1⁻¹*s*z.1,1) := by
        ext <;> simp [mul_assoc]
      rw [←Module.End.mul_apply,←map_mul,←map_mul,hz,map_mul,map_mul,Module.End.mul_apply]
      exact congrArg (ρ (i z)) (hv (z.1⁻¹*s*z.1)) }

abbrev leftAction : Representation k S (NormalPairSupport.left ρ i) :=
  (leftSupport ρ i).toRepresentation.comp (MonoidHom.inl S S)
abbrev rightAction : Representation k S (NormalPairSupport.right ρ i) :=
  (rightSupport ρ i).toRepresentation.comp (MonoidHom.inr S S)

omit [Finite S] [IsQuasisimple S] in
/-- Each pulled-back model span belongs to its literal support block. -/
theorem left_typeSpan_le_support :
    (typeSpan (ρ.comp i) (leftType σ)).toSubmodule ≤ NormalPairSupport.left ρ i := by
  let P := leftSupport ρ i
  change typeSpan (ρ.comp i) (leftType σ) ≤ P
  apply iSup_le
  intro f v hv
  obtain ⟨w,rfl⟩ := hv
  intro s
  change ρ (i (1,s)) (f w) = f w
  have h := Representation.IntertwiningMap.isIntertwining (leftType σ) (ρ.comp i) f (1,s) w
  change f (σ 1 w) = ρ (i (1,s)) (f w) at h
  simpa only [map_one,Module.End.one_apply] using h.symm

omit [Finite S] [IsQuasisimple S] in
theorem right_typeSpan_le_support :
    (typeSpan (ρ.comp i) (rightType σ)).toSubmodule ≤ NormalPairSupport.right ρ i := by
  let P := rightSupport ρ i
  change typeSpan (ρ.comp i) (rightType σ) ≤ P
  apply iSup_le
  intro f v hv
  obtain ⟨w,rfl⟩ := hv
  intro s
  change ρ (i (s,1)) (f w) = f w
  have h := Representation.IntertwiningMap.isIntertwining (rightType σ) (ρ.comp i) f (s,1) w
  change f (σ 1 w) = ρ (i (s,1)) (f w) at h
  simpa only [map_one,Module.End.one_apply] using h.symm

private theorem eq_of_complementary_spans {A B L R : Submodule k V}
    (hA : A ≤ L) (hB : B ≤ R) (hs : A ⊔ B = ⊤) (hd : Disjoint L R) : A = L := by
  apply le_antisymm hA
  intro v hv
  have ht : v ∈ A ⊔ B := hs.symm ▸ Submodule.mem_top
  obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp ht
  have hyL : y ∈ L := by
    have he : y = v - x := by rw [←hxy]; abel
    rw [he]
    exact L.sub_mem hv (hA hx)
  have hy0 : y = 0 := Submodule.disjoint_def.mp hd y hyL (hB hy)
  have hxv : x = v := by simpa only [hy0,add_zero] using hxy
  exact hxv ▸ hx

/-- Both canonical support blocks are homogeneous in the same simple type. -/
theorem pair_typeSpans_eq_supports (hi : Function.Injective i) [i.range.Normal]
    [Nontrivial S] (hZ : Subgroup.center S = ⊥) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ)
    (htwist : ∀ a : MulAut S, ∃ c : E ≃ₗ[k] E,
      ∀ s v, c (σ s v) = σ (a s) (c v))
    (f : (leftType σ).IntertwiningMap (ρ.comp i)) (hf : f ≠ 0) :
    (typeSpan (ρ.comp i) (leftType σ)).toSubmodule = NormalPairSupport.left ρ i ∧
    (typeSpan (ρ.comp i) (rightType σ)).toSubmodule = NormalPairSupport.right ρ i := by
  have hs := pair_typeSpan_sup_eq_top ρ i σ hi hZ htwist f hf
  have hd := NormalPairSupport.support_disjoint ρ i hi hρ
  exact ⟨eq_of_complementary_spans (left_typeSpan_le_support ρ i σ)
      (right_typeSpan_le_support ρ i σ) hs hd,
    eq_of_complementary_spans (right_typeSpan_le_support ρ i σ)
      (left_typeSpan_le_support ρ i σ) (by simpa only [sup_comm] using hs) hd.symm⟩


omit [Finite S] [IsQuasisimple S] in
/-- Faithfulness rules out the trivial simple model on a separated support. -/
theorem left_type_nontrivial (hi : Function.Injective i) [i.range.Normal]
    [Nontrivial S] [ρ.IsIrreducible] (hρ : Function.Injective ρ)
    (f : (leftType σ).IntertwiningMap (ρ.comp i)) (hf : f ≠ 0) :
    ∃ s, σ s ≠ 1 := by
  by_contra! hσ
  apply hf
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have hvL : f v ∈ NormalPairSupport.left ρ i := left_typeSpan_le_support ρ i σ
    ((show f.range ≤ typeSpan (ρ.comp i) (leftType σ) from le_iSup _ f) ⟨v,rfl⟩)
  have hvR : f v ∈ NormalPairSupport.right ρ i := by
    intro s
    change ρ (i (s,1)) (f v) = f v
    have h := Representation.IntertwiningMap.isIntertwining (leftType σ) (ρ.comp i)
      f (s,1) v
    change f (σ s v) = ρ (i (s,1)) (f v) at h
    simpa only [hσ,Module.End.one_apply] using h.symm
  exact Submodule.disjoint_def.mp (NormalPairSupport.support_disjoint ρ i hi hρ)
    (f v) hvL hvR

/-- Equal positive copy coordinates retain the two literal factor actions. -/
structure Coordinates where
  multiplicity : ℕ
  positive : 0 < multiplicity
  leftEquiv : NormalPairSupport.left ρ i ≃ₗ[k] (Fin multiplicity → E)
  rightEquiv : NormalPairSupport.right ρ i ≃ₗ[k] (Fin multiplicity → E)
  left_intertwines : ∀ s v,
    leftEquiv (leftAction ρ i s v) = fun j => σ s (leftEquiv v j)
  right_intertwines : ∀ s v,
    rightEquiv (rightAction ρ i s v) = fun j => σ s (rightEquiv v j)

variable {E' : Type*} [AddCommGroup E'] [Module k E']

/-- Changing the marked simple model changes every copy by the same map. -/
def Coordinates.changeModel (C : Coordinates ρ i σ)
    {τ : Representation k S E'} (e : σ.Equiv τ) : Coordinates ρ i τ where
  multiplicity := C.multiplicity
  positive := C.positive
  leftEquiv := C.leftEquiv.trans (LinearEquiv.piCongrRight fun _ => e.toLinearEquiv)
  rightEquiv := C.rightEquiv.trans (LinearEquiv.piCongrRight fun _ => e.toLinearEquiv)
  left_intertwines s v := by
    change (fun j => e (C.leftEquiv (leftAction ρ i s v) j)) =
      (fun j => τ s (e (C.leftEquiv v j)))
    rw [C.left_intertwines]
    funext j
    exact Representation.IntertwiningMap.isIntertwining σ τ e.toIntertwiningMap s _
  right_intertwines s v := by
    change (fun j => e (C.rightEquiv (rightAction ρ i s v) j)) =
      (fun j => τ s (e (C.rightEquiv v j)))
    rw [C.right_intertwines]
    funext j
    exact Representation.IntertwiningMap.isIntertwining σ τ e.toIntertwiningMap s _

omit [Finite S] [IsQuasisimple S] in
/-- Changing the simple model preserves the multiplicity of the same witness. -/
@[simp] theorem Coordinates.changeModel_multiplicity (C : Coordinates ρ i σ)
    {τ : Representation k S E'} (e : σ.Equiv τ) :
    (Coordinates.changeModel ρ i σ C e).multiplicity = C.multiplicity := by rfl

variable [FiniteDimensional k V] [FiniteDimensional k E] [σ.IsIrreducible]

/-- Literal finite-copy coordinates on both normal-pair supports. -/
theorem pair_copy_coordinates (hi : Function.Injective i) [i.range.Normal]
    [Nontrivial S] (hZ : Subgroup.center S = ⊥) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ)
    (htwist : ∀ a : MulAut S, ∃ c : E ≃ₗ[k] E,
      ∀ s v, c (σ s v) = σ (a s) (c v))
    (f : (leftType σ).IntertwiningMap (ρ.comp i)) (hf : f ≠ 0)
    (exchange : NormalPairSupport.left ρ i ≃ₗ[k] NormalPairSupport.right ρ i) :
    Nonempty (Coordinates ρ i σ) := by
  let : (leftType σ).IsIrreducible :=
    (irreducible_comp_surjective_iff (MonoidHom.fst S S)
      (fun s => ⟨(s,1),rfl⟩) σ).mpr inferInstance
  let : (rightType σ).IsIrreducible :=
    (irreducible_comp_surjective_iff (MonoidHom.snd S S)
      (fun s => ⟨(1,s),rfl⟩) σ).mpr inferInstance
  obtain ⟨hL,hR⟩ := pair_typeSpans_eq_supports ρ i σ hi hZ hρ htwist f hf
  rw [typeSpan_eq_isotypic] at hL hR
  obtain ⟨n,a,ha⟩ := SchurCopies.isotypic_finite_rep_coordinates (ρ.comp i) (leftType σ)
  obtain ⟨m,b,hb⟩ := SchurCopies.isotypic_finite_rep_coordinates (ρ.comp i) (rightType σ)
  let eL := (LinearEquiv.ofEq _ _ hL.symm).trans a
  let eR := (LinearEquiv.ofEq _ _ hR.symm).trans b
  have heL (s : S) (v : NormalPairSupport.left ρ i) :
      eL (leftAction ρ i s v) = fun j => σ s (eL v j) := by
    exact ha (s,1) ((LinearEquiv.ofEq _ _ hL.symm) v)
  have heR (s : S) (v : NormalPairSupport.right ρ i) :
      eR (rightAction ρ i s v) = fun j => σ s (eR v j) := by
    exact hb (1,s) ((LinearEquiv.ofEq _ _ hR.symm) v)
  let : Nontrivial E := Subrepresentation.irreducible_module_nontrivial σ
  have hdim : n * Module.finrank k E = m * Module.finrank k E := by
    calc
      n * Module.finrank k E = Module.finrank k (NormalPairSupport.left ρ i) := by
        simpa [Module.finrank_pi_fintype] using eL.finrank_eq.symm
      _ = Module.finrank k (NormalPairSupport.right ρ i) := exchange.finrank_eq
      _ = m * Module.finrank k E := by simpa [Module.finrank_pi_fintype] using eR.finrank_eq
  have hnm : n = m := Nat.eq_of_mul_eq_mul_right
    (Module.finrank_pos_iff.mpr inferInstance) hdim
  subst m
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    apply hf
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    have hv : f v ∈ NormalPairSupport.left ρ i := left_typeSpan_le_support ρ i σ
      ((show f.range ≤ typeSpan (ρ.comp i) (leftType σ) from le_iSup _ f) ⟨v,rfl⟩)
    have hz : eL ⟨f v,hv⟩ = eL 0 := by funext j; exact j.elim0
    exact congrArg Subtype.val (eL.injective hz)
  exact ⟨⟨n,hn,eL,eR,heL,heR⟩⟩


end Pair

section Selection
variable (ρ : Representation k Q V) (i : S × S →* Q) [FiniteDimensional k V]

/-- A nonzero support supplies a simple model and a nonzero map for the
whole product action, with the other factor acting identically. -/
theorem exists_simple_left_type (hL : NormalPairSupport.left ρ i ≠ ⊥) :
    ∃ A : Subrepresentation (leftAction ρ i), A.toRepresentation.IsIrreducible ∧
      ∃ f : (leftType A.toRepresentation).IntertwiningMap (ρ.comp i), f ≠ 0 := by
  let : Nontrivial (NormalPairSupport.left ρ i) := Submodule.nontrivial_iff_ne_bot.mpr hL
  obtain ⟨A,hA⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (leftAction ρ i)
  let f : (leftType A.toRepresentation).IntertwiningMap (ρ.comp i) := {
    toLinearMap := (NormalPairSupport.left ρ i).subtype.comp A.toSubmodule.subtype
    isIntertwining' z := by
      apply LinearMap.ext
      intro v
      change ρ (i (z.1,1)) v.val.val = ρ (i z) v.val.val
      have hz : z = (z.1,1) * (1,z.2) := by simp
      conv_rhs => rw [hz,map_mul,map_mul,Module.End.mul_apply]
      exact (congrArg (ρ (i (z.1,1))) (v.val.property z.2)).symm }
  refine ⟨A,hA,f,?_⟩
  let : A.toRepresentation.IsIrreducible := hA
  let : Nontrivial A.toSubmodule := Subrepresentation.irreducible_module_nontrivial
    A.toRepresentation
  obtain ⟨v,hv⟩ := exists_ne (0 : A.toSubmodule)
  intro hf
  apply hv
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun g : (leftType A.toRepresentation).IntertwiningMap (ρ.comp i) => g v) hf

end Selection
end Representation.NormalPairHomogeneous
