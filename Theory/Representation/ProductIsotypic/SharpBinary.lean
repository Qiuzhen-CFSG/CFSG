module
public import Theory.Representation.ProductIsotypic.Nonabelian
public import Theory.Representation.BinaryParabolicNatural.RepeatedOffender
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.SpecificGroups.PSL3Two.ProperSubgroups
public import Theory.Representation.BinaryFullLinearRecognition

/-!
# Sharp binary product actions

An irreducible product action with a nonabelian commuting factor has more
than one copy of its first-factor constituent. Displacement three therefore
forces exactly three copies and displacement one on the constituent. A
commuting endomorphism preserves that fixed hyperplane. Its scalar action
on the one-dimensional quotient determines it everywhere by irreducibility,
so the constituent is absolutely irreducible. Schur coordinates now construct
an actual external tensor, with a three-dimensional multiplicity action.

A faithful perfect multiplicity actor is the full binary linear three-group:
its proper subgroups are solvable. The resulting group equivalence retains
the literal matrix action, rather than recognizing a group by an order tag.

Source application: Aschbacher--Smith 13.1.9, printed p.871, the scalar-field
and canonical-factor identification after equality in (*). The common-chief
consumer supplies the faithful perfect factor and the sharp displacement.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.ProductIsotypic
variable {G H V : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- An irreducible binary action with a fixed hyperplane has scalar commutant. -/
theorem absolute_of_fixedCodim_one (σ : Representation (ZMod 2) G V)
    [IsIrreducible σ] (A : Subgroup G) (hd : fixedCodim σ A = 1) :
    IsAbsolutelyIrreducible σ := by
  apply (isAbsolutelyIrreducible_iff_surjective σ).mpr
  intro f
  let C := fixedSpace σ A
  have hC : C ≤ C.comap f.toLinearMap := by
    intro v hv a
    exact (IntertwiningMap.isIntertwining σ σ f a v).symm.trans (congrArg f (hv a))
  let q : (V ⧸ C) →ₗ[ZMod 2] (V ⧸ C) := C.mapQ C f.toLinearMap hC
  obtain ⟨c,hc,_⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hd q
  have hzero : f - algebraMap (ZMod 2) (End σ) c = 0 := by
    rcases IsIrreducible.surjective_or_eq_zero (f - algebraMap (ZMod 2) (End σ) c) with hs | hz
    · have ht : C = ⊤ := by
        apply top_unique
        intro v _
        obtain ⟨w,rfl⟩ := hs v
        apply (Submodule.Quotient.mk_eq_zero C).mp
        change C.mkQ (f w - c • w) = 0
        rw [map_sub,map_smul]
        have hh := LinearMap.congr_fun hc (C.mkQ w)
        change C.mkQ (f w) = c • C.mkQ w at hh
        rw [hh,sub_self]
      have hz : fixedCodim σ A = 0 := (fixedCodim_eq_zero_iff σ A).mpr ht
      omega
    · exact hz
  exact ⟨c,(sub_eq_zero.mp hzero).symm⟩

/-- Displacement three and nonabelian commuting action force three absolute copies. -/
theorem exists_three_absolute_copies
    (ρ : Representation (ZMod 2) (G × H) V) [IsIrreducible ρ]
    (hn : ∃ a b : H, ρ (1,a*b) ≠ ρ (1,b*a))
    (A : Subgroup G) (hd : fixedCodim (left ρ) A = 3) :
    ∃ S : Subrepresentation (left ρ), IsIrreducible S.toRepresentation ∧
      IsAbsolutelyIrreducible S.toRepresentation ∧
      fixedCodim S.toRepresentation A = 1 ∧
      ∃ e : V ≃ₗ[ZMod 2] (Fin 3 → S.toSubmodule),
        ∀ g v, e (ρ (g,1) v) = fun i => S.toRepresentation g (e v i) := by
  obtain ⟨S,hS,r,hr,e,he⟩ := exists_multiple_copy_coordinates ρ hn
  let := hS
  have hh := fixedCodim_map_equivariant (left ρ)
    (BinaryParabolicNatural.copies (Fin r) S.toRepresentation) (MonoidHom.id G) e he A
  simp only [Subgroup.map_id, BinaryParabolicNatural.fixedCodim_copies,
    Fintype.card_fin,hd] at hh
  have hc : fixedCodim S.toRepresentation A = 1 := by
    have hdvd : fixedCodim S.toRepresentation A ∣ 3 := ⟨r,by simpa only [mul_comm] using hh⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact h
    · rw [h] at hh
      omega
  have hr3 : r = 3 := by rw [hc,mul_one] at hh; exact hh.symm
  subst r
  exact ⟨S,hS,absolute_of_fixedCodim_one S.toRepresentation A hc,hc,e,he⟩

open scoped _root_.TensorProduct
open QuadraticFourGroup.TensorClassification

/-- Actual tensor coordinates with the original constituent and multiplicity actions. -/
structure SharpTensor (ρ : Representation (ZMod 2) (G × H) V) (A : Subgroup G) where
  constituent : Subrepresentation (left ρ)
  irreducible : IsIrreducible constituent.toRepresentation
  absolute : IsAbsolutelyIrreducible constituent.toRepresentation
  displacement : fixedCodim constituent.toRepresentation A = 1
  multiplicity : Representation (ZMod 2) H (Fin 3 → ZMod 2)
  coordinates : ρ.Equiv (externalTensor constituent.toRepresentation multiplicity)

/-- Construct the tensor and its three-dimensional multiplicity action. -/
theorem exists_sharpTensor
    (ρ : Representation (ZMod 2) (G × H) V) [IsIrreducible ρ]
    (hn : ∃ a b : H, ρ (1,a*b) ≠ ρ (1,b*a))
    (A : Subgroup G) (hd : fixedCodim (left ρ) A = 3) : Nonempty (SharpTensor ρ A) := by
  obtain ⟨S,hS,habs,hcod,e,he⟩ := exists_three_absolute_copies ρ hn A hd
  let := hS
  let := habs
  let : Nontrivial S.toSubmodule := Subrepresentation.irreducible_module_nontrivial S.toRepresentation
  let f : S.toRepresentation.IntertwiningMap (left ρ) :=
    .mk S.toSubmodule.subtype (by intro g; ext v; rfl)
  have hf : f ≠ 0 := by
    obtain ⟨v,hv⟩ := exists_ne (0 : S.toSubmodule)
    intro hz
    exact hv (Subtype.ext (congrArg (fun f : S.toRepresentation.IntertwiningMap (left ρ) => f v) hz))
  obtain ⟨n,μ,⟨a⟩⟩ := exists_externalTensor ρ S.toRepresentation f hf
  have hdim := a.toLinearEquiv.finrank_eq
  have hcopy := e.finrank_eq
  simp only [Module.finrank_tensorProduct,Module.finrank_pi,Fintype.card_fin] at hdim
  simp only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul] at hcopy
  have hpos : 0 < Module.finrank (ZMod 2) S.toSubmodule := Module.finrank_pos
  have hn3 : n = 3 := by nlinarith
  subst n
  exact ⟨⟨S,hS,habs,hcod,μ,a⟩⟩

omit [FiniteDimensional (ZMod 2) V] in
/-- Faithfulness of the original second factor passes to its multiplicity action. -/
theorem SharpTensor.multiplicity_faithful
    {ρ : Representation (ZMod 2) (G × H) V} {A : Subgroup G}
    (d : SharpTensor ρ A) (hf : Function.Injective (ρ.comp (MonoidHom.inr G H))) :
    Function.Injective d.multiplicity := by
  intro a b hab
  apply hf
  apply LinearMap.ext
  intro v
  apply d.coordinates.injective
  change d.coordinates (ρ (1,a) v) = d.coordinates (ρ (1,b) v)
  have hact (g : G × H) : d.coordinates (ρ g v) =
      externalTensor d.constituent.toRepresentation d.multiplicity g (d.coordinates v) :=
    LinearMap.congr_fun (d.coordinates.isIntertwining' g) v
  rw [hact,hact]
  change externalTensor d.constituent.toRepresentation d.multiplicity (1,a) (d.coordinates v) =
    externalTensor d.constituent.toRepresentation d.multiplicity (1,b) (d.coordinates v)
  rw [externalTensor_apply,externalTensor_apply,hab]

open scoped MatrixGroups

/-- A faithful nontrivial perfect action in binary degree three is the full linear action. -/
theorem perfect_three_natural {J : Type*} [Group J] [Finite J]
    [Group.IsPerfect J] [Nontrivial J]
    (σ : Representation (ZMod 2) J (Fin 3 → ZMod 2)) (hf : Function.Injective σ) :
    ∃ e : J ≃* SL(3,ZMod 2), ∀ j v, σ j v = (e j).val.mulVec v := by
  let a := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → ZMod 2)).trans
    (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  let φ : J →* SL(3,ZMod 2) := a.toMonoidHom.comp σ.asGroupHom
  have hφ : Function.Injective φ := by
    apply a.injective.comp
    intro x y h
    exact hf (congrArg Units.val h)
  have ht : φ.range = ⊤ := by
    by_contra hn
    let : Group.IsSolvable φ.range := Matrix.PSL3Two.isSolvable_subgroup_SL_of_ne_top _ hn
    let : Group.IsPerfect φ.range := Group.IsPerfect.range φ
    let : Nontrivial φ.range := Function.Injective.nontrivial
      (MonoidHom.ofInjective hφ).injective
    exact Group.IsPerfect.not_isSolvable φ.range inferInstance
  let e := MulEquiv.ofBijective φ ⟨hφ,MonoidHom.range_eq_top.mp ht⟩
  refine ⟨e,?_⟩
  intro j v
  have h := BinaryLinear.OuterCyclic.slEquivLinear_apply 3 (e j) v
  rw [show BinaryLinear.OuterCyclic.slEquivLinear 3 (e j) =
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → ZMod 2))
      (σ.asGroupHom j) by exact (BinaryLinear.OuterCyclic.slEquivLinear 3).apply_symm_apply _] at h
  simpa [Representation.asGroupHom_apply] using h

/-- The sharp tensor carries a natural SL₃(2) action of the original perfect factor. -/
theorem exists_natural_sharpTensor [Finite H] [Group.IsPerfect H] [Nontrivial H]
    (ρ : Representation (ZMod 2) (G × H) V) [IsIrreducible ρ]
    (hf : Function.Injective (ρ.comp (MonoidHom.inr G H)))
    (A : Subgroup G) (hd : fixedCodim (left ρ) A = 3) :
    ∃ d : SharpTensor ρ A, ∃ e : H ≃* SL(3,ZMod 2),
      ∀ h v, d.multiplicity h v = (e h).val.mulVec v := by
  have hn : ∃ a b : H, ρ (1,a*b) ≠ ρ (1,b*a) := by
    by_contra! hc
    have hm : IsMulCommutative H := ⟨⟨fun a b => hf (hc a b)⟩⟩
    exact Group.IsPerfect.not_isMulCommutative H hm
  obtain ⟨d⟩ := exists_sharpTensor ρ hn A hd
  obtain ⟨e,he⟩ := perfect_three_natural d.multiplicity (d.multiplicity_faithful hf)
  exact ⟨d,e,he⟩
omit [FiniteDimensional (ZMod 2) V] in
/-- The actual constituent retains exactly the first factor action kernel. -/
theorem SharpTensor.constituent_kernel
    {ρ : Representation (ZMod 2) (G × H) V} {A : Subgroup G}
    (d : SharpTensor ρ A) : d.constituent.toRepresentation.ker = (left ρ).ker := by
  ext g
  constructor
  · intro hg
    apply LinearMap.ext
    intro v
    apply d.coordinates.injective
    have hact : d.coordinates (ρ (g,1) v) =
        externalTensor d.constituent.toRepresentation d.multiplicity (g,1) (d.coordinates v) :=
      LinearMap.congr_fun (d.coordinates.isIntertwining' (g,1)) v
    change d.coordinates (ρ (g,1) v) = d.coordinates v
    rw [hact]
    change d.constituent.toRepresentation g = 1 at hg
    rw [externalTensor_apply,hg,map_one]
    exact LinearMap.congr_fun (_root_.TensorProduct.map_id :
      _root_.TensorProduct.map (LinearMap.id : d.constituent.toSubmodule →ₗ[ZMod 2] _) (LinearMap.id : (Fin 3 → ZMod 2) →ₗ[ZMod 2] _) = LinearMap.id) _
  · intro hg
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun hg v
end Representation.ProductIsotypic
