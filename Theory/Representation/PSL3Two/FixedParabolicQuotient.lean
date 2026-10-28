module
public import Theory.Representation.PSL3Two.FanoLineMoved
public import Theory.Representation.PSL3Two.SmallModuleProperties
public import Theory.Representation.CosetOrbitQuotient
public import Theory.Representation.BinaryConjugacyOrbit
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import Theory.Representation.PSL3Two.FanoLocalStructure.ParabolicSpaces
public import Theory.GroupAction.SurjectiveFlagCosets

/-!
# Fano quotients of vectors fixed by an actual parabolic

A cyclic binary module whose generator is fixed by an index-seven
parabolic in a two-core cover of PSL₃(2) is a quotient of the actual
Fano-line permutation module. A single marking identifies both the
parabolic and its specified Sylow subgroup. The line-core
classification identifies the moved action with the dual natural module
or the Fano core, gives full dimensions three, four, six or seven and an
equivariant quotient onto the dual natural module. The two surjections
identify the action kernel with the literal two-core.

The proof constructs the coset map before applying the native Fano
calculation. The marking may use graph duality; no preferred orientation
relative to a previously chosen natural constituent is asserted.
Source: Aschbacher–Smith H.5.3, printed pp.385–386, and its application
in 13.4.7, printed p.901. The original-pair application is in
FixedCoreSource/Amalgam/LinearFixedLine.
-/

public noncomputable section
open Subgroup Representation
namespace BinaryLinearThree.FixedParabolicQuotient
open FanoDecomposition FanoLineQuotients
variable {A M : Type*} [_root_.Group A] [Finite A] [AddCommGroup M] [Module (ZMod 2) M]

local instance lineAction : MulAction Group Line := MulAction.compHom Line linePerm
local instance lineTransitive : MulAction.IsPretransitive Group Line where
  exists_smul_eq x y := by
    obtain ⟨a,ha⟩ := FanoLocalStructure.line_reachable x
    obtain ⟨b,hb⟩ := FanoLocalStructure.line_reachable y
    refine ⟨b * a⁻¹, ?_⟩
    change linePerm (b * a⁻¹) x = y
    rw [map_mul, Equiv.Perm.mul_apply, ←ha, map_inv, Equiv.Perm.inv_def,
      Equiv.symm_apply_apply, hb]

omit [Finite A] in
/-- A marked parabolic-fixed spanning vector gives the literal Fano quotient. -/
theorem marked_quotient (f : A →* Group) (hf : Function.Surjective f)
    (P : Subgroup A) (hk : f.ker ≤ P) (hP : P.map f = Matrix.PSL3Two.lineParabolicSL)
    (ρ : Representation (ZMod 2) A M) (w : M) (hw : ∀ a : P, ρ a w = w)
    (hs : Submodule.span (ZMod 2) (Set.range (fun a : A => ρ a w)) = ⊤) :
    ∃ q : Representation.IntertwiningMap (lineRepresentation.comp f) ρ, Function.Surjective q := by
  classical
  have hfix : P.map f = MulAction.stabilizer Group Matrix.PSL3Two.flagLine := by
    rw [hP]
    ext g
    exact FanoLocalStructure.ParabolicSpaces.mem_lineParabolic_iff_fixes_line g
  let E := MulAction.surjectiveCosetEquiv P f hf hk Matrix.PSL3Two.flagLine hfix
  obtain ⟨q,hq,hm,he⟩ := exists_coset_orbit_map ρ P w hw hs
  let v : Line → M := fun l => q (Finsupp.single (E.symm l) 1)
  have hv (a : A) (l : Line) : v (linePerm (f a) l) = ρ a (v l) := by
    have hE : E.symm (linePerm (f a) l) = a • E.symm l := by
      apply E.injective
      rw [E.apply_symm_apply]
      exact (MulAction.surjectiveCosetEquiv_smul P f hf hk _ hfix a (E.symm l)).trans
        (congrArg (fun l : Line => f a • l) (E.apply_symm_apply l)) |>.symm
    change q (Finsupp.single (E.symm (linePerm (f a) l)) 1) = _
    rw [hE]
    simpa only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single] using
      he a (Finsupp.single (E.symm l) 1)
  have hvspan : Submodule.span (ZMod 2) (Set.range v) = ⊤ := by
    apply top_unique
    rw [←hs]
    apply Submodule.span_mono
    rintro _ ⟨a,rfl⟩
    exact ⟨E (QuotientGroup.mk a),by
      change q (Finsupp.single (E.symm (E (QuotientGroup.mk a))) 1) = ρ a w
      rw [E.symm_apply_apply,hm]⟩
  exact ⟨BinaryPermutation.orbitQuotient ρ (linePerm.comp f) v hv,
    BinaryPermutation.orbitQuotient_surjective ρ (linePerm.comp f) v hv hvspan⟩

/-- Mark the actual parabolic and common Sylow under one quotient isomorphism. -/
theorem exists_marking (e₀ : (A ⧸ pCore 2 A) ≃* Matrix.PSL3Two.PSL)
    (S : Sylow 2 A) (P : Subgroup A) (hSP : (S : Subgroup A) ≤ P)
    (hindex : P.index = 7) :
    ∃ e : (A ⧸ pCore 2 A) ≃* Group,
      let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
      P.map f = Matrix.PSL3Two.lineParabolicSL ∧
      (S : Subgroup A).map f = Matrix.PSL3Two.borelSL := by
  let q := QuotientGroup.mk' (pCore 2 A)
  have hq := QuotientGroup.mk'_surjective (pCore 2 A)
  let S' := S.mapSurjective hq
  let P' := P.map q
  have hk : q.ker ≤ P := by
    rw [QuotientGroup.ker_mk']
    exact (pCore_isPGroup.le_sylow_of_normal S).trans hSP
  have hi : P'.index = 7 := (P.index_map_eq hq hk).trans hindex
  have hc : Nat.card P' = 24 := by
    have hh := P'.index_mul_card
    rw [hi,Nat.card_congr e₀.toEquiv,Matrix.PSL3Two.card_PSL] at hh
    omega
  have hn : P' ≠ ⊤ := by intro he; rw [he,index_top] at hi; omega
  have ht : ¬ IsPGroup 2 P' := by
    intro hp
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hc] at hn
    have hd : 3 ∣ 2 ^ n := hn ▸ (by decide : 3 ∣ 24)
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  obtain ⟨e,hS,hP⟩ := Matrix.PSL3Two.exists_sylow_line_marking e₀ S' P'
    (map_mono hSP) hn ht
  exact ⟨e,by simpa only [←map_map] using hP,by simpa only [S', Sylow.coe_mapSurjective, ←map_map] using hS⟩

omit [Finite A] in
/-- The permutation quotient and its faithful dual-natural quotient have
exactly the kernel of the original model homomorphism. -/
theorem kernel_eq_of_fano_quotients (f : A →* Group)
    (ρ : Representation (ZMod 2) A M)
    (q : Representation.IntertwiningMap (lineRepresentation.comp f) ρ)
    (hq : Function.Surjective q)
    (r : ρ.IntertwiningMap (W.dual.comp f)) (hr : Function.Surjective r) :
    ρ.ker = f.ker := by
  ext a
  change ρ a = 1 ↔ f a = 1
  constructor
  · intro ha
    apply dual_injective
    rw [map_one]
    apply LinearMap.ext
    intro φ
    obtain ⟨v,rfl⟩ := hr φ
    change (W.dual.comp f) a (r v) = r v
    rw [← r.isIntertwining]
    rw [ha]
    rfl
  · intro ha
    apply LinearMap.ext
    intro v
    obtain ⟨x,rfl⟩ := hq v
    rw [←q.isIntertwining]
    change q (lineRepresentation (f a) x) = q x
    rw [ha,map_one]
    rfl

/-- Exact quotient dimensions, moved-module alternatives, the original
kernel, and the two actual intertwiners, retaining the same parabolic and Sylow marking. -/

theorem quotient_and_head (e₀ : (A ⧸ pCore 2 A) ≃* Matrix.PSL3Two.PSL)
    (S : Sylow 2 A) (P : Subgroup A) (hSP : (S : Subgroup A) ≤ P)
    (hindex : P.index = 7) (ρ : Representation (ZMod 2) A M)
    (w : M) (hw : ∀ a : P, ρ a w = w)
    (hs : Submodule.span (ZMod 2) (Set.range (fun a : A => ρ a w)) = ⊤)
    [FiniteDimensional (ZMod 2) M] (hd : 1 < Module.finrank (ZMod 2) M) :
    (Module.finrank (ZMod 2) M = 3 ∨ Module.finrank (ZMod 2) M = 4 ∨
      Module.finrank (ZMod 2) M = 6 ∨ Module.finrank (ZMod 2) M = 7) ∧
    ρ.ker = pCore 2 A ∧
    ∃ e : (A ⧸ pCore 2 A) ≃* Group,
      let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
      P.map f = Matrix.PSL3Two.lineParabolicSL ∧
      (S : Subgroup A).map f = Matrix.PSL3Two.borelSL ∧
      (∃ q : Representation.IntertwiningMap (lineRepresentation.comp f) ρ,
        Function.Surjective q ∧
        (FanoLineMoved.coreMap f ρ q).range.toSubmodule =
          Representation.BinaryOffender.subspaceCommutator ρ ⊤ ⊤ ∧
        (Nonempty (Representation.Equiv (W.dual.comp f)
            (FanoLineMoved.coreMap f ρ q).range.toRepresentation) ∨
          Nonempty (Representation.Equiv (lineCoreRepresentation.comp f)
            (FanoLineMoved.coreMap f ρ q).range.toRepresentation))) ∧
      (∃ r : ρ.IntertwiningMap (W.dual.comp f), Function.Surjective r) := by
  obtain ⟨e,hP,hS⟩ := exists_marking e₀ S P hSP hindex
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker ≤ P := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact (pCore_isPGroup.le_sylow_of_normal S).trans hSP
  obtain ⟨q,hq⟩ := marked_quotient f hf P hk hP ρ w hw hs
  obtain ⟨r,hr⟩ := dual_quotient f hf ρ q hq hd
  have hker : ρ.ker = pCore 2 A := by
    rw [kernel_eq_of_fano_quotients f ρ q hq r hr,
      MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  exact ⟨quotient_dimensions f hf ρ q hq hd,hker,e,hP,hS,
    ⟨q,hq,FanoLineMoved.core_image_eq_moved f hf ρ q hq,
      FanoLineMoved.core_image_models f hf ρ q hq hd⟩,r,hr⟩
end BinaryLinearThree.FixedParabolicQuotient
