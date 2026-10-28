module
public import Theory.Representation.BinaryPermutation.SixCoreResidualLine

/-!
# The radical of an augmentation point stabilizer modulo constants

For a nonconstant vector in the binary six-letter augmentation core, let R
be the cubic residual of its A₆ stabilizer. The literal O₂(R) acts faithfully
on the residual three-space modulo the constant line. Its fixed vectors
modulo that line in the full augmentation core form a space of order at most
four. Two explicit Klein-four actors prove the marked calculation; actual
even permutations and complementation transport it to every nonfixed vector.

These are the module calculations bounding the center of the point radical
in an augmentation A₆ block. The application to the original common residual
is in Chapter13/Section04/FixedCoreSource/Nonsolvable/ReciprocalSixCenter.
Source: Aschbacher–Smith 13.4.15, final paragraph, printed p.912,
refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement
namespace BinaryPermutation.SixCoreResidualCenter
open SixCoreResidualMovement SixCoreResidualLine
open Theory.SpecificGroups.SymmetricSix
local instance : DecidablePred (· ∈ core (Fin 6)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype W := Subtype.fintype _
local instance : Fintype (Equiv.Perm (Fin 4)) := fintypePerm

@[expose] def constantLine : Submodule (ZMod 2) W :=
  Submodule.span (ZMod 2) ({sixCoreConstant} : Set W)

theorem mem_constantLine (v : W) : v ∈ constantLine ↔ v = 0 ∨ v = sixCoreConstant := by
  constructor
  · intro hv
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hv
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact Submodule.zero_mem _
    · exact Submodule.subset_span rfl

theorem constantLine_action (g : A) {v : W} (hv : v ∈ constantLine) :
    rho g v ∈ constantLine := by
  rw [mem_constantLine] at hv ⊢
  rcases hv with rfl | rfl
  · exact Or.inl (map_zero _)
  · exact Or.inr (sixCoreConstant_fixed g)

@[expose] def fixedModuloLine (R : Subgroup A) : Submodule (ZMod 2) W :=
  ⨅ a : R, constantLine.comap (rho a.val - LinearMap.id)

theorem mem_fixedModuloLine (R : Subgroup A) (v : W) :
    v ∈ fixedModuloLine R ↔ ∀ a ∈ R, rho a v - v ∈ constantLine := by
  simp only [fixedModuloLine,Submodule.mem_iInf,Submodule.mem_comap,
    LinearMap.sub_apply,LinearMap.id_apply,Subtype.forall]

private def pair : W := ⟨![1,1,0,0,0,0],by rw [mem_core];decide⟩
private theorem pair_stabilizer : S pair = a6DuadStabilizer := by
  ext g
  change rho g pair = pair ↔ g.val ∈ duadStabilizer
  revert g
  decide +kernel
private noncomputable def e : Equiv.Perm (Fin 4) ≃* S pair :=
  a6DuadModelEquiv.trans (MulEquiv.subgroupCongr pair_stabilizer.symm)
private def a0 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2
private def b0 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 3
private def c0 : Equiv.Perm (Fin 4) := ⁅a0,Equiv.swap 0 1 * Equiv.swap 2 3⁆
private def d0 : Equiv.Perm (Fin 4) := ⁅b0,Equiv.swap 0 1 * Equiv.swap 2 3⁆

private theorem comm_core (a c : Equiv.Perm (Fin 4)) (ha : a^3=1)
    (hc : c.sign=1 ∧ c^2=1) : (e ⁅a,c⁆).val ∈ (residual pair).pCoreIn 2 := by
  have har : e a ∈ primeToResidual 3 (S pair) :=
    mem_primeToResidual_of_pow (n := 1) (by simp only [pow_one,←map_pow,ha,map_one])
  have hcc : e c ∈ pCore 2 (S pair) := by
    rw [←pCore_map_iso 2 e]
    apply mem_map_of_mem
    rwa [←DuadCalculation.core_eq,DuadCalculation.core_mem_iff]
  have hbr : ⁅e a,e c⁆ ∈ primeToResidual 3 (S pair) :=
    commutator_le_left _ _ (commutator_mem_commutator har (mem_top _))
  have hbc : ⁅e a,e c⁆ ∈ pCore 2 (S pair) :=
    commutator_le_right _ _ (commutator_mem_commutator (mem_top _) hcc)
  have hh : ⁅e a,e c⁆ ∈ (primeToResidual 3 (S pair)).pCoreIn 2 := by
    refine ⟨⟨_,hbr⟩,?_,rfl⟩
    rwa [pCore_eq_comap_of_normal]
  rw [SixCoreResidualLine.residual,←map_pCoreIn_of_injective 2 _ _ (S pair).subtype_injective]
  rw [map_commutatorElement]
  exact mem_map_of_mem (S pair).subtype hh

private theorem c_mem : (e c0).val ∈ (residual pair).pCoreIn 2 :=
  comm_core a0 _ (by decide) (by decide)
private theorem d_mem : (e d0).val ∈ (residual pair).pCoreIn 2 :=
  comm_core b0 _ (by decide) (by decide)

private def pairFixed (v : W) : Prop :=
  (rho (e c0).val v-v=0 ∨ rho (e c0).val v-v=sixCoreConstant) ∧
  (rho (e d0).val v-v=0 ∨ rho (e d0).val v-v=sixCoreConstant)
private instance (v : W) : Decidable (pairFixed v) := inferInstanceAs (Decidable (_ ∧ _))
private theorem pairFixed_card : Nat.card {v : W // pairFixed v} = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
private theorem pair_fixed_bound : Nat.card (fixedModuloLine ((residual pair).pCoreIn 2)) ≤ 4 := by
  let f : fixedModuloLine ((residual pair).pCoreIn 2) → {v : W // pairFixed v} :=
    fun v => ⟨v.val,⟨(mem_constantLine _).mp ((mem_fixedModuloLine _ _).mp v.property _ c_mem),
      (mem_constantLine _).mp ((mem_fixedModuloLine _ _).mp v.property _ d_mem)⟩⟩
  exact (Nat.card_le_card_of_injective f (fun _ _ he => Subtype.ext (show _ from congrArg (fun x : {v : W // pairFixed v} => x.val) he))).trans_eq pairFixed_card

private def t : W := ⟨![1,0,1,0,0,0],by rw [mem_core];decide⟩
private theorem displacement_mem (a : Equiv.Perm (Fin 4)) (ha : a^3=1) :
    rho (e a).val t-t ∈ moved pair := by
  have har : e a ∈ primeToResidual 3 (S pair) :=
    mem_primeToResidual_of_pow (n := 1) (by simp only [pow_one,←map_pow,ha,map_one])
  exact Submodule.subset_span ⟨(e a).val,mem_map_of_mem (S pair).subtype har,t,Submodule.mem_top,rfl⟩
private def faithfulTest (a : Equiv.Perm (Fin 4)) : Prop :=
    a.sign=1 ∧ a^2=1 →
    (rho (e a).val (rho (e a0).val t-t)-(rho (e a0).val t-t)=0 ∨
      rho (e a).val (rho (e a0).val t-t)-(rho (e a0).val t-t)=sixCoreConstant) →
    (rho (e a).val (rho (e (a0*a0)).val t-t)-(rho (e (a0*a0)).val t-t)=0 ∨
      rho (e a).val (rho (e (a0*a0)).val t-t)-(rho (e (a0*a0)).val t-t)=sixCoreConstant) → a=1
private instance (a : Equiv.Perm (Fin 4)) : Decidable (faithfulTest a) :=
  inferInstanceAs (Decidable (_ → _ → _ → _))
private theorem pair_faithful_certificate : ∀ a : Equiv.Perm (Fin 4), faithfulTest a := by
  decide +kernel

private theorem pair_faithful (a : A) (ha : a ∈ (residual pair).pCoreIn 2)
    (hh : ∀ v ∈ moved pair, rho a v-v ∈ constantLine) : a=1 := by
  rw [SixCoreResidualLine.residual,←map_pCoreIn_of_injective 2 _ _ (S pair).subtype_injective] at ha
  obtain ⟨b,hb,rfl⟩ := ha
  obtain ⟨c,hc,he⟩ := hb
  have hbc : b ∈ pCore 2 (S pair) := he ▸ (by rwa [pCore_eq_comap_of_normal] at hc)
  have hk : e.symm b ∈ pCore 2 (Equiv.Perm (Fin 4)) := by
    rw [←pCore_map_iso 2 e.symm]
    exact mem_map_of_mem _ hbc
  rw [←DuadCalculation.core_eq,DuadCalculation.core_mem_iff] at hk
  have h₁ := (mem_constantLine _).mp (hh _ (displacement_mem a0 (by decide)))
  have h₂ := (mem_constantLine _).mp (hh _ (displacement_mem (a0*a0) (by decide)))
  have hb1 : e.symm b=1 := pair_faithful_certificate _ hk (by simpa using h₁) (by simpa using h₂)
  exact congrArg Subtype.val (e.symm.injective (hb1.trans e.symm.map_one.symm))


private local instance : MulAction A W where
  smul g w := rho g w
  one_smul w := by change rho 1 w = w; rw [map_one]; rfl
  mul_smul g h w := by change rho (g*h) w = rho g (rho h w); rw [map_mul]; rfl

private theorem residual_conjugate (g : A) (w : W) :
    (residual w).map (MulAut.conj g).toMonoidHom = residual (rho g w) := by
  rw [SixCoreResidualLine.residual,map_embedded_primeToResidual_of_hom]
  have hs : (S w).map (MulAut.conj g).toMonoidHom = S (rho g w) :=
    (MulAction.stabilizer_smul_eq_stabilizer_map_conj g w).symm
  exact congrArg (fun P : Subgroup A => (primeToResidual 3 P).map P.subtype) hs
private theorem core_conjugate (g : A) (w : W) :
    ((residual w).pCoreIn 2).map (MulAut.conj g).toMonoidHom =
      (residual (rho g w)).pCoreIn 2 := by
  rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,residual_conjugate]
private theorem moved_conjugate (g : A) (w : W) :
    (moved w).map (rho g) = moved (rho g w) := by
  rw [moved,subspaceCommutator_map_conj,Submodule.map_top,
    LinearMap.range_eq_top.mpr (rho.apply_bijective g).surjective,residual_conjugate]
  rfl
private theorem residual_complement (w : W) : residual (w+sixCoreConstant)=residual w := by
  have hs : S (w+sixCoreConstant)=S w := by
    ext x
    change rho x (w+sixCoreConstant)=w+sixCoreConstant ↔ rho x w=w
    rw [map_add,sixCoreConstant_fixed,add_left_inj]
  exact congrArg (fun P : Subgroup A => (primeToResidual 3 P).map P.subtype) hs
private theorem conjugate_action (g a : A) (v : W) :
    rho (MulAut.conj g a) (rho g v)=rho g (rho a v) := by
  change rho (g*a*g⁻¹) (rho g v)=_
  rw [←Module.End.mul_apply,←map_mul]
  simp only [mul_assoc,inv_mul_cancel,mul_one,map_mul,Module.End.mul_apply]
private theorem inverse_action (g : A) (v : W) : rho g⁻¹ (rho g v)=v := by
  rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one]
  rfl

/-- Centrality modulo the constant line on the residual three-space
faithfully detects every element of the literal point radical. -/
theorem radical_faithful_mod_constants (w : W) (hw : ¬ ∀ a : A, rho a w=w)
    (a : A) (ha : a ∈ (residual w).pCoreIn 2)
    (hh : ∀ v ∈ moved w, rho a v-v ∈ constantLine) : a=1 := by
  have hnf := not_or.mp ((not_congr (sixCore_fixed_iff w)).mp hw)
  have step (w₀ : W) (hr : residual w₀=residual pair) (g : A) (hg : rho g w₀=w) : a=1 := by
    have hc := core_conjugate g w₀
    rw [hr,hg] at hc
    obtain ⟨b,hb,hba⟩ := hc.ge ha
    change MulAut.conj g b=a at hba
    have hm := moved_conjugate g w₀
    have hm₀ : moved w₀=moved pair := congrArg (fun R => subspaceCommutator rho ⊤ R) hr
    rw [hm₀,hg] at hm
    have hb1 : b=1 := pair_faithful b hb (by
      intro v hv
      have hh' := hh (rho g v) (hm.le (Submodule.mem_map_of_mem hv))
      rw [←hba,conjugate_action,←map_sub] at hh'
      simpa only [inverse_action] using constantLine_action g⁻¹ hh')
    rw [hb1,map_one] at hba
    exact hba.symm
  rcases sixCore_paired_orbits pair w (by decide) (by decide) hnf.1 hnf.2 with ⟨g,hg⟩ | ⟨g,hg⟩
  · exact step pair rfl g hg
  · exact step (pair+sixCoreConstant) (residual_complement pair) g hg

/-- The full augmentation space fixed modulo constants by the literal
point radical has at most four vectors. -/
theorem radical_fixed_mod_constants_card (w : W) (hw : ¬ ∀ a : A, rho a w=w) :
    Nat.card (fixedModuloLine ((residual w).pCoreIn 2)) ≤ 4 := by
  have hnf := not_or.mp ((not_congr (sixCore_fixed_iff w)).mp hw)
  have step (w₀ : W) (hr : residual w₀=residual pair) (g : A) (hg : rho g w₀=w) :
      Nat.card (fixedModuloLine ((residual w).pCoreIn 2)) ≤ 4 := by
    have hc := core_conjugate g w₀
    rw [hr,hg] at hc
    let f : fixedModuloLine ((residual w).pCoreIn 2) → fixedModuloLine ((residual pair).pCoreIn 2) :=
      fun v => ⟨rho g⁻¹ v.val,by
        apply (mem_fixedModuloLine _ _).mpr
        intro b hb
        have hmem : MulAut.conj g b ∈ (residual w).pCoreIn 2 :=
          hc.le (mem_map_of_mem _ hb)
        have hd := (mem_fixedModuloLine _ _).mp v.property _ hmem
        have hv : rho g (rho g⁻¹ v.val)=v.val := by simpa only [inv_inv] using inverse_action g⁻¹ v.val
        rw [←hv,conjugate_action,←map_sub] at hd
        simpa only [inverse_action] using constantLine_action g⁻¹ hd⟩
    exact (Nat.card_le_card_of_injective f (by
      intro v u h
      apply Subtype.ext
      exact (rho.apply_bijective g⁻¹).injective (congrArg Subtype.val h))).trans pair_fixed_bound
  rcases sixCore_paired_orbits pair w (by decide) (by decide) hnf.1 hnf.2 with ⟨g,hg⟩ | ⟨g,hg⟩
  · exact step pair rfl g hg
  · exact step (pair+sixCoreConstant) (residual_complement pair) g hg
end BinaryPermutation.SixCoreResidualCenter
