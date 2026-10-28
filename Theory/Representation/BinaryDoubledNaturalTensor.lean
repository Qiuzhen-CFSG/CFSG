module
public import Theory.Representation.BinaryDoubledNaturalCentralizer

/-!
# The binary tensor subgroup with its literal action

On two identical natural binary modules, the natural special linear factor
commutes with the two-dimensional multiplicity factor. Their intersection is
trivial because the binary special linear group has trivial center. The
resulting tensor homomorphism identifies their join with the actual product,
and retains its action equation on every vector. This does not identify the
full ambient normalizer, which can also exchange the factors in degree two.

The source consumer is the dimension-three normalizer in Aschbacher--Smith,
original 12.2.25, printed p.806. Its canonical fixed actor supplies the first
factor, and the original cyclic pair supplies the multiplicity factor.
-/

@[expose] public noncomputable section
namespace Representation.BinaryDoubledNatural
open Matrix Subgroup
variable (n : ℕ) [NeZero n]

def multiplicityRepresentation : Representation (ZMod 2) MultiplicitySL (Space n) :=
  (multiplicityHom n).toMonoidHom.comp SpecialLinearGroup.coeMonoidHom

def tensorRepresentation : Representation (ZMod 2) (SL n × MultiplicitySL) (Space n) where
  toFun g := representation n g.1 * multiplicityRepresentation n g.2
  map_one' := by simp [multiplicityRepresentation]
  map_mul' g h := by
    simp only [Prod.fst_mul,Prod.snd_mul,map_mul]
    have hc := multiplicity_commutes n g.2.val h.1
    change multiplicityRepresentation n g.2 * representation n h.1 =
      representation n h.1 * multiplicityRepresentation n g.2 at hc
    calc
      _ = representation n g.1 * (representation n h.1 * multiplicityRepresentation n g.2) *
          multiplicityRepresentation n h.2 := by simp only [mul_assoc]
      _ = _ := by rw [←hc]; simp only [mul_assoc]

omit [NeZero n] in
theorem multiplicity_mem_centralizer (c : MultiplicitySL) :
    (multiplicityRepresentation n).asGroupHom c ∈ centralizer (component n : Set (Ambient n)) := by
  rw [mem_centralizer_iff]
  rintro a ⟨g,rfl⟩
  exact Units.ext (multiplicity_commutes n c.val g).symm

theorem tensor_injective : Function.Injective (tensorRepresentation n).asGroupHom := by
  apply (injective_iff_map_eq_one _).mpr
  rintro ⟨g,c⟩ h
  have ht : (tensorRepresentation n).asGroupHom (g,c) =
      (representation n).asGroupHom g * (multiplicityRepresentation n).asGroupHom c := Units.ext rfl
  have he : (representation n).asGroupHom g =
      ((multiplicityRepresentation n).asGroupHom c)⁻¹ := eq_inv_of_mul_eq_one_left (ht.symm.trans h)
  have hc : (representation n).asGroupHom g ∈ centralizer (component n : Set (Ambient n)) := by
    rw [he]
    exact (centralizer _).inv_mem (multiplicity_mem_centralizer n c)
  have hg : g ∈ center (SL n) := by
    rw [mem_center_iff]
    intro a
    apply representation_injective
    have hh := mem_centralizer_iff.mp hc ((representation n).asGroupHom a) ⟨a,rfl⟩
    exact congrArg Units.val (by simpa only [←map_mul] using hh)
  rw [BinaryLinear.OuterCyclic.binary_center_eq_bot (NeZero.pos n)] at hg
  have hg1 : g = 1 := mem_bot.mp hg
  have hc1 : c = 1 := by
    apply Subtype.ext
    apply multiplicity_injective n
    have hh := congrArg Units.val h
    change representation n g * multiplicity n c.val = 1 at hh
    rw [hg1,map_one,one_mul,←multiplicity_one] at hh
    exact hh
  exact Prod.ext hg1 hc1

def tensorSubgroup : Subgroup (Ambient n) := (tensorRepresentation n).asGroupHom.range

theorem tensorSubgroup_eq_sup (hn : 2 ≤ n) : tensorSubgroup n =
    component n ⊔ centralizer (component n : Set (Ambient n)) := by
  apply le_antisymm
  · rintro a ⟨⟨g,c⟩,rfl⟩
    have he : (tensorRepresentation n).asGroupHom (g,c) =
        (representation n).asGroupHom g * (multiplicityRepresentation n).asGroupHom c := Units.ext rfl
    rw [he]
    exact mul_mem_sup ⟨g,rfl⟩ (multiplicity_mem_centralizer n c)
  · apply sup_le
    · rintro a ⟨g,rfl⟩
      refine ⟨(g,1),Units.ext ?_⟩
      change representation n g * multiplicity n 1 = representation n g
      rw [multiplicity_one,mul_one]
    · intro b hb
      obtain ⟨c,hc⟩ := centralizer_units hn b hb
      obtain ⟨c,hcg⟩ := BinaryLinear.OuterCyclic.binary_toGL_surjective 2 c
      have hcv : c.val = _ := congrArg (fun x : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) => x.val) hcg
      refine ⟨(1,c),Units.ext ?_⟩
      change representation n 1 * multiplicity n c.val = (b : Module.End (ZMod 2) (Space n))
      rw [map_one,one_mul,hcv]
      exact hc.symm

def tensorEquiv : tensorSubgroup n ≃* (SL n × MultiplicitySL) :=
  (MonoidHom.ofInjective (tensor_injective n)).symm

theorem tensorEquiv_action (b : tensorSubgroup n) (v : Space n) :
    (b.val : Module.End (ZMod 2) (Space n)) v = tensorRepresentation n (tensorEquiv n b) v := by
  have hh := (MonoidHom.ofInjective (tensor_injective n)).apply_symm_apply b
  exact (LinearMap.congr_fun (congrArg (fun x : tensorSubgroup n =>
    (x.val : Module.End (ZMod 2) (Space n))) hh) v).symm
end Representation.BinaryDoubledNatural
