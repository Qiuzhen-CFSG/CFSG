module

public import Theory.Representation.PSL3Two.SteinbergStructure.LineRadicalCommutator
public import Theory.Representation.PSL3Two.SteinbergStructure.PointRadicalFixedSpace
public import Theory.Representation.PSL3Two.NaturalPlaneStabilizer.Core

/-!
# Incident natural planes and Steinberg commutators

A nonzero plane invariant under a point radical contains its unique natural
fixed point. The radical-fixed Steinberg endomorphisms have image in that
point, hence in the plane. An adapted basis sends the plane to the coordinate
plane; the two lower off-diagonal entries then vanish, placing every such
endomorphism in the line-radical commutator. All conjugations use the actual
natural and Steinberg representations.

Source: Aschbacher–Smith, J.4.3(2), printed p.441, using J.2.3(8).
-/

public section
open Subgroup Representation Representation.BinaryOffender Matrix
open scoped Pointwise
namespace BinaryLinearThree.SteinbergStructure.LineRadicalCommutator
open Matrix.PSL3Two BinaryLinearThree.IrreducibleCatalogue
noncomputable section
private def upper01 : Group := ⟨!![1,1,0;0,1,0;0,0,1],by decide⟩
private def upper02 : Group := ⟨!![1,0,1;0,1,0;0,0,1],by decide⟩
private theorem natural_fixed_point (v : Vector) (hv : v ≠ 0)
    (h : v ∈ fixedSpace W MarkedAutomorphisms.pointV) : v = ![1,0,0] := by
  have h1 := h ⟨upper01,by decide⟩
  have h2 := h ⟨upper02,by decide⟩
  have hc : ∀ v : Vector, v ≠ 0 → W upper01 v=v → W upper02 v=v → v=![1,0,0] := by
    decide +kernel
  exact hc v hv h1 h2

private theorem point_mem_invariant (A : Submodule (ZMod 2) Vector)
    (hc : Nat.card A = 4) (hs : MarkedAutomorphisms.pointV ≤ subspaceStabilizer W A) :
    ![1,0,0] ∈ A := by
  let B : Subrepresentation (W.comp MarkedAutomorphisms.pointV.subtype) := {
    toSubmodule := A
    apply_mem_toSubmodule := fun a v hv => (hs a.property v).2 hv }
  have hb : Nat.card B = 4 := hc
  let : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by rw [hb];decide)
  obtain ⟨v,hvn,hv⟩ := binary_pGroup_fixed_vector B.toRepresentation
    (IsPGroup.of_card (p := 2) (n := 2) MarkedAutomorphisms.card_pointV)
  have he : (v : Vector) = ![1,0,0] := natural_fixed_point v
    (fun h => hvn (Subtype.ext h)) (fun a => congrArg Subtype.val (hv a))
  exact he ▸ v.property

private theorem conjugate_equivariant {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) Group M) (g a : Group) (v : M) :
    ρ a (ρ g⁻¹ v) = ρ g⁻¹ (ρ ((MulAut.conj g) a) v) := by
  simp only [MulAut.conj_apply,map_mul,Module.End.mul_apply,Representation.inv_self_apply]

private theorem conjugate_point_mem (g : Group) (A : Submodule (ZMod 2) Vector)
    (hc : Nat.card A = 4)
    (hs : MarkedAutomorphisms.pointV.map (MulAut.conj g).toMonoidHom ≤
      subspaceStabilizer W A) : W g ![1,0,0] ∈ A := by
  let B := A.map (W g⁻¹)
  have hb : Nat.card B = 4 :=
    (Nat.card_congr (Submodule.equivMapOfInjective (W g⁻¹)
      (W.apply_bijective g⁻¹).injective A).toEquiv).symm.trans hc
  have hsB : MarkedAutomorphisms.pointV ≤ subspaceStabilizer W B :=
    map_subspace_invariant W W (MulAut.conj g).toMonoidHom (W g⁻¹)
      (conjugate_equivariant W g) _ A hs
  have hp := point_mem_invariant B hb hsB
  obtain ⟨a,ha,he⟩ := hp
  have h := congrArg (W g) he
  rw [Representation.self_inv_apply] at h
  exact h ▸ ha

private theorem S_apply_val (g : Group) (v : Steinberg) (x : Vector) :
    (S g v).val x = W g (v.val (W g⁻¹ x)) := by rfl

private theorem coordinates_bottom (v : Steinberg) :
    coordinates v 4 = (v.val (Pi.single 0 1)) 2 ∧
      coordinates v 5 = (v.val (Pi.single 1 1)) 2 := by
  exact ⟨rfl,rfl⟩

/-- A fixed endomorphism of a point radical has image in every invariant natural plane. -/
theorem fixed_image_in_plane (g : Group) (A : Submodule (ZMod 2) Vector)
    (hc : Nat.card A = 4)
    (hs : MarkedAutomorphisms.pointV.map (MulAut.conj g).toMonoidHom ≤
      subspaceStabilizer W A)
    (v : Steinberg)
    (hv : v ∈ fixedSpace S (MarkedAutomorphisms.pointV.map (MulAut.conj g).toMonoidHom))
    (x : Vector) : v.val x ∈ A := by
  have hf : S g⁻¹ v ∈ fixedSpace S MarkedAutomorphisms.pointV :=
    (embedding_mem_fixedSpace_iff S S (MulAut.conj g).toMonoidHom (S g⁻¹)
      (S.apply_bijective g⁻¹).injective (conjugate_equivariant S g) _ v).mpr hv
  have hr := PointRadicalFixedSpace.fixed_image (S g⁻¹ v) hf (W g⁻¹ x)
  rw [S_apply_val,inv_inv,Representation.self_inv_apply] at hr
  have heq : W g⁻¹ (v.val x) = (W g⁻¹ (v.val x)) 0 • ![1,0,0] := by
    ext i
    fin_cases i <;> simp [hr.1,hr.2]
  have h := congrArg (W g) heq
  rw [Representation.self_inv_apply,map_smul] at h
  rw [h]
  exact A.smul_mem _ (conjugate_point_mem g A hc hs)

private theorem stabilizer_eq_of_coordinates (A : Submodule (ZMod 2) Vector)
    (g : Group) (hg : ∀ v : Vector, W g v ∈ A ↔ v ∈ NaturalPlaneStabilizer.standard) :
    NaturalPlaneStabilizer.stabilizer A = lineParabolicSL.map (MulAut.conj g).toMonoidHom := by
  have hm (v : Vector) : v ∈ A ↔ W g⁻¹ v ∈ NaturalPlaneStabilizer.standard := by
    have h := hg (W g⁻¹ v)
    rwa [Representation.self_inv_apply] at h
  ext a
  constructor
  · intro ha
    refine ⟨g⁻¹*a*g,?_,by simp [MulAut.conj_apply,mul_assoc]⟩
    rw [← NaturalPlaneStabilizer.stabilizer_standard]
    apply (NaturalPlaneStabilizer.mem_stabilizer NaturalPlaneStabilizer.standard (g⁻¹*a*g)).mpr
    intro x
    calc
      W (g⁻¹*a*g) x ∈ NaturalPlaneStabilizer.standard ↔
          W g (W (g⁻¹*a*g) x) ∈ A := (hg _).symm
      _ ↔ W a (W g x) ∈ A := by
        simp only [map_mul,Module.End.mul_apply,Representation.self_inv_apply]
      _ ↔ W g x ∈ A := (NaturalPlaneStabilizer.mem_stabilizer A a).mp ha _
      _ ↔ x ∈ NaturalPlaneStabilizer.standard := hg x
  · rintro ⟨b,hb,rfl⟩
    rw [NaturalPlaneStabilizer.mem_stabilizer]
    intro x
    calc
      W ((MulAut.conj g) b) x ∈ A ↔
          W g⁻¹ (W ((MulAut.conj g) b) x) ∈ NaturalPlaneStabilizer.standard := hm _
      _ ↔ W b (W g⁻¹ x) ∈ NaturalPlaneStabilizer.standard := by
        simp only [MulAut.conj_apply,map_mul,Module.End.mul_apply,Representation.inv_self_apply]
      _ ↔ W g⁻¹ x ∈ NaturalPlaneStabilizer.standard :=
        (NaturalPlaneStabilizer.mem_stabilizer _ b).mp
          (NaturalPlaneStabilizer.stabilizer_standard.symm ▸ hb) _
      _ ↔ x ∈ A := (hm x).symm

/-- Every trace-zero endomorphism whose image lies in a plane lies in the radical commutator. -/
theorem image_in_plane_le_commutator (A : Submodule (ZMod 2) Vector)
    (hA : Module.finrank (ZMod 2) A = 2) (v : Steinberg)
    (hv : ∀ x : Vector, v.val x ∈ A) :
    v ∈ subspaceCommutator S ⊤ ((NaturalPlaneStabilizer.stabilizer A).pCoreIn 2) := by
  obtain ⟨g,hg⟩ := NaturalPlaneStabilizer.exists_matrix A hA
  have hs := stabilizer_eq_of_coordinates A g hg
  rw [hs,← map_pCoreIn_of_injective 2 lineParabolicSL
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
    lineParabolicSL_pCoreIn_two_eq_R]
  have he : S g⁻¹ v ∈ subspaceCommutator S ⊤ R := by
    apply (mem_commutator_iff _).mpr
    have hmem (x : Vector) : W g⁻¹ (v.val (W g x)) ∈ NaturalPlaneStabilizer.standard := by
      apply (hg _).mp
      rw [Representation.self_inv_apply]
      exact hv _
    have h0 := (NaturalPlaneStabilizer.mem_standard _).mp (hmem (Pi.single 0 1))
    have h1 := (NaturalPlaneStabilizer.mem_standard _).mp (hmem (Pi.single 1 1))
    rw [(coordinates_bottom _).1,(coordinates_bottom _).2,
      S_apply_val,S_apply_val,inv_inv]
    exact ⟨h0,h1⟩
  have hm : S g⁻¹ v ∈
      (subspaceCommutator S ⊤ (R.map (MulAut.conj g).toMonoidHom)).map (S g⁻¹) := by
    rw [conjugate_commutator]
    exact he
  obtain ⟨w,hw,he⟩ := hm
  exact (S.apply_bijective g⁻¹).injective he ▸ hw
end
end BinaryLinearThree.SteinbergStructure.LineRadicalCommutator
