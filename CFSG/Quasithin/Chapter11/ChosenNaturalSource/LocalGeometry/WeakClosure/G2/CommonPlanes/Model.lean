module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalPlanes.Model
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalRoots.Centralizers
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# Original root-centralizer displacement planes

For every nonzero long-root parameter (a,b) in the A-B plane, the full A-B-C
actor moves its fixed four-space through exactly its displacement plane.
The proof uses the literal six quotient coordinates and two explicit root
displacements. The original coordinate equivalence then recovers the actual
natural plane, with the same conjugator as the long-root subgroup.

Transfer uses this equality to reconstruct full original planes in 11.2.2(5),
adjoining the entire original covering center. No equality with the reciprocal
covering center is asserted here.
Source: Aschbacher--Smith B.4.6(3,7) and 11.2.2(5), printed pp.88,768.
The coordinate formulas use the existing attributed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff. No new ATLAS source is copied.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CommonPlanes
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
open Atlas.G2.Restricted.NaturalCoordinates Atlas.G2.NaturalOffenders
variable (F : Type*) [Field F] [CharP F 2] [Algebra (ZMod 2) F]

private def parameterPlane (a b : F) : (Fin 2 → F) →ₗ[F] (Fin 6 → F) where
  toFun v := ![v 0,a*v 1,b*v 1,0,0,0]
  map_add' v w := by ext i; fin_cases i <;> simp [mul_add]
  map_smul' c v := by ext i; fin_cases i <;> simp [mul_left_comm]

private theorem parameter_fixed (a b : F) (hne : a ≠ 0 ∨ b ≠ 0) (v : Fin 6 → F) :
    binaryAction (rootA a * rootB b) v = v ↔ v 5 = 0 ∧ a*v 4+b*v 3=0 := by
  change Restricted.NaturalCoordinates.action F (rootA a * rootB b) v = v ↔ _
  rw [map_mul,Module.End.mul_apply,action_rootB,action_rootA]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    dsimp at h0 h1 h2
    refine ⟨?_,?_⟩
    · rcases hne with ha | hb
      · exact (mul_eq_zero.mp (add_eq_left.mp h1)).resolve_left ha
      · exact (mul_eq_zero.mp (add_eq_left.mp h2)).resolve_left hb
    · linear_combination h0
  · rintro ⟨h5,h0⟩
    ext i
    fin_cases i <;> simp [h5]
    linear_combination h0

private theorem fixed_parameters (a b : F) (hne : a ≠ 0 ∨ b ≠ 0)
    {v : Fin 6 → F} (hv : binaryAction (rootA a * rootB b) v = v) :
    ∃ t : F, v 5 = 0 ∧ v 3=a*t ∧ v 4=b*t := by
  obtain ⟨h5,hrel⟩ := (parameter_fixed F a b hne v).mp hv
  by_cases ha : a = 0
  · have hb := hne.resolve_left (not_not.mpr ha)
    have h3 : v 3 = 0 := (mul_eq_zero.mp (by simpa [ha] using hrel)).resolve_left hb
    exact ⟨v 4/b,h5,by simp [ha,h3],(mul_div_cancel₀ _ hb).symm⟩
  · refine ⟨v 3/a,h5,(mul_div_cancel₀ _ ha).symm,?_⟩
    apply (mul_right_inj' ha).mp
    have hh : a*(b*(v 3/a)) = b*v 3 := by field_simp
    rw [hh]
    have h := eq_neg_of_add_eq_zero_left hrel
    simpa only [CharTwo.neg_eq] using h

private theorem parameter_displacement_range (a b : F) (hne : a ≠ 0 ∨ b ≠ 0) :
    LinearMap.range (binaryAction (rootA a * rootB b) - LinearMap.id) =
      ((parameterPlane F a b).range).restrictScalars (ZMod 2) := by
  apply le_antisymm
  · rintro _ ⟨v,rfl⟩
    refine ⟨![a*v 4+b*v 3,v 5],?_⟩
    change parameterPlane F a b _ = Restricted.NaturalCoordinates.action F (rootA a*rootB b) v-v
    rw [map_mul,Module.End.mul_apply,action_rootB,action_rootA]
    ext i
    fin_cases i <;> simp [parameterPlane]
    ring
  · rintro _ ⟨v,rfl⟩
    by_cases ha : a = 0
    · have hb := hne.resolve_left (not_not.mpr ha)
      refine ⟨![0,0,0,v 0/b,0,v 1],?_⟩
      change Restricted.NaturalCoordinates.action F (rootA a*rootB b) _ - _ = _
      rw [map_mul,Module.End.mul_apply,action_rootB,action_rootA]
      ext i
      fin_cases i <;> simp [parameterPlane,ha,mul_div_cancel₀,hb]
    · refine ⟨![0,0,0,0,v 0/a,v 1],?_⟩
      change Restricted.NaturalCoordinates.action F (rootA a*rootB b) _ - _ = _
      rw [map_mul,Module.End.mul_apply,action_rootB,action_rootA]
      ext i
      fin_cases i <;> simp [parameterPlane,mul_div_cancel₀,ha]

/-- The whole q³ actor moves the fixed four-space of any nonzero long-root
parameter through exactly that root's displacement plane. -/
theorem parameter_commutator (a b : F) (hne : a ≠ 0 ∨ b ≠ 0) :
    subspaceCommutator (binaryAction (F:=F))
      (fixedSpace (binaryAction (F:=F)) (zpowers (rootA a*rootB b)))
      (EvenTwoRank.elementary F) =
      LinearMap.range (binaryAction (rootA a*rootB b)-LinearMap.id) := by
  rw [parameter_displacement_range F a b hne]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,⟨p,rfl⟩,v,hv,rfl⟩
    obtain ⟨t,h5,h3,h4⟩ := fixed_parameters F a b hne
      ((mem_fixedSpace_zpowers_iff _ _ _).mp hv)
    refine ⟨![p.toAdd 0*(b*t)+p.toAdd 1*(a*t),p.toAdd 2*t],?_⟩
    change parameterPlane F a b _ = Restricted.NaturalCoordinates.action F _ v-v
    simp only [EvenTwoRank.elementaryEmbedding,EvenTwoRank.elementaryParameters,unipotentProduct,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
    ext i
    fin_cases i <;> simp [parameterPlane,h3,h4,h5] <;> ring
  · rintro _ ⟨v,rfl⟩
    let x : Fin 6 → F := ![0,0,0,a,b,0]
    have hx : x ∈ fixedSpace (binaryAction (F:=F)) (zpowers (rootA a*rootB b)) := by
      rw [mem_fixedSpace_zpowers_iff,parameter_fixed F a b hne]
      exact ⟨rfl,by simp [x,mul_comm,CharTwo.add_self_eq_zero]⟩
    have hm (g : Model F) (hg : g ∈ EvenTwoRank.elementary F) :
        binaryAction g x-x ∈ subspaceCommutator (binaryAction (F:=F))
          (fixedSpace (binaryAction (F:=F)) (zpowers (rootA a*rootB b)))
          (EvenTwoRank.elementary F) := Submodule.subset_span ⟨g,hg,x,hx,rfl⟩
    have hc := hm (rootC (v 1)) (rootC_mem_elementary _)
    by_cases ha : a = 0
    · have hb := hne.resolve_left (not_not.mpr ha)
      have hd := hm (rootA (v 0/b)) (rootA_mem_elementary _)
      have he : (binaryAction (rootA (v 0/b)) x-x) + (binaryAction (rootC (v 1)) x-x) =
          parameterPlane F a b v := by
        change (Restricted.NaturalCoordinates.action F (rootA _) x-x) +
          (Restricted.NaturalCoordinates.action F (rootC _) x-x) = _
        ext i
        fin_cases i <;> simp [x,parameterPlane,ha,mul_div_cancel₀,hb,mul_comm]
      exact he ▸ Submodule.add_mem _ hd hc
    · have hd := hm (rootB (v 0/a)) (rootB_mem_elementary _)
      have he : (binaryAction (rootB (v 0/a)) x-x) + (binaryAction (rootC (v 1)) x-x) =
          parameterPlane F a b v := by
        change (Restricted.NaturalCoordinates.action F (rootB _) x-x) +
          (Restricted.NaturalCoordinates.action F (rootC _) x-x) = _
        ext i
        fin_cases i <;> simp [x,parameterPlane,mul_div_cancel₀,ha,mul_comm]
      exact he ▸ Submodule.add_mem _ hd hc
private theorem rootA_displacement_range :
    LinearMap.range (binaryNatural (rootA (1 : F))-LinearMap.id) =
      (naturalPlane F).restrictScalars (ZMod 2) := by
  apply le_antisymm
  · rintro _ ⟨v,rfl⟩
    obtain ⟨x,rfl⟩ := mk_surjective F v
    refine ⟨OrthogonalCover.action F (longRootElement F 1) x-x,?_,?_⟩
    · rw [longRoot_displacement]
      exact ⟨_,rfl⟩
    · rw [map_sub]
      rfl
  · rintro _ ⟨_,⟨w,rfl⟩,rfl⟩
    let x : TraceZero F := ⟨![0,0,0,0,0,0,-w 0,w 1],by simp [Atlas.SplitOctonion.trace]⟩
    refine ⟨mk F x,?_⟩
    have he : OrthogonalCover.action F (longRootElement F 1) x-x = planeLift F w := by
      rw [longRoot_displacement]
      congr 1
      ext i
      fin_cases i <;> simp [x]
    have hh := congrArg (mk F) he
    rw [map_sub] at hh
    exact hh

private theorem displacement_conjugate {H X : Type*} [Group H] [AddCommGroup X]
    [Module (ZMod 2) X] (ρ : Representation (ZMod 2) H X) (u b : H) :
    LinearMap.range (ρ (MulAut.conj u b)-LinearMap.id) =
      (LinearMap.range (ρ b-LinearMap.id)).map (ρ u) := by
  have he : ρ (MulAut.conj u b)-LinearMap.id =
      (ρ u).comp ((ρ b-LinearMap.id).comp (ρ u⁻¹)) := by
    apply LinearMap.ext
    intro v
    simp only [MulAut.conj_apply,LinearMap.sub_apply,LinearMap.comp_apply,
      LinearMap.id_apply,map_mul,Module.End.mul_apply,map_sub,ρ.self_inv_apply]
  rw [he,LinearMap.range_comp,LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (ρ.apply_bijective u⁻¹).surjective,Submodule.map_top]

private theorem root_displacement_range (u : Model F) :
    LinearMap.range (binaryNatural (MulAut.conj u (rootA (1 : F)))-LinearMap.id) =
      ((naturalPlane F).map (Natural.action F u)).restrictScalars (ZMod 2) := by
  rw [displacement_conjugate,rootA_displacement_range]
  ext v
  rfl

/-- Every full long root in the A-B plane gives the corresponding natural
plane by moving its fixed four-space with the actual full A-B-C actor. -/
theorem root_commutator (u : Model F)
    (hZ : LieParabolicSetup.highestRoot.map (MulAut.conj u).toMonoidHom ≤ longRootLocal) :
    subspaceCommutator (binaryNatural (F:=F))
      (fixedSpace (binaryNatural (F:=F))
        (LieParabolicSetup.highestRoot.map (MulAut.conj u).toMonoidHom))
      (EvenTwoRank.elementary F) =
      ((naturalPlane F).map (Natural.action F u)).restrictScalars (ZMod 2) := by
  let z := MulAut.conj u (rootA (1 : F))
  have hz : z ∈ longRootLocal := hZ (mem_map_of_mem _ ⟨Multiplicative.ofAdd 1,rfl⟩)
  obtain ⟨p,hp⟩ := hz
  have hze : z = rootA p.toAdd.1 * rootB p.toAdd.2 := hp.symm
  have hn : p.toAdd.1 ≠ 0 ∨ p.toAdd.2 ≠ 0 := by
    by_contra! h
    have hz1 : z = 1 := by rw [hze,h.1,h.2,rootA_zero,rootB_zero,one_mul]
    have hh := (MulAut.conj u).injective (hz1.trans (map_one _).symm)
    exact one_ne_zero (rootA_injective (hh.trans rootA_zero.symm))
  rw [ReciprocalRoots.root_fixedSpace,←root_displacement_range]
  let e := (equiv F).restrictScalars (ZMod 2)
  have hact (b : Model F) (v : Natural.Space F) :
      binaryAction b (e v) = e (binaryNatural b v) :=
    ((repEquiv F).isIntertwining b v).symm
  apply Submodule.map_injective_of_injective e.injective
  have hf : (fixedSpace (binaryNatural (F:=F)) (zpowers z)).map e.toLinearMap =
      fixedSpace (binaryAction (F:=F)) (zpowers z) := by
    simpa only [Subgroup.map_id] using fixedSpace_map_equivariant
      (binaryNatural (F:=F)) (binaryAction (F:=F)) (MonoidHom.id _) e
      (fun b v => (hact b v).symm) (zpowers z)
  have hc := subspaceCommutator_map_embedding (binaryAction (F:=F)) (binaryNatural (F:=F))
    (MonoidHom.id _) e.toLinearMap hact (EvenTwoRank.elementary F)
    (fixedSpace (binaryNatural (F:=F)) (zpowers z))
  rw [Subgroup.map_id,hf] at hc
  rw [←hc]
  have hd : (LinearMap.range (binaryNatural z-LinearMap.id)).map e.toLinearMap =
      LinearMap.range (binaryAction z-LinearMap.id) := by
    apply le_antisymm
    · rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
      refine ⟨e v,?_⟩
      change binaryAction z (e v)-e v = e (binaryNatural z v-v)
      rw [map_sub,hact]
    · rintro _ ⟨v,rfl⟩
      obtain ⟨w,rfl⟩ := e.surjective v
      refine ⟨binaryNatural z w-w,⟨w,rfl⟩,?_⟩
      change e (binaryNatural z w-w) = binaryAction z (e w)-e w
      rw [map_sub,hact]
  rw [hd,hze]
  exact parameter_commutator F _ _ hn
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CommonPlanes
