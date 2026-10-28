module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Models
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# Residual action on the actual binary G₂ pencil

The long-root cubic and its conjugate by root F lie in the two-residual of
every point stabilizer whose actor contains the actual derived group. Their
differences on the first three octonion coordinates span the pencil plane.
The cubic's three distinct line images exhaust the pencil. Equivariance and
point transitivity transport both calculations to every singular point.

The result applies to both the natural quotient and the trace-zero Weyl
action through the published singular maps. No transitivity or commutator
conclusion is a premise. The point stabilizer is the second (long-root)
parabolic, not the first parabolic with its quaternion residual.

Source: Aschbacher–Smith, 14.7.55(6), combined manuscript (1 March 2004),
printed p.1066, PDF p.1083, with B.4.6, printed pp.88–90. Coordinates use
the existing licensed ATLAS port; see LICENSES/ATLAS.txt.
-/

open Atlas.G2 Atlas.SplitOctonion Atlas.G2.Natural Atlas.G2.Explicit
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.ResidualAction
@[expose] public noncomputable section

/-- The point stabilizer inside the chosen actor, embedded in the full model. -/
def pointParabolic (J : Subgroup (Model (ZMod 2))) (p : SingularPoints (ZMod 2)) :
    Subgroup (Model (ZMod 2)) := MulAction.stabilizer (Model (ZMod 2)) p ⊓ J

/-- The embedded two-residual of the actual relative point stabilizer. -/
def pointResidual (J : Subgroup (Model (ZMod 2))) (p : SingularPoints (ZMod 2)) :
    Subgroup (Model (ZMod 2)) :=
  (pResidual 2 (pointParabolic J p)).map (pointParabolic J p).subtype

theorem cube_mem_derived (g : Model (ZMod 2)) (hg : g ^ 3 = 1) :
    g ∈ commutator (Model (ZMod 2)) := by
  rw [BinaryParabolicPair.commutator_eq_longRootClosure, ← BinaryException.lineSign_kernel,
    MonoidHom.mem_ker]
  have h := congrArg Binary.lineSign hg
  rw [map_pow, map_one] at h
  rcases Int.units_eq_one_or (Binary.lineSign g) with he | he
  · exact he
  · rw [he] at h
    norm_num at h

theorem cube_mem_pointResidual (J : Subgroup (Model (ZMod 2)))
    (hJ : commutator (Model (ZMod 2)) ≤ J) (p : SingularPoints (ZMod 2))
    (g : Model (ZMod 2)) (hg : g ^ 3 = 1) (hp : g • p = p) :
    g ∈ pointResidual J p := by
  have hm : g ∈ pointParabolic J p := ⟨hp, hJ (cube_mem_derived g hg)⟩
  refine ⟨⟨g,hm⟩, ?_, rfl⟩
  apply Subgroup.mem_pResidual_of_orderOf_coprime
  exact (show Nat.Coprime 2 3 by decide).of_dvd_right
    (orderOf_dvd_of_pow_eq_one (show (⟨g,hm⟩ : pointParabolic J p)^3 = 1 from Subtype.ext hg))

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem pencilSpan_stabilizer (f : SingularMap W)
    (σ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant σ)
    (p : SingularPoints (ZMod 2)) :
    MulAction.stabilizer (Model (ZMod 2)) p ≤ subspaceStabilizer σ (pencilSpan f p) := by
  apply le_subspaceStabilizer
  intro g hg x hx
  have he := pencilSpan_equivariant f σ hf g p
  rw [show g • p = p from hg] at he
  rw [← he]
  exact ⟨x,hx,rfl⟩

private def e (i : Fin 3) : TraceZero (ZMod 2) :=
  ⟨basisVector ⟨i.val, by omega⟩, by fin_cases i <;> simp [basisVector, trace]⟩

private theorem e_mem (f : SingularMap W) (i : Fin 3) :
    f.linear (e i) ∈ pencilSpan f firstPoint := by
  rw [pencilSpan_firstPoint]
  exact ⟨e i, basis_mem_distinguishedPlane _ i.isLt, rfl⟩

private def c : Model (ZMod 2) := BinaryCore.movingActor
private def d : Model (ZMod 2) := rootF 1 * c * (rootF 1)⁻¹

private theorem c_fix : c • (firstPoint (K := ZMod 2)) = firstPoint :=
  parabolic_le_pointStabilizer BinaryCore.movingActor_mem

private theorem d_fix : d • (firstPoint (K := ZMod 2)) = firstPoint := by
  apply parabolic_le_pointStabilizer
  have hF : rootF (1 : ZMod 2) ∈ parabolic :=
    unipotent_le_parabolic (Subgroup.subset_closure (by simp))
  exact parabolic.mul_mem (parabolic.mul_mem hF BinaryCore.movingActor_mem) (parabolic.inv_mem hF)

private theorem d_cube : d ^ 3 = 1 := by
  dsimp [d, c]
  rw [conj_pow, BinaryCore.movingActor_cube]
  simp

private theorem c_e1 : traceZeroAction (ZMod 2) c (e 1) - e 1 = e 2 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> decide +kernel

private theorem c_e2 : traceZeroAction (ZMod 2) c (e 2) - e 2 = e 1 + e 2 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> decide +kernel

private theorem d_e2 : traceZeroAction (ZMod 2) d (e 2) - e 2 = e 0 + (e 1 + e 2) := by
  apply Subtype.ext
  funext i
  fin_cases i <;> decide +kernel

theorem pencilSpan_commutator_firstPoint (f : SingularMap W)
    (σ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant σ)
    (J : Subgroup (Model (ZMod 2))) (hJ : commutator (Model (ZMod 2)) ≤ J) :
    subspaceCommutator σ (pencilSpan f firstPoint) (pointResidual J firstPoint) =
      pencilSpan f firstPoint := by
  apply le_antisymm
  · exact subspaceCommutator_le_of_invariant σ
      ((Subgroup.map_subtype_le _).trans (inf_le_left.trans (pencilSpan_stabilizer f σ hf firstPoint)))
  · let S := subspaceCommutator σ (pencilSpan f firstPoint) (pointResidual J firstPoint)
    have hc : c ∈ pointResidual J firstPoint :=
      cube_mem_pointResidual J hJ firstPoint c BinaryCore.movingActor_cube c_fix
    have hd : d ∈ pointResidual J firstPoint :=
      cube_mem_pointResidual J hJ firstPoint d d_cube d_fix
    have hm (g : Model (ZMod 2)) (hg : g ∈ pointResidual J firstPoint) (i : Fin 3) :
        f.linear (traceZeroAction (ZMod 2) g (e i) - e i) ∈ S := by
      rw [map_sub, ← hf]
      exact Submodule.subset_span ⟨g,hg,f.linear (e i),e_mem f i,rfl⟩
    have h2 : f.linear (e 2) ∈ S := by simpa only [c_e1] using hm c hc 1
    have h12 : f.linear (e 1 + e 2) ∈ S := by simpa only [c_e2] using hm c hc 2
    have h1 : f.linear (e 1) ∈ S := by
      have hh := S.sub_mem h12 h2
      simpa only [map_add, add_sub_cancel_right] using hh
    have h0 : f.linear (e 0) ∈ S := by
      have hh := S.sub_mem (hm d hd 2) h12
      simpa only [d_e2, map_add, add_sub_cancel_right] using hh
    change pencilSpan f firstPoint ≤ S
    intro y hy
    rw [pencilSpan_firstPoint] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    have he : x = x.val 0 • e 0 + x.val 1 • e 1 + x.val 2 • e 2 := by
      apply Subtype.ext
      have hh := distinguishedPlane_coordinates hx
      change x.val = ![x.val 0,x.val 1,x.val 2,0,0,0,0,0] at hh
      change x.val = _
      conv_lhs => rw [hh]
      ext i
      fin_cases i <;> simp [e, basisVector]
    rw [he, map_add, map_add, map_smul, map_smul, map_smul]
    exact S.add_mem (S.add_mem (S.smul_mem _ h0) (S.smul_mem _ h1)) (S.smul_mem _ h2)


private theorem normal_of_derived_le (J : Subgroup (Model (ZMod 2)))
    (hJ : commutator (Model (ZMod 2)) ≤ J) : J.Normal :=
  Subgroup.commutator_top_left_le_iff.mp ((Subgroup.commutator_mono le_rfl le_top).trans hJ)

theorem pointParabolic_conj (J : Subgroup (Model (ZMod 2)))
    (hJ : commutator (Model (ZMod 2)) ≤ J) (g : Model (ZMod 2))
    (p : SingularPoints (ZMod 2)) :
    (pointParabolic J p).map (MulAut.conj g).toMonoidHom = pointParabolic J (g • p) := by
  let _ := normal_of_derived_le J hJ
  ext x
  constructor
  · rintro ⟨a,⟨ha,hJa⟩,rfl⟩
    refine ⟨?_, (inferInstance : J.Normal).conj_mem a hJa g⟩
    change (g * a * g⁻¹) • (g • p) = g • p
    change a • p = p at ha
    simp only [SemigroupAction.mul_smul, inv_smul_smul, ha]
  · rintro ⟨hp,hx⟩
    change x • (g • p) = g • p at hp
    refine ⟨g⁻¹ * x * g, ⟨?_, ?_⟩, ?_⟩
    · change (g⁻¹ * x * g) • p = p
      simp only [SemigroupAction.mul_smul, hp, inv_smul_smul]
    · change g⁻¹ * x * g ∈ J
      simpa only [inv_inv] using (inferInstance : J.Normal).conj_mem x hx g⁻¹
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      group

theorem pointResidual_conj (J : Subgroup (Model (ZMod 2)))
    (hJ : commutator (Model (ZMod 2)) ≤ J) (g : Model (ZMod 2))
    (p : SingularPoints (ZMod 2)) :
    (pointResidual J p).map (MulAut.conj g).toMonoidHom = pointResidual J (g • p) := by
  unfold pointResidual
  rw [map_embedded_pResidual, pointParabolic_conj J hJ]

/-- The residual generates the actual three-dimensional pencil span in either
module, uniformly for every actor containing the genuine derived group. -/
theorem pencilSpan_commutator (f : SingularMap W)
    (σ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant σ)
    (J : Subgroup (Model (ZMod 2))) (hJ : commutator (Model (ZMod 2)) ≤ J)
    (p : SingularPoints (ZMod 2)) :
    subspaceCommutator σ (pencilSpan f p) (pointResidual J p) = pencilSpan f p := by
  obtain ⟨g,hg⟩ := exists_smul_firstPoint p
  have he : (pencilSpan f firstPoint).map (σ g⁻¹) = pencilSpan f p := by
    rw [pencilSpan_equivariant f σ hf, ← hg, inv_smul_smul]
  have hact (a : Model (ZMod 2)) (w : W) :
      σ a (σ g⁻¹ w) = σ g⁻¹ (σ ((MulAut.conj g) a) w) := by
    change σ a (σ g⁻¹ w) = σ g⁻¹ (σ (g*a*g⁻¹) w)
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  have hh := subspaceCommutator_map_embedding σ σ (MulAut.conj g).toMonoidHom
    (σ g⁻¹) hact (pointResidual J p) (pencilSpan f firstPoint)
  rw [he, pointResidual_conj J hJ, hg, pencilSpan_commutator_firstPoint f σ hf J hJ, he] at hh
  exact hh


private def orbitLine (i : Fin 3) : ZeroProductLine (ZMod 2) := c ^ i.val • standardLine

private theorem orbitLine_incident (i : Fin 3) : pointOnLine firstPoint (orbitLine i) := by
  have hf : c ^ i.val • (firstPoint (K := ZMod 2)) = firstPoint :=
    (MulAction.stabilizer (Model (ZMod 2)) firstPoint).pow_mem c_fix i.val
  rw [orbitLine, ← hf]
  exact (pointOnLine_smul_iff (c ^ i.val) firstPoint standardLine).mpr firstPoint_on_standardLine

private theorem orbitLine_plane (i : Fin 3) :
    (orbitLine i).val = Submodule.span (ZMod 2)
      {basisVector 0, (c ^ i.val).val (basisVector 1)} := by
  change (Submodule.span (ZMod 2) {basisVector 0,basisVector 1}).map
    (c ^ i.val).val.toLinearMap = _
  rw [Submodule.map_span, Set.image_pair]
  have he : (c ^ i.val).val (basisVector 0) = basisVector 0 := by
    fin_cases i <;> ext j <;> fin_cases j <;> decide +kernel
  change Submodule.span (ZMod 2) {(c ^ i.val).val (basisVector 0),
    (c ^ i.val).val (basisVector 1)} = _
  rw [he]

private theorem orbitLine_injective : Function.Injective orbitLine := by
  intro i j he
  have hm : (c ^ i.val).val (basisVector 1) ∈ (orbitLine j).val := by
    rw [← he, orbitLine_plane]
    exact Submodule.subset_span (by simp)
  rw [orbitLine_plane] at hm
  obtain ⟨a,b,hab⟩ := Submodule.mem_span_pair.mp hm
  have h1 := congrFun hab 1
  have h2 := congrFun hab 2
  have ht : ∀ (i j : Fin 3) (a b : ZMod 2),
      (a • (basisVector 0 : Carrier (ZMod 2)) + b • (c ^ j.val).val (basisVector 1) : Carrier (ZMod 2)) 1 =
        (c ^ i.val).val (basisVector 1) 1 →
      (a • (basisVector 0 : Carrier (ZMod 2)) + b • (c ^ j.val).val (basisVector 1) : Carrier (ZMod 2)) 2 =
        (c ^ i.val).val (basisVector 1) 2 → i = j := by decide +kernel
  exact ht i j a b h1 h2

private theorem orbitLine_exhausts (L : ZeroProductLine (ZMod 2))
    (hL : pointOnLine firstPoint L) : ∃ i, orbitLine i = L := by
  let F : Fin 3 → {L : ZeroProductLine (ZMod 2) // pointOnLine firstPoint L} :=
    fun i => ⟨orbitLine i,orbitLine_incident i⟩
  have hF : Function.Injective F := fun i j h => orbitLine_injective (congrArg Subtype.val h)
  have hfin : Finite {L : ZeroProductLine (ZMod 2) // pointOnLine firstPoint L} :=
    Nat.finite_of_card_ne_zero (by rw [pencil_card]; decide)
  have hsurj := ((Nat.bijective_iff_injective_and_card F).mpr
    ⟨hF, by rw [pencil_card]; simp⟩).2
  obtain ⟨i,hi⟩ := hsurj ⟨L,hL⟩
  exact ⟨i,congrArg Subtype.val hi⟩

/-- The concrete cubic already acts transitively on the base pencil. -/
theorem pencil_transitive_firstPoint (J : Subgroup (Model (ZMod 2)))
    (hJ : commutator (Model (ZMod 2)) ≤ J)
    (L M : ZeroProductLine (ZMod 2)) (hL : pointOnLine firstPoint L)
    (hM : pointOnLine firstPoint M) :
    ∃ g ∈ pointResidual J firstPoint, g • L = M := by
  obtain ⟨i,rfl⟩ := orbitLine_exhausts L hL
  obtain ⟨j,rfl⟩ := orbitLine_exhausts M hM
  have hc := cube_mem_pointResidual J hJ firstPoint c BinaryCore.movingActor_cube c_fix
  refine ⟨c^j.val * (c^i.val)⁻¹,
    (pointResidual J firstPoint).mul_mem ((pointResidual J firstPoint).pow_mem hc _)
      ((pointResidual J firstPoint).inv_mem ((pointResidual J firstPoint).pow_mem hc _)), ?_⟩
  simp only [orbitLine, SemigroupAction.mul_smul, inv_smul_smul]

/-- Transitivity of the embedded residual on the actual incident zero-product
lines, uniformly for the full and derived actors and every marked point. -/
theorem pencil_transitive (J : Subgroup (Model (ZMod 2)))
    (hJ : commutator (Model (ZMod 2)) ≤ J) (p : SingularPoints (ZMod 2))
    (L M : ZeroProductLine (ZMod 2)) (hL : pointOnLine p L) (hM : pointOnLine p M) :
    ∃ g ∈ pointResidual J p, g • L = M := by
  obtain ⟨a,ha⟩ := exists_smul_firstPoint p
  have hLa : pointOnLine firstPoint (a • L) := by
    rw [← ha]
    exact (pointOnLine_smul_iff a p L).mpr hL
  have hMa : pointOnLine firstPoint (a • M) := by
    rw [← ha]
    exact (pointOnLine_smul_iff a p M).mpr hM
  obtain ⟨b,hb,he⟩ := pencil_transitive_firstPoint J hJ (a • L) (a • M) hLa hMa
  have hm : a⁻¹ * b * a ∈ pointResidual J p := by
    have hh := Subgroup.mem_map_of_mem (MulAut.conj a⁻¹).toMonoidHom hb
    rw [pointResidual_conj J hJ, ← ha, inv_smul_smul] at hh
    exact hh
  refine ⟨a⁻¹*b*a,hm,?_⟩
  simp only [SemigroupAction.mul_smul, he, inv_smul_smul]

end
end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.ResidualAction
