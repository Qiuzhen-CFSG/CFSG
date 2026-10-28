module

public import Theory.Representation.BinaryDuadModule
public import Theory.SpecificGroups.SymmetricSix.Parabolics.QuadrangleActions
public import Theory.Representation.SubspaceQuotient
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.OrbitQuotient

/-!
# The binary S₆ incidence building

The vertices are the actual fifteen duads and fifteen synthemes. Edges are
incident pairs, with the simultaneous six-letter permutation action. The two
existing polar equivalences identify every edge with a nonzero binary vector
contained in a totally isotropic plane, and the component equations retain the
actual linear S₆ action.

The boundary sends an edge to its endpoints; the coboundary adds the values at
those endpoints. Their kernel and cokernel are the top reduced homology and
cohomology of this rank-two building. Connectivity makes the coboundary kernel
one-dimensional, hence top cohomology has dimension sixteen. A flag stabilizer
is the proved Sylow two-subgroup, so every finite-dimensional binary simple
module is an equivariant quotient of the forty-five-dimensional flag module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.5.1–2,
printed pp.342–343 (PDF pp.353–354), using the duad–syntheme polar model of I.5.4.
The tensor comparison and the fifteen-point quotient calculations are separate
inputs to the catalogue reduction.
-/

@[expose] public section

open Theory.SpecificGroups.SymmetricSix BinaryPermutation Representation
namespace BinaryAlternatingSix.SymmetricCatalogue

/-- An edge of the actual duad–syntheme incidence graph. -/
abbrev Flag := {p : Duad × Syntheme // incident p.1 p.2}

def baseFlag : Flag := ⟨(0, 0), by decide⟩

noncomputable instance flagAction : MulAction S6 Flag where
  smul g f := ⟨(g • f.val.1, synthemeAct g f.val.2),
    (incident_act_iff g _ _).mpr f.property⟩
  one_smul f := Subtype.ext (Prod.ext (one_smul S6 f.val.1) (synthemeAct_one f.val.2))
  mul_smul g h f := Subtype.ext (Prod.ext (mul_smul g h f.val.1)
    (synthemeAct_mul g h f.val.2))

@[simp] theorem flag_smul_point (g : S6) (f : Flag) :
    (g • f).val.1 = g • f.val.1 := rfl

@[simp] theorem flag_smul_line (g : S6) (f : Flag) :
    (g • f).val.2 = synthemeAct g f.val.2 := rfl

theorem flag_card : Fintype.card Flag = 45 := by decide +kernel

noncomputable def flagPerm : S6 →* Equiv.Perm Flag := MulAction.toPermHom S6 Flag

theorem flag_stabilizer (g : S6) : g ∈ borel ↔ flagPerm g baseFlag = baseFlag := by
  have hd : g ∈ duadStabilizer ↔ g • (0 : Duad) = 0 := by
    rw [← duad_stabilizer_zero]; rfl
  have hs : g ∈ synthemeStabilizer ↔ synthemeAct g 0 = 0 := by
    rw [← syntheme_stabilizer_zero]; rfl
  change g ∈ duadStabilizer ∧ g ∈ synthemeStabilizer ↔ _
  rw [hd, hs]
  constructor
  · rintro ⟨h, k⟩
    exact Subtype.ext (Prod.ext h k)
  · intro h
    exact ⟨congrArg (fun f : Flag => f.val.1) h,
      congrArg (fun f : Flag => f.val.2) h⟩

theorem flag_reachable (f : Flag) : ∃ g : S6, flagPerm g baseFlag = f := by
  obtain ⟨g, hg, hs⟩ := flag_transitive 0 f.val.1 0 f.val.2 (by decide) f.property
  exact ⟨g, Subtype.ext (Prod.ext hg hs)⟩

abbrev FlagModule := Full Flag
abbrev VertexModule := Full Duad × Full Syntheme

noncomputable def flagRepresentation : Representation (ZMod 2) S6 FlagModule :=
  (representation Flag).comp flagPerm

noncomputable def linePerm : S6 →* Equiv.Perm Syntheme :=
  @MulAction.toPermHom S6 Syntheme _ synthemeAction

noncomputable def lineRepresentation : Representation (ZMod 2) S6 (Full Syntheme) :=
  (representation Syntheme).comp linePerm

noncomputable def vertexRepresentation : Representation (ZMod 2) S6 VertexModule :=
  BinaryDuadModule.pointAction.prod lineRepresentation

@[simp] theorem flagRepresentation_apply (g : S6) (v : FlagModule) (f : Flag) :
    flagRepresentation g v f = v (g⁻¹ • f) := rfl

@[simp] theorem lineRepresentation_apply (g : S6) (v : Full Syntheme) (s : Syntheme) :
    lineRepresentation g v s = v (synthemeAct g⁻¹ s) := rfl

/-- The graph coboundary: add the values at the two ends of an edge. -/
def coboundaryLinear : VertexModule →ₗ[ZMod 2] FlagModule where
  toFun v f := v.1 f.val.1 + v.2 f.val.2
  map_add' u v := by ext f; simp; ring
  map_smul' a v := by ext f; simp [mul_add]

noncomputable def coboundary : vertexRepresentation.IntertwiningMap flagRepresentation where
  toLinearMap := coboundaryLinear
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    funext f
    rfl

/-- The image of degree-zero cochains in the flag module. -/
noncomputable def coboundaries : Subrepresentation flagRepresentation := coboundary.range

/-- Top reduced cohomology of the rank-two incidence building. -/
abbrev TopCohomology := FlagModule ⧸ coboundaries.toSubmodule

noncomputable def topCohomologyRepresentation : Representation (ZMod 2) S6 TopCohomology :=
  coboundaries.quotientRepresentation

def edgeVertices (f : Flag) : VertexModule :=
  (Pi.single f.val.1 1, Pi.single f.val.2 1)

noncomputable def topCohomologyProjection :
    flagRepresentation.IntertwiningMap topCohomologyRepresentation where
  toLinearMap := coboundaries.toSubmodule.mkQ
  isIntertwining' _ := rfl

theorem topCohomologyProjection_surjective : Function.Surjective topCohomologyProjection :=
  Submodule.mkQ_surjective _

/-- The boundary sends an edge to the sum of its two vertices. -/
def boundaryLinear : FlagModule →ₗ[ZMod 2] VertexModule where
  toFun v := ∑ f : Flag, v f • edgeVertices f
  map_add' u v := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a v := by simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, smul_eq_mul, RingHom.id_apply]

private theorem single_point_action (g : S6) (d : Duad) :
    BinaryDuadModule.pointAction g (Pi.single d 1) = Pi.single (g • d) 1 := by
  ext e
  simp [BinaryDuadModule.pointAction, Pi.single_apply, inv_smul_eq_iff]

private theorem single_line_action (g : S6) (s : Syntheme) :
    lineRepresentation g (Pi.single s 1) = Pi.single (synthemeAct g s) 1 := by
  let := synthemeAction
  ext t
  change (Pi.single s (1 : ZMod 2) : Full Syntheme) (g⁻¹ • t) =
    (Pi.single (g • s) 1 : Full Syntheme) t
  simp [Pi.single_apply, inv_smul_eq_iff]

private theorem edgeVertices_action (g : S6) (f : Flag) :
    vertexRepresentation g (edgeVertices f) = edgeVertices (g • f) :=
  Prod.ext (single_point_action g _) (single_line_action g _)

theorem boundaryLinear_equivariant (g : S6) (v : FlagModule) :
    boundaryLinear (flagRepresentation g v) = vertexRepresentation g (boundaryLinear v) := by
  simp only [boundaryLinear, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    flagRepresentation_apply, edgeVertices_action]
  exact (Equiv.sum_comp (MulAction.toPerm g)
    (fun f : Flag => v (g⁻¹ • f) • edgeVertices f)).symm.trans (by simp)

noncomputable def boundary : flagRepresentation.IntertwiningMap vertexRepresentation where
  toLinearMap := boundaryLinear
  isIntertwining' g := LinearMap.ext (boundaryLinear_equivariant g)

/-- Since the building is a graph, its top reduced homology is its cycle space. -/
noncomputable def cycles : Subrepresentation flagRepresentation := boundary.ker

noncomputable abbrev TopHomology := cycles.toSubmodule

noncomputable def topHomologyRepresentation : Representation (ZMod 2) S6 TopHomology :=
  cycles.toRepresentation

theorem boundaryLinear_apply_point (v : FlagModule) (d : Duad) :
    (boundaryLinear v).1 d = ∑ f : Flag, if f.val.1 = d then v f else 0 := by
  simp [boundaryLinear, edgeVertices, Prod.fst_sum, Finset.sum_apply, Pi.single_apply, eq_comm]

theorem boundaryLinear_apply_line (v : FlagModule) (s : Syntheme) :
    (boundaryLinear v).2 s = ∑ f : Flag, if f.val.2 = s then v f else 0 := by
  simp [boundaryLinear, edgeVertices, Prod.snd_sum, Finset.sum_apply, Pi.single_apply, eq_comm]

theorem mem_cycles_iff (v : FlagModule) : v ∈ cycles ↔
    (∀ d : Duad, (∑ f : Flag, if f.val.1 = d then v f else 0) = 0) ∧
    (∀ s : Syntheme, (∑ f : Flag, if f.val.2 = s then v f else 0) = 0) := by
  change boundaryLinear v = 0 ↔ _
  rw [Prod.ext_iff, funext_iff, funext_iff]
  simp only [boundaryLinear_apply_point, boundaryLinear_apply_line, Prod.fst_zero,
    Prod.snd_zero, Pi.zero_apply]

theorem irreducible_flag_quotient
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) S6 V) [IsIrreducible ρ] :
    ∃ f : flagRepresentation.IntertwiningMap ρ, Function.Surjective f :=
  BinaryLinearThree.IrreducibleCatalogue.irreducible_permutation_quotient
    flagPerm baseFlag borel borelSylow.isPGroup' flag_stabilizer flag_reachable ρ

/-- The actual flags in the binary symplectic four-space. In characteristic
two, a projective point has a unique nonzero vector. -/
abbrev PolarFlag := {p : BinaryPoint × BinaryLine // p.1.val ∈ p.2.val}

/-- Incidence identifies all duad–syntheme flags with all symplectic flags. -/
noncomputable def polarFlagEquiv : Flag ≃ PolarFlag :=
  (Equiv.prodCongr duadPolarEquiv synthemePolarEquiv).subtypeEquiv
    (fun p => polar_incidence_equivalence p.1 p.2)

theorem polarFlagEquiv_point_action (g : S6) (f : Flag) :
    (polarFlagEquiv (g • f)).val.1.val =
      polarLinearMap g (polarFlagEquiv f).val.1.val :=
  (polarAction_vector g f.val.1).symm

theorem polarFlagEquiv_line_action (g : S6) (f : Flag) :
    (polarFlagEquiv (g • f)).val.2.val =
      (polarFlagEquiv f).val.2.val.map (polarLinearMap g) :=
  polarLine_act g f.val.2

private theorem point_path (d : Duad) :
    ∃ (e : Duad) (s t : Syntheme),
      incident 0 s ∧ incident e s ∧ incident e t ∧ incident d t := by
  decide +revert +kernel

private theorem line_has_point (s : Syntheme) : ∃ d : Duad, incident d s := by
  decide +revert +kernel

/-- The connected incidence graph has only constant zero-coboundaries. -/
theorem coboundary_eq_zero_iff (v : VertexModule) : coboundary v = 0 ↔
    ∃ c : ZMod 2, v = (fun _ => c, fun _ => c) := by
  constructor
  · intro hv
    have he (d : Duad) (s : Syntheme) (h : incident d s) : v.1 d = v.2 s := by
      apply CharTwo.add_eq_zero.mp
      exact congrFun hv ⟨(d, s), h⟩
    have hp (d : Duad) : v.1 d = v.1 0 := by
      obtain ⟨e, s, t, h₀, he₀, he₁, hd⟩ := point_path d
      exact (he d t hd).trans ((he e t he₁).symm.trans
        ((he e s he₀).trans (he 0 s h₀).symm))
    refine ⟨v.1 0, Prod.ext (funext hp) (funext fun s => ?_)⟩
    obtain ⟨d, hd⟩ := line_has_point s
    exact (he d s hd).symm.trans (hp d)
  · rintro ⟨c, rfl⟩
    funext f
    exact CharTwo.add_self_eq_zero c

private def diagonalConstant : ZMod 2 →ₗ[ZMod 2] VertexModule where
  toFun c := (fun _ => c, fun _ => c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem diagonalConstant_injective : Function.Injective diagonalConstant := by
  intro c d h
  exact congrArg (fun v : VertexModule => v.1 0) h

theorem coboundary_ker_finrank : Module.finrank (ZMod 2) coboundaryLinear.ker = 1 := by
  have hk : coboundaryLinear.ker = diagonalConstant.range := by
    ext v
    exact (coboundary_eq_zero_iff v).trans (by simp only [LinearMap.mem_range, eq_comm]; rfl)
  rw [hk, LinearMap.finrank_range_of_inj diagonalConstant_injective]
  exact Module.finrank_self _

theorem coboundaries_finrank : Module.finrank (ZMod 2) coboundaries.toSubmodule = 29 := by
  have h := coboundaryLinear.finrank_range_add_finrank_ker
  rw [coboundary_ker_finrank] at h
  have hv : Module.finrank (ZMod 2) VertexModule = 30 := by
    simp [VertexModule, Full, Module.finrank_prod]
  rw [hv] at h
  change Module.finrank (ZMod 2) coboundaryLinear.range = 29
  omega

theorem topCohomology_finrank : Module.finrank (ZMod 2) TopCohomology = 16 := by
  have h := coboundaries.toSubmodule.finrank_quotient_add_finrank
  rw [coboundaries_finrank] at h
  have hf : Module.finrank (ZMod 2) FlagModule = 45 := by
    simp only [FlagModule, Full, Module.finrank_fintype_fun_eq_card, flag_card]
  rw [hf] at h
  change Module.finrank (ZMod 2) (FlagModule ⧸ coboundaries.toSubmodule) = 16
  omega


end BinaryAlternatingSix.SymmetricCatalogue
