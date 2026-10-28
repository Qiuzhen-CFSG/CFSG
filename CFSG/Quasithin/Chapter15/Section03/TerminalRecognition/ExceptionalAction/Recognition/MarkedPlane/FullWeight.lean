module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.MarkedPlane.FullWeight.WeightTransport
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.MarkedPlane.FullWeight.Orbits
public import Theory.Representation.HexacodeAction.LocalMarking


/-!
# Full weight of the actual definite planes

The source product `Y = Y_E Y_F O₂(Y)` makes Hamming weight invariant under
`Y`: `Y_E` acts by the assumed code scalars, `Y_F` lies in the actual local
group, and `O₂(Y)` centralizes `V`. The full orthogonal residual image then
makes weight constant on each of the three nonzero support patterns of the
two definite summands. Their sizes are three, three and nine.

The image of `T_E` is a Sylow two-subgroup stabilizing the actual four-space.
Scalar stability of the two summands makes that four-space scalar-stable.
The concrete coordinate-fiber calculation in `LocalMarking` therefore gives
weight total 72. Since every nonzero word has weight four or six, the two
three-element definite-plane orbits must both have weight six.

Only the stated scalar premises are added to `SourceConfiguration`. The
argument uses the joint `Y_E`/`Y_F` product and does not exclude a scalar
`Y_F` image, choose a preferred code plane, or assume a plane-orbit condition.
The target remains the image of the original `d.plane i`; `vectorImage_plane`
identifies it with the literal `localPlane` expression for final assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, the
orthogonal decomposition and 15.3.7 on printed pp.1121–1122, the residual
product and Sylow conclusion around 15.3.68 on pp.1154–1155, and the terminal
recognition on p.1155. The code's four-element-field interpretation is K.1.3,
printed p.453. This is a conditional recognition helper, not the assembly of
Theorem 15.3.1.
-/

public section

open Subgroup
open scoped BigOperators IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.MarkedPlane
variable {G : Type*} [Group G] {G₀ M V : Subgroup G}
  {d : NaturalOrthogonalAction M V}
  [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))]
  {hC : IsPGroup 2 (centralizer (V.subgroupOf G₀ : Set G₀))}
  {hcore : pCore 2 G₀ ≤ centralizer (V.subgroupOf G₀ : Set G₀)}
  (c : HexacodeCoordinates (V.subgroupOf G₀) hC hcore)
  (cfg : SourceConfiguration G₀ M V d)

private theorem ambientVector_zero : ambientVector c 0 = 1 := by
  simp [ambientVector]

private theorem vectorImage_planes_disjoint {i j : OrthogonalPlaneIndex} (hij : i ≠ j) :
    Disjoint (vectorImage c (d.plane i)) (vectorImage c (d.plane j)) := by
  rw [disjoint_iff_inf_le]
  intro w hw
  change w = 0
  apply ambientVector_injective c
  rw [ambientVector_zero]
  obtain ⟨u, hu, heu⟩ := (mem_vectorImage c _ w).mp hw.1
  obtain ⟨v, hv, hev⟩ := (mem_vectorImage c _ w).mp hw.2
  have huv : u = v := Subtype.ext (heu.trans hev.symm)
  have he : d.coordinates u = 1 := by
    funext k
    by_cases hk : k = i
    · exact huv ▸ hv k (hk ▸ hij)
    · exact hu k hk
  rw [← heu]
  exact congrArg V.subtype (d.coordinates.injective (he.trans d.coordinates.map_one.symm))

variable [Finite G]

include cfg in
private theorem vectorImage_planes_sup {i j : OrthogonalPlaneIndex} (hij : i ≠ j) :
    vectorImage c (d.plane i) ⊔ vectorImage c (d.plane j) = vectorImage c V := by
  apply Submodule.eq_of_le_of_finrank_eq
  · exact sup_le (vectorImage_mono c (d.plane_le i)) (vectorImage_mono c (d.plane_le j))
  · have h := Submodule.finrank_sup_add_finrank_inf_eq
      (vectorImage c (d.plane i)) (vectorImage c (d.plane j))
    rw [(vectorImage_planes_disjoint c hij).eq_bot, finrank_bot,
      add_zero, vectorImage_plane_finrank c cfg i, vectorImage_plane_finrank c cfg j] at h
    rw [h, vectorImage_vector_finrank c cfg]

include cfg in
private theorem vectorImage_scalar (hscalar : ∀ i, Atlas.Codes.hexZ ∈
    Representation.BinaryOffender.subspaceStabilizer Representation.Hexacode.action
      (vectorImage c (d.plane i))) :
    Atlas.Codes.hexZ ∈ Representation.BinaryOffender.subspaceStabilizer
      Representation.Hexacode.action (vectorImage c V) := by
  rw [← vectorImage_planes_sup c cfg
    (by decide : Multiplicative.ofAdd (0 : ZMod 2) ≠ Multiplicative.ofAdd 1)]
  let P := vectorImage c (d.plane (Multiplicative.ofAdd 0))
  let Q := vectorImage c (d.plane (Multiplicative.ofAdd 1))
  have hz (g : Atlas.Codes.HexAutomorphisms)
      (hP : g ∈ Representation.BinaryOffender.subspaceStabilizer Representation.Hexacode.action P)
      (hQ : g ∈ Representation.BinaryOffender.subspaceStabilizer Representation.Hexacode.action Q) :
      ∀ w ∈ P ⊔ Q, Representation.Hexacode.action g w ∈ P ⊔ Q := by
    intro w hw
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hw
    exact Submodule.mem_sup.mpr ⟨_, (hP u).mpr hu, _, (hQ v).mpr hv, (map_add _ _ _).symm⟩
  intro w
  constructor
  · intro hw
    have h := hz Atlas.Codes.hexZ⁻¹
      ((Representation.BinaryOffender.subspaceStabilizer _ P).inv_mem (hscalar (Multiplicative.ofAdd 0)))
      ((Representation.BinaryOffender.subspaceStabilizer _ Q).inv_mem (hscalar (Multiplicative.ofAdd 1))) _ hw
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using h
  · exact hz _ (hscalar (Multiplicative.ofAdd 0)) (hscalar (Multiplicative.ofAdd 1)) w

omit [Finite G] in
private theorem actorHom_surjective : Function.Surjective (actorHom c) :=
  c.actor.surjective.comp (QuotientGroup.mk'_surjective _)

include cfg in
private theorem vectorImage_sylow : ∃ S : Sylow 2 Atlas.Codes.HexAutomorphisms,
    (S : Subgroup Atlas.Codes.HexAutomorphisms) ≤
      Representation.BinaryOffender.subspaceStabilizer Representation.Hexacode.action
        (vectorImage c V) := by
  obtain ⟨S, hS⟩ := cfg.local_sylow
  refine ⟨S.mapSurjective (actorHom_surjective c), ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  rw [actor_stabilizer_iff c V le_rfl cfg.vector_le]
  apply d.normalizes
  apply cfg.sylow_le
  have hgT : (g : G) ∈ cfg.TE := hS ▸ mem_map_of_mem G₀.subtype hg
  rw [cfg.sylow_stabilizer_eq] at hgT
  exact hgT.1

private noncomputable def sourceVectorEquiv : V ≃ vectorImage c V where
  toFun v := ⟨sourceVector c cfg v, sourceVector_mem c cfg v⟩
  invFun w := ⟨ambientVector c w.val, (mem_vectorImage c V w.val).mp w.property⟩
  left_inv v := Subtype.ext (ambientVector_sourceVector c cfg v)
  right_inv w := by
    apply Subtype.ext
    apply ambientVector_injective c
    exact ambientVector_sourceVector c cfg _

private noncomputable def orthogonalWeight (u : OrthogonalVector) : ℕ :=
  hammingNorm (sourceVector c cfg (d.coordinates.symm u)).val

omit [Finite G] in
private theorem orthogonalWeight_support (hYE : ScalarActionOn c cfg.YE)
    (u v : OrthogonalVector) (huv : ∀ i, u i = 1 ↔ v i = 1) :
    orthogonalWeight c cfg u = orthogonalWeight c cfg v := by
  let _ := orthogonalAction
  obtain ⟨n, hn⟩ := cubic_orbit u v huv
  have hnY : cubicActor n ∈ d.image cfg.Y := by
    rw [cfg.residual_image]
    exact cubicActor_mem n
  obtain ⟨m, hm, hmn⟩ := hnY
  have hconj := sourceVector_weight_conjugate c cfg hYE m hm (d.coordinates.symm u)
  have he : V.normalizerMonoidHom ⟨(m : G), d.normalizes m.property⟩ (d.coordinates.symm u) =
      d.coordinates.symm v := by
    apply d.coordinates.injective
    rw [d.compatible, d.coordinates.apply_symm_apply, d.coordinates.apply_symm_apply, hmn, hn]
  rw [he] at hconj
  exact hconj.symm

omit [Finite G] in
private theorem orthogonalWeight_one : orthogonalWeight c cfg 1 = 0 := by
  simp [orthogonalWeight, sourceVector_one]

omit [Finite G] in
private theorem orthogonalWeight_values (u : OrthogonalVector) (hu : u ≠ 1) :
    orthogonalWeight c cfg u = 4 ∨ orthogonalWeight c cfg u = 6 := by
  have hn : sourceVector c cfg (d.coordinates.symm u) ≠ 0 := by
    intro h
    apply hu
    have hv := sourceVector_injective c cfg (h.trans (sourceVector_one c cfg).symm)
    simpa using congrArg d.coordinates hv
  rcases Atlas.Codes.hex_weights (sourceVector c cfg (d.coordinates.symm u)) with h | h | h
  · exact (hn (Subtype.ext (hammingNorm_eq_zero.mp h))).elim
  · exact Or.inl h
  · exact Or.inr h

private theorem orthogonalWeight_total (hscalar : ∀ i, Atlas.Codes.hexZ ∈
    Representation.BinaryOffender.subspaceStabilizer Representation.Hexacode.action
      (vectorImage c (d.plane i))) : ∑ u, orthogonalWeight c cfg u = 72 := by
  classical
  let _ := Fintype.ofFinite (vectorImage c V)
  obtain ⟨S, hS⟩ := vectorImage_sylow c cfg
  have htotal := Representation.Hexacode.sylow_scalar_four_weight_total
    (vectorImage c V) (vectorImage_vector_finrank c cfg) (vectorImage_scalar c cfg hscalar) S hS
  let e : OrthogonalVector ≃ vectorImage c V :=
    d.coordinates.toEquiv.symm.trans (sourceVectorEquiv c cfg)
  exact (Equiv.sum_comp e (fun w => hammingNorm w.val.val)).trans htotal

/-- Every nonzero vector of either source definite plane has full Hamming
weight, assuming only the two scalar-identification premises. -/
theorem vectorImage_plane_full_weight (hYE : ScalarActionOn c cfg.YE)
    (hscalar : ∀ i, Atlas.Codes.hexZ ∈
      Representation.BinaryOffender.subspaceStabilizer Representation.Hexacode.action
        (vectorImage c (d.plane i))) (i : OrthogonalPlaneIndex)
    (w : vectorImage c (d.plane i)) (hw : w ≠ 0) :
    hammingNorm (w.val : Atlas.Codes.HexWord) = 6 := by
  have hsum := sum_patterns (orthogonalWeight c cfg)
    (orthogonalWeight_support c cfg hYE) (orthogonalWeight_one c cfg)
  rw [orthogonalWeight_total c cfg hscalar] at hsum
  have h1 := orthogonalWeight_values c cfg (patternVector 1) (patternVector_nontrivial 1 (by decide))
  have h2 := orthogonalWeight_values c cfg (patternVector 2) (patternVector_nontrivial 2 (by decide))
  have h3 := orthogonalWeight_values c cfg (patternVector 3) (patternVector_nontrivial 3 (by decide))
  have hh1 : orthogonalWeight c cfg (patternVector 1) = 6 := by omega
  have hh2 : orthogonalWeight c cfg (patternVector 2) = 6 := by omega
  have hwV : w.val ∈ vectorImage c V := vectorImage_mono c (d.plane_le i) w.property
  obtain ⟨v, hv⟩ := sourceVector_surjective c cfg w.val hwV
  have hp : (v : G) ∈ d.plane i := by
    have h := (mem_vectorImage c _ w.val).mp w.property
    rwa [← hv, ambientVector_sourceVector] at h
  have hsupport : d.coordinates v ∈ orthogonalCoordinatePlane i := by
    obtain ⟨u, hu, he⟩ := hp
    have he' : u = v := Subtype.ext he
    exact he' ▸ hu
  have hvne : d.coordinates v ≠ 1 := by
    intro h
    have he : v = 1 := d.coordinates.injective (h.trans d.coordinates.map_one.symm)
    apply hw
    apply Subtype.ext
    rw [← hv, he, sourceVector_one]
    rfl
  have hpat : supportPattern (d.coordinates v) = 1 ∨ supportPattern (d.coordinates v) = 2 := by
    have h : ∀ (i : OrthogonalPlaneIndex) (u : OrthogonalVector),
        (∀ j, j ≠ i → u j = 1) → u ≠ 1 → supportPattern u = 1 ∨ supportPattern u = 2 := by
      decide +kernel
    exact h i _ hsupport hvne
  have hweight := orthogonalWeight_support c cfg hYE _ _ (patternVector_support (d.coordinates v))
  rcases hpat with hpat | hpat
  · rw [hpat, hh1] at hweight
    simpa [orthogonalWeight, hv] using hweight
  · rw [hpat, hh2] at hweight
    simpa [orthogonalWeight, hv] using hweight
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.MarkedPlane
