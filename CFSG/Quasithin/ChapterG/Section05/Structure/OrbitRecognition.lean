module

public import CFSG.Quasithin.ChapterG.Section05.Basic
public import Theory.Representation.BinaryDuadStructure.Universal
public import Theory.Representation.BinaryDuadStructure.OrbitRelations.StabilizerPlane

/-!
# Recognition from the original orbit hypotheses of G.5.3(6)

A nonzero vector fixed by the literal point parabolic descends along the left
cosets to an equivariant configuration on the fifteen duads. Its stabilizer is
exactly the point parabolic: otherwise maximality makes the vector fixed by all
of A₆, contradicting the two-dimensional line-parabolic orbit span. Thus the
configuration is injective. The three nonzero images on each line sum to zero,
so the spanning configuration gives the explicit surjective map from the
universal line quotient. Its already proved quotient classification yields an
actual equivalence with the marked natural module or its five-dimensional cover.

No faithfulness, irreducibility, or finite-dimensionality of the target is assumed.
Source: Aschbacher–Smith, G.5.3(6), printed pp.343–344 (PDF pp.354–355).
-/

public section

open Theory.SpecificGroups.SymmetricSix BinaryDuadStructure

namespace CFSG.Quasithin.ChapterG.Section05.Structure
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

private noncomputable def orbitCosetMap (ρ : Representation (ZMod 2) G W) (w : W)
    (hfix : ∀ g : G1, ρ g.val w = w) : G ⧸ G1 → W :=
  Quotient.lift (fun g => ρ g w) (by
    intro g h hgh
    have hh := hfix ⟨g⁻¹ * h, QuotientGroup.leftRel_apply.mp hgh⟩
    have hh' := congrArg (ρ g) hh
    simpa only [map_mul, Module.End.mul_apply, Representation.self_inv_apply] using hh'.symm)

/-- The well-defined orbit configuration on duads, using the literal left-coset
identification `cosetEquiv : G ⧸ G1 ≃ Omega`. -/
noncomputable def orbitConfiguration (ρ : Representation (ZMod 2) G W) (w : W)
    (hfix : ∀ g : G1, ρ g.val w = w) : Duad → W :=
  fun d => orbitCosetMap ρ w hfix (cosetEquiv.symm d)

@[simp] theorem orbitConfiguration_smul_zero (ρ : Representation (ZMod 2) G W) (w : W)
    (hfix : ∀ g : G1, ρ g.val w = w) (g : G) :
    orbitConfiguration ρ w hfix (g • 0) = ρ g w := by
  rw [← cosetEquiv_mk]
  simp only [orbitConfiguration, Equiv.symm_apply_apply]
  rfl

@[simp] theorem orbitConfiguration_zero (ρ : Representation (ZMod 2) G W) (w : W)
    (hfix : ∀ g : G1, ρ g.val w = w) : orbitConfiguration ρ w hfix 0 = w := by
  simpa using orbitConfiguration_smul_zero ρ w hfix 1

theorem orbitConfiguration_equivariant (ρ : Representation (ZMod 2) G W) (w : W)
    (hfix : ∀ g : G1, ρ g.val w = w) (g : G) (d : Duad) :
    orbitConfiguration ρ w hfix (g • d) = ρ g (orbitConfiguration ρ w hfix d) := by
  obtain ⟨h, rfl⟩ := a6_duad_transitive 0 d
  rw [← mul_smul, orbitConfiguration_smul_zero, orbitConfiguration_smul_zero, map_mul,
    Module.End.mul_apply]

private def vectorStabilizer (ρ : Representation (ZMod 2) G W) (w : W) : Subgroup G where
  carrier := {g | ρ g w = w}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    change ρ g w = w at hg
    change ρ h w = w at hh
    change ρ (g * h) w = w
    rw [map_mul, Module.End.mul_apply, hh, hg]
  inv_mem' {g} hg := by
    change ρ g⁻¹ w = w
    change ρ g w = w at hg
    exact (congrArg (ρ g⁻¹) hg).symm.trans (ρ.inv_self_apply g w)

private theorem vectorStabilizer_eq (ρ : Representation (ZMod 2) G W) (w : W) (hw : w ≠ 0)
    (hfix : ∀ g : G1, ρ g.val w = w)
    (hdim : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range (fun g : G2 => ρ g.val w))) = 2) :
    vectorStabilizer ρ w = G1 := by
  have hle : G1 ≤ vectorStabilizer ρ w := fun g hg => hfix ⟨g, hg⟩
  rcases a6DuadStabilizer_isCoatom.le_iff.mp hle with htop | heq
  · have hrange : Set.range (fun g : G2 => ρ g.val w) = {w} := by
      ext x
      constructor
      · rintro ⟨g, rfl⟩
        exact (show g.val ∈ vectorStabilizer ρ w from htop ▸ Subgroup.mem_top _)
      · rintro rfl
        exact ⟨1, by simp⟩
    rw [hrange, finrank_span_singleton hw] at hdim
    omega
  · exact heq

/-- The orbit-plane hypothesis rules out a constant configuration; maximality of
the literal point stabilizer then makes the configuration injective. -/
theorem orbitConfiguration_injective (ρ : Representation (ZMod 2) G W) (w : W) (hw : w ≠ 0)
    (hfix : ∀ g : G1, ρ g.val w = w)
    (hdim : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range (fun g : G2 => ρ g.val w))) = 2) :
    Function.Injective (orbitConfiguration ρ w hfix) := by
  intro d e hde
  obtain ⟨g, rfl⟩ := a6_duad_transitive 0 d
  obtain ⟨h, rfl⟩ := a6_duad_transitive 0 e
  rw [orbitConfiguration_smul_zero, orbitConfiguration_smul_zero] at hde
  have hmem : g⁻¹ * h ∈ vectorStabilizer ρ w := by
    change ρ (g⁻¹ * h) w = w
    rw [map_mul, Module.End.mul_apply, ← hde, Representation.inv_self_apply]
  rw [vectorStabilizer_eq ρ w hw hfix hdim] at hmem
  change g⁻¹ * h ∈ a6DuadStabilizer at hmem
  rw [← a6_duad_stabilizer_zero] at hmem
  change (g⁻¹ * h) • (0 : Duad) = 0 at hmem
  rw [mul_smul, inv_smul_eq_iff] at hmem
  exact hmem.symm

theorem orbitConfiguration_ne_zero (ρ : Representation (ZMod 2) G W) (w : W) (hw : w ≠ 0)
    (hfix : ∀ g : G1, ρ g.val w = w) (d : Duad) :
    orbitConfiguration ρ w hfix d ≠ 0 := by
  obtain ⟨g, rfl⟩ := a6_duad_transitive 0 d
  rw [orbitConfiguration_smul_zero]
  exact fun h => hw ((ρ.apply_bijective g).injective (h.trans (map_zero _).symm))

theorem orbitConfiguration_range (ρ : Representation (ZMod 2) G W) (w : W)
    (hfix : ∀ g : G1, ρ g.val w = w) :
    Set.range (orbitConfiguration ρ w hfix) = Set.range (fun g : G => ρ g w) := by
  ext x
  constructor
  · rintro ⟨d, rfl⟩
    obtain ⟨g, rfl⟩ := a6_duad_transitive 0 d
    exact ⟨g, (orbitConfiguration_smul_zero ρ w hfix g).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g • 0, orbitConfiguration_smul_zero ρ w hfix g⟩

/-- The source orbit-plane hypothesis implies the actual universal line relations. -/
theorem orbit_line_relations (ρ : Representation (ZMod 2) G W) (w : W) (hw : w ≠ 0)
    (hfix : ∀ g : G1, ρ g.val w = w)
    (hdim : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range (fun g : G2 => ρ g.val w))) = 2)
    (s : Syntheme) :
    ∑ d ∈ Finset.univ.filter (fun d => incident d s), orbitConfiguration ρ w hfix d = 0 := by
  apply OrbitRelations.line_relations_of_injective_orbit_plane ρ (orbitConfiguration ρ w hfix)
    (orbitConfiguration_ne_zero ρ w hw hfix)
    (orbitConfiguration_injective ρ w hw hfix hdim)
    (orbitConfiguration_equivariant ρ w hfix)
  rw [orbitConfiguration_zero]
  exact hdim

/-- The explicit equivariant factor of the permutation-basis evaluation through
`LineQuotient`, with no extra relations assumed beyond the source orbit hypothesis. -/
noncomputable def orbitUniversalMap (ρ : Representation (ZMod 2) G W) (w : W) (hw : w ≠ 0)
    (hfix : ∀ g : G1, ρ g.val w = w)
    (hdim : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range (fun g : G2 => ρ g.val w))) = 2) :
    lineQuotientAction.IntertwiningMap ρ :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (lineQuotientLift (orbitConfiguration ρ w hfix) (orbit_line_relations ρ w hw hfix hdim))
    (lineQuotientLift_equivariant ρ _ _ (orbitConfiguration_equivariant ρ w hfix))

@[simp] theorem orbitUniversalMap_point (ρ : Representation (ZMod 2) G W) (w : W) (hw : w ≠ 0)
    (hfix : ∀ g : G1, ρ g.val w = w)
    (hdim : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range (fun g : G2 => ρ g.val w))) = 2)
    (d : Duad) :
    orbitUniversalMap ρ w hw hfix hdim (pointClass d) = orbitConfiguration ρ w hfix d :=
  lineQuotientLift_point _ (orbit_line_relations ρ w hw hfix hdim) d

/-- On the point indexed by the left coset of g, the universal map has value ρ(g)w. -/
theorem orbitUniversalMap_point_smul_zero (ρ : Representation (ZMod 2) G W) (w : W)
    (hw : w ≠ 0) (hfix : ∀ g : G1, ρ g.val w = w)
    (hdim : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range (fun g : G2 => ρ g.val w))) = 2)
    (g : G) : orbitUniversalMap ρ w hw hfix hdim (pointClass (g • 0)) = ρ g w := by
  rw [orbitUniversalMap_point, orbitConfiguration_smul_zero]

/-- Orbit generation makes the literal universal factor map surjective. -/
theorem orbitUniversalMap_surjective (ρ : Representation (ZMod 2) G W) (w : W) (hw : w ≠ 0)
    (hspan : Submodule.span (ZMod 2) (Set.range (fun g : G => ρ g w)) = ⊤)
    (hfix : ∀ g : G1, ρ g.val w = w)
    (hdim : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range (fun g : G2 => ρ g.val w))) = 2) :
    Function.Surjective (orbitUniversalMap ρ w hw hfix hdim) := by
  apply lineQuotientLift_surjective _ (orbit_line_relations ρ w hw hfix hdim)
  rw [orbitConfiguration_range]
  exact hspan

/-- Aschbacher–Smith G.5.3(6), with precisely its original orbit hypotheses.
The second marked representation is the actual five-dimensional covering module,
whose covering map is `BinaryDuadStructure.coreNaturalProjection`. -/
theorem orbit_recognition (ρ : Representation (ZMod 2) G W) (w : W) (hw : w ≠ 0)
    (hspan : Submodule.span (ZMod 2) (Set.range (fun g : G => ρ g w)) = ⊤)
    (hfix : ∀ g : G1, ρ g.val w = w)
    (hdim : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range (fun g : G2 => ρ g.val w))) = 2) :
    Nonempty (Representation.Equiv naturalAction ρ) ∨
      Nonempty (coreQuotientAction.Equiv ρ) := by
  let : Nontrivial W := ⟨⟨w, 0, hw⟩⟩
  apply lineConfiguration_alternatives ρ (orbitConfiguration ρ w hfix)
    (orbit_line_relations ρ w hw hfix hdim) _ (orbitConfiguration_equivariant ρ w hfix)
  rw [orbitConfiguration_range]
  exact hspan

end CFSG.Quasithin.ChapterG.Section05.Structure
