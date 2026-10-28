module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Tetrahedral.Reference
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.FixedDimension

/-!
# Integral and involution markings for the reference tetrahedral orbit

The reference integral cubic is the image of the retained icosian word, with
no change of representative. Commutation with its central-sign quotient lifts
to actual commutation: a discrepancy of central negation contradicts the cube
identity. Consequently its full integral centralizer maps onto the required
centralizer, with precisely the sign kernel.

We mark one double transposition in the literal scalar tetrahedron. Every
ambient transport has a lift squaring to negation; whenever the transport lies
in the reference centralizer, that lift centralizes the integral cubic too.
These facts retain the concrete lattice maps. They do not identify the class
with the source root class in a Suzuki quotient.

The two propositions at the end isolate involution conjugacy and the incidence
problem for ambient transports fixing the marked involution. Their conjunction is
used in `Orbit`; neither geometric proposition is asserted here.

Source: Aschbacher, *Sporadic Groups* (1994), 48.3 and the root conventions
(pp.268–269), 49.1–49.2 (p.280), and 49.5 (pp.283–284).
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion

/-- The same literal cubic as `RootModel.referenceCubic`, before dividing by signs. -/
def orbitIntegralCubic : LeechIsometryGroup :=
  icosianHermitianToCo0 RootModel.referenceLift

theorem orbitIntegralCubic_projection :
    leechCentralProjection orbitIntegralCubic = RootModel.referenceCubic := rfl

theorem orbitIntegralCubic_cube : orbitIntegralCubic ^ 3 = 1 := by
  rw [orbitIntegralCubic, ← map_pow, RootModel.referenceLift_cube, map_one]

/-- A cubic lift cannot acquire a central minus sign under conjugation. -/
theorem commute_cubic_lift {r s : LeechIsometryGroup} (hr : r ^ 3 = 1)
    (hc : Commute (leechCentralProjection s) (leechCentralProjection r)) :
    Commute s r := by
  have hk : MulAut.conj s r * r⁻¹ ∈ leechCentralSigns := by
    rw [← leechCentralProjection_kernel, MonoidHom.mem_ker]
    simp only [MulAut.conj_apply, map_mul, map_inv, hc.eq,
      mul_inv_cancel_right, mul_inv_cancel]
  rcases (leechCentralSigns_mem _).mp hk with h | h
  · have he : MulAut.conj s r = r := mul_inv_eq_one.mp h
    exact mul_inv_eq_iff_eq_mul.mp he
  · have he : MulAut.conj s r = negationIsometry * r :=
      mul_inv_eq_iff_eq_mul.mp h
    have hz : Commute negationIsometry r :=
      (Subgroup.mem_center_iff.mp negation_mem_center r).symm
    have hn3 : negationIsometry ^ 3 = negationIsometry := by
      rw [pow_succ, pow_two, negationIsometry_sq, one_mul]
    have hp := congrArg (fun x : LeechIsometryGroup => x ^ 3) he
    rw [← map_pow, hr, map_one, hz.mul_pow, hr, mul_one, hn3] at hp
    exact (negationIsometry_ne_one hp.symm).elim

/-- Membership is pointwise centralization of the cyclic group, hence of its generator. -/
theorem mem_referenceCubicCentralizer_iff (s : LeechCentralQuotient) :
    s ∈ referenceCubicCentralizer ↔ Commute s RootModel.referenceCubic := by
  constructor
  · intro hs
    exact (hs _ (Subgroup.mem_zpowers _)).symm
  · intro hs p hp
    obtain ⟨n, rfl⟩ := hp
    exact (hs.zpow_right n).symm

/-- The full integral centralizer of the retained cubic. -/
def orbitIntegralCentralizer : Subgroup LeechIsometryGroup :=
  Subgroup.centralizer ({orbitIntegralCubic} : Set LeechIsometryGroup)

/-- Exact comparison of full centralizers across the actual sign quotient. -/
theorem orbitIntegralCentralizer_eq_comap :
    orbitIntegralCentralizer = referenceCubicCentralizer.comap leechCentralProjection := by
  ext s
  change s ∈ Subgroup.centralizer ({orbitIntegralCubic} : Set LeechIsometryGroup) ↔
    leechCentralProjection s ∈ referenceCubicCentralizer
  rw [Subgroup.mem_centralizer_singleton_iff, mem_referenceCubicCentralizer_iff,
    ← orbitIntegralCubic_projection]
  exact ⟨fun hs => (show Commute s orbitIntegralCubic from hs).map leechCentralProjection,
    commute_cubic_lift orbitIntegralCubic_cube⟩

/-- Restriction of the literal Conway quotient map to the full integral centralizer. -/
def orbitCentralizerProjection : orbitIntegralCentralizer →* referenceCubicCentralizer :=
  (leechCentralProjection.comp orbitIntegralCentralizer.subtype).codRestrict _ (by
    intro s
    exact (show s.val ∈ referenceCubicCentralizer.comap leechCentralProjection from
      orbitIntegralCentralizer_eq_comap ▸ s.property))

theorem orbitCentralizerProjection_surjective : Function.Surjective orbitCentralizerProjection := by
  intro x
  obtain ⟨s, hs⟩ := leechCentralProjection_surjective x.val
  have hm : s ∈ orbitIntegralCentralizer := by
    rw [orbitIntegralCentralizer_eq_comap]
    change leechCentralProjection s ∈ referenceCubicCentralizer
    rw [hs]
    exact x.property
  exact ⟨⟨s, hm⟩, Subtype.ext hs⟩

theorem orbitCentralizerProjection_kernel :
    orbitCentralizerProjection.ker = leechCentralSigns.comap orbitIntegralCentralizer.subtype := by
  ext s
  change (orbitCentralizerProjection s = 1) ↔ s.val ∈ leechCentralSigns
  constructor
  · intro hs
    exact (QuotientGroup.eq_one_iff s.val).mp (congrArg Subtype.val hs)
  · intro hs
    exact Subtype.ext ((QuotientGroup.eq_one_iff s.val).mpr hs)

/-- Quotient only by the two central signs, keeping the full reference centralizer. -/
def orbitCentralizerQuotientEquiv :
    orbitIntegralCentralizer ⧸ leechCentralSigns.comap orbitIntegralCentralizer.subtype ≃*
      referenceCubicCentralizer :=
  (QuotientGroup.quotientMulEquivOfEq orbitCentralizerProjection_kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective orbitCentralizerProjection
      orbitCentralizerProjection_surjective)

/-- The centralizer equivalence agrees with the original ambient quotient map. -/
theorem orbitCentralizerQuotientEquiv_mk (s : orbitIntegralCentralizer) :
    (orbitCentralizerQuotientEquiv (QuotientGroup.mk s)).val =
      leechCentralProjection s.val := rfl

/-- A concrete double transposition on the four specified scalar points. -/
def orbitPair : alternatingGroup fourPoints :=
  ⟨Equiv.swap ⟨0, by decide⟩ ⟨1, by decide⟩ *
    Equiv.swap ⟨2, by decide⟩ ⟨3, by decide⟩, by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide⟩

theorem orbitPair_mem : orbitPair ∈ alternatingGroup.kleinFour fourPoints := by
  apply Subgroup.subset_closure
  decide +kernel

/-- The involution used to mark the tetrahedron, in the actual Leech quotient. -/
def orbitInvolution : LeechCentralQuotient := scalarFour orbitPair

theorem orbitInvolution_mem_U : orbitInvolution ∈ U := ⟨orbitPair, orbitPair_mem, rfl⟩

theorem orbitInvolution_mem_I : orbitInvolution ∈ I := U_le_I orbitInvolution_mem_U

theorem orbitInvolution_ne_one : orbitInvolution ≠ 1 := by
  intro h
  have he : orbitPair = 1 := scalarFour_injective (h.trans scalarFour.map_one.symm)
  exact (by decide +kernel : orbitPair ≠ 1) he

theorem orbitInvolution_order : orderOf orbitInvolution = 2 := by
  rw [orbitInvolution, orderOf_injective scalarFour scalarFour_injective]
  exact orderOf_eq_prime (by decide +kernel : orbitPair ^ 2 = 1)
    (by decide +kernel : orbitPair ≠ 1)

theorem orbitInvolution_mem_centralizer : orbitInvolution ∈ referenceCubicCentralizer := by
  rw [mem_referenceCubicCentralizer_iff]
  exact RootModel.referenceCubic_mem orbitInvolution orbitInvolution_mem_I

/-- Every ambient transport has an actual lift squaring to central negation. -/
theorem orbitInvolution_conj_lift (g : LeechCentralQuotient) :
    ∃ s : LeechIsometryGroup,
      leechCentralProjection s = MulAut.conj g orbitInvolution ∧
      s ^ 2 = negationIsometry := by
  obtain ⟨s, hs, hs2⟩ := U_involution_lift
    ⟨orbitInvolution, orbitInvolution_mem_U⟩ orbitInvolution_ne_one
  obtain ⟨k, hk⟩ := leechCentralProjection_surjective g
  refine ⟨MulAut.conj k s, ?_, ?_⟩
  · simp [MulAut.conj_apply, hk, hs]
  · rw [← map_pow, hs2]
    have hc := Subgroup.mem_center_iff.mp negation_mem_center k
    change k * negationIsometry * k⁻¹ = negationIsometry
    rw [hc, mul_inv_cancel_right]

/-- For a transport in the reference centralizer its lift lies in the full
integral centralizer. This is stronger than projective commutation alone. -/
theorem orbitInvolution_conj_integral_lift (g : LeechCentralQuotient)
    (hg : MulAut.conj g orbitInvolution ∈ referenceCubicCentralizer) :
    ∃ s : orbitIntegralCentralizer,
      (orbitCentralizerProjection s).val = MulAut.conj g orbitInvolution ∧
      (s.val : LeechIsometryGroup) ^ 2 = negationIsometry := by
  obtain ⟨s, hs, hs2⟩ := orbitInvolution_conj_lift g
  have hm : s ∈ orbitIntegralCentralizer := by
    rw [orbitIntegralCentralizer_eq_comap]
    change leechCentralProjection s ∈ referenceCubicCentralizer
    rwa [hs]
  exact ⟨⟨s, hm⟩, hs, hs2⟩

/-- The single ambient involution class required inside the fixed cubic centralizer.
This remains a geometric obligation, not a consequence of an abstract A₄ type. -/
def ReferenceInvolutionOrbit : Prop :=
  ∀ g : LeechCentralQuotient,
    MulAut.conj g orbitInvolution ∈ referenceCubicCentralizer →
    ∃ c ∈ referenceCubicCentralizer,
      MulAut.conj c (MulAut.conj g orbitInvolution) = orbitInvolution

/-- The remaining incidence orbit, with the involution already fixed. The actor
must centralize both the reference cubic and the marked involution. -/
def ReferenceTetrahedralIncidence : Prop :=
  ∀ g : LeechCentralQuotient,
    Subgroup.zpowers RootModel.referenceCubic ≤ Subgroup.centralizer
      (I.map (MulAut.conj g).toMonoidHom : Set LeechCentralQuotient) →
    MulAut.conj g orbitInvolution = orbitInvolution →
    ∃ c ∈ referenceCubicCentralizer, Commute c orbitInvolution ∧
      (I.map (MulAut.conj g).toMonoidHom).map (MulAut.conj c).toMonoidHom = I

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
