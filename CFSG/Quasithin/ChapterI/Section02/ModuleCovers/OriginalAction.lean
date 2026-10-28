module

public import Theory.Representation.CentralCoverOriginalAction.Descent
public import CFSG.Quasithin.ChapterI.Section02.ModuleCovers
public import Theory.Representation.SL2NaturalOffenders.Semilinear

/-!
# I.2.3 for the original ambient action

The inputs are the actual universal L-cover, its orthogonal geometry, and the
marked natural L-action. We construct its original G-action, prove preservation
of the singular section, and descend fixed points and normalizer centrality to
the given central G-cover. No dimension assertion about the universal G-cover
is used. The SL₂ second preimage is handled separately because it is not isotropic.

The three orthogonal family producers supply the displayed L-geometry and
the point/plane stabilizer irreducibility. The source assembly discharges these
inputs for the original field and model. Reference: Aschbacher--Smith I.2.3,
printed p.413, and Remark I.1.5, p.408.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterI.ModuleCovers.OriginalAction

open Representation Representation.OneCohomology
open Representation.OneCohomology.CentralCoverOriginalAction
open Representation.BinaryOffender Module

variable {G N W : Type*} [Group G]
  [AddCommGroup N] [Module (ZMod 2) N]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The actual stabilizer of a covering preimage is the stabilizer of its
original natural image, with equality inside the original ambient group. -/
theorem preimage_stabilizer_eq
    {η : Representation (ZMod 2) G N} {τ : Representation (ZMod 2) G W}
    (q : τ.IntertwiningMap η) (hq : Function.Surjective q)
    (A : Submodule (ZMod 2) N) :
    subspaceStabilizer τ (A.comap q.toLinearMap) = subspaceStabilizer η A := by
  ext g
  constructor
  · intro hg v
    obtain ⟨w, rfl⟩ := hq v
    have he := hg w
    change q (τ g w) ∈ A ↔ q w ∈ A at he
    simpa only [q.isIntertwining] using he
  · intro hg w
    change q (τ g w) ∈ A ↔ q w ∈ A
    rw [q.isIntertwining]
    exact hg (q w)

section Orthogonal
variable {F U : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Module F N] [IsScalarTower (ZMod 2) F N] [Nontrivial N]
  [FiniteDimensional F N] [FiniteDimensional (ZMod 2) N]
  [AddCommGroup U] [Module F U] [Module (ZMod 2) U]
  [IsScalarTower (ZMod 2) F U] [FiniteDimensional (ZMod 2) U]
  [FiniteDimensional (ZMod 2) W] [Finite G]

/-- Clauses I.2.3(2) for any marked isotropic source line or plane. The
original actors, original covering projection and original Sylow are retained.
Every compatibility of the lifted action is proved inside this theorem. -/
theorem fixed_point_and_normalizer_centrality
    (H : Subgroup G) [H.Normal]
    (η : Representation (ZMod 2) G N)
    (ρ : Representation F H N) (σ : Representation F H U)
    (hρ : ∀ h : H, ∀ v, η h v = ρ h v)
    (p : σ.IntertwiningMap ρ)
    (hp : IsCover (restrictCoverMap (k := ZMod 2) p))
    (hd : finrank (ZMod 2) (p.toLinearMap.restrictScalars (ZMod 2)).ker =
      finrank (ZMod 2) (H1 (restrictScalars (k := ZMod 2) ρ).dual))
    (hscalar : HasScalarCommutant ρ)
    (B : LinearMap.BilinForm F N) (hB : B.Nondegenerate)
    (hBinv : ∀ h v w, B (ρ h v) (ρ h w) = B v w)
    (Q : QuadraticForm F U) (hQ : ∀ h u, Q (σ h u) = Q u)
    (hpolar : ∀ u v, Q.polarBilin u v = B (p u) (p v))
    (r : U) (hr : p r = 0) (hQr : Q r ≠ 0)
    (haniso : ∀ u, p u = 0 → Q u = 0 → u = 0)
    (hfixed : fixed (restrictScalars (k := ZMod 2) ρ) = ⊥)
    (τ : Representation (ZMod 2) G W) (q : τ.IntertwiningMap η) (hq : IsCover q)
    (A : Submodule F N) (hA : A ≠ ⊥)
    (hisotropic : ∀ v ∈ A, ∀ w ∈ A, B v w = 0)
    (T : Sylow 2 G)
    (hT : T.toSubgroup ≤ subspaceStabilizer η (A.restrictScalars (ZMod 2)))
    [IsIrreducible (stabilizerRepresentation η (A.restrictScalars (ZMod 2)))] :
    (∃ w : W, q w ∈ A ∧ w ∉ fixed (τ.comp H.subtype) ∧
      ∀ t : T, τ t w = w) ∧
    (∀ g : pCore 2 (subspaceStabilizer η (A.restrictScalars (ZMod 2))),
      ∀ w : W, q w ∈ A → τ g.val.val w = w) ∧
    subspaceStabilizer τ ((A.restrictScalars (ZMod 2)).comap q.toLinearMap) =
      subspaceStabilizer η (A.restrictScalars (ZMod 2)) := by
  obtain ⟨ζ, hζ, hquot, hsing⟩ := exists_original_action_preserving_singular
    H η ρ σ hρ p hp hd hscalar B hB hBinv Q hQ hpolar
  have hρeq : η.comp H.subtype = restrictScalars (k := ZMod 2) ρ := by
    apply MonoidHom.ext
    intro h
    exact LinearMap.ext (hρ h)
  have hζeq : ζ.comp H.subtype = restrictScalars (k := ZMod 2) σ := by
    apply MonoidHom.ext
    intro h
    exact LinearMap.ext (hζ h)
  let p' : Representation.IntertwiningMap (ζ.comp H.subtype) (η.comp H.subtype) :=
    (p.toLinearMap.restrictScalars (ZMod 2)).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro h u
      exact hquot h u)
  have hp' : IsCover p' := by
    change Function.Surjective p ∧ _ ∧ _
    refine ⟨hp.1, ?_, ?_⟩
    · intro u hu h
      change ζ h u = u
      rw [hζ]
      exact hp.2.1 hu h
    · rw [hζeq]
      exact hp.2.2
  have hd' : finrank (ZMod 2) p'.toLinearMap.ker =
      finrank (ZMod 2) (H1 (Representation.dual (η.comp H.subtype))) := by
    change finrank (ZMod 2) (p.toLinearMap.restrictScalars (ZMod 2)).ker = _
    exact hd.trans (congrArg (fun δ : Representation (ZMod 2) H N =>
      finrank (ZMod 2) (H1 δ.dual)) hρeq).symm
  have hN : Coinvariants.ker (η.comp H.subtype) = ⊤ := by
    rw [← map_coinvariants_of_surjective p' hp'.1, hp'.2.2,
      Submodule.map_top, LinearMap.range_eq_top.mpr hp'.1]
  have hqH := restrict_isCover H q hq hN
  obtain ⟨f, _, hover⟩ := exists_quotient_of_finrank_ker_eq p' hp' hd'
    (restrictProjection H q) hqH
  have hf : ∀ g u, f (ζ g u) = τ g (f u) :=
    quotient_original_equivariant H p'.toLinearMap q.toLinearMap f.toLinearMap
      hquot (fun g w => LinearMap.congr_fun (q.isIntertwining' g) w)
      (fun w hw h => hq.2.1 hw h) hp'.2.2
      (fun h u => LinearMap.congr_fun (f.isIntertwining' h) u) hover
  have hzero : ∀ u v, p u ∈ A → p v ∈ A → Q.polarBilin u v = 0 := by
    intro u v hu hv
    rw [hpolar]
    exact hisotropic (p u) hu (p v) hv
  let D := singularPreimage p.toLinearMap Q A hzero
  let D₂ := D.restrictScalars (ZMod 2)
  let A₂ := A.restrictScalars (ZMod 2)
  have hDmap : ∀ u ∈ D₂, p u ∈ A₂ := fun _ hu => hu.1
  have hDinj : ∀ u ∈ D₂, p u = 0 → u = 0 := fun u hu hz => haniso u hz hu.2
  have hDsurj : ∀ v ∈ A₂, ∃ u ∈ D₂, p u = v := by
    intro v hv
    obtain ⟨u, hu⟩ := singularPreimage_surjective p.toLinearMap hp.1 Q A hzero r hr hQr ⟨v, hv⟩
    exact ⟨u, u.property, hu⟩
  have hDne : D₂ ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
    obtain ⟨u, hu, hpu⟩ := hDsurj v hv
    intro hbot
    have hu0 : u = 0 := by simpa [hbot] using hu
    exact hv0 (hpu.symm.trans (hu0 ▸ map_zero p))
  have hstable (g : G) (hg : g ∈ subspaceStabilizer η A₂) :
      ∀ u ∈ D₂, ζ g u ∈ D₂ := by
    exact singularPreimage_stable p.toLinearMap Q A hzero (actorEquiv η g)
      (actorEquiv ζ g) (hquot g) (fun v hv => (hg v).mpr hv) (hsing g)
  refine ⟨?_, ?_, preimage_stabilizer_eq q hq.1 A₂⟩
  · obtain ⟨w, hw, hw0, htw⟩ := exists_fixed_above ζ τ p'.toLinearMap q.toLinearMap
      f.toLinearMap hf hover D₂ A₂ hDmap hDne hDinj T.toSubgroup T.isPGroup'
      (fun t => hstable t (hT t.property))
    refine ⟨w, hw, ?_, htw⟩
    intro hfix
    have hn : q w ∈ fixed (restrictScalars (k := ZMod 2) ρ) := by
      intro h
      change ρ h (q w) = q w
      calc
        _ = η h (q w) := (hρ h (q w)).symm
        _ = q (τ h w) := (LinearMap.congr_fun (q.isIntertwining' h) w).symm
        _ = q w := congrArg q (hfix h)
    exact hw0 (by simpa [hfixed] using hn)
  · let K := subspaceStabilizer η A₂
    have hcore : pCore 2 K ≤ (stabilizerRepresentation η A₂).ker :=
      normal_p_subgroup_le_ker (stabilizerRepresentation η A₂) (pCore 2 K) pCore_isPGroup
    intro g
    apply fixed_preimage_of_stable_section η ζ τ p'.toLinearMap q.toLinearMap
      f.toLinearMap hquot hf hover hq.2.1 D₂ A₂ hDmap hDinj hDsurj g.val.val
      (hstable g.val.val g.val.property)
    intro v hv
    have hg := LinearMap.congr_fun (hcore g.property) (⟨v, hv⟩ : A₂)
    exact congrArg Subtype.val hg

end Orthogonal

/-- The separate SL₂ i=2 mechanism: the second preimage is the whole cover,
and the normal two-core is trivial on its irreducible natural quotient. -/
theorem whole_preimage_twoCore_fixed [Finite G] [FiniteDimensional (ZMod 2) N]
    (H : Subgroup G) [H.Normal]
    (η : Representation (ZMod 2) G N) [IsIrreducible η]
    (τ : Representation (ZMod 2) G W) (q : τ.IntertwiningMap η) (hq : IsCover q)
    (hN : Coinvariants.ker (η.comp H.subtype) = ⊤)
    (hfaith : Function.Injective (η.comp H.subtype)) :
    ∀ g : pCore 2 G, ∀ w, τ g w = w := by
  have hcore : pCore 2 G ≤ η.ker := normal_p_subgroup_le_ker η (pCore 2 G) pCore_isPGroup
  intro g
  apply fixed_cover_of_fixed_quotient H η τ q hq (restrict_full H q hq hN) hfaith g
  intro v
  exact LinearMap.congr_fun (hcore g.property) v

section LinearTwoFour
open Representation.SL2FourNatural Representation.SL2FourCentralCover

private theorem four_kernel_dimension :
    finrank (ZMod 2) projection.toLinearMap.ker =
      finrank (ZMod 2) (H1 naturalRepresentation.dual) := by
  have h := projection.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr projection_isCover.1, finrank_top,
    finrank_vector, binary_finrank] at h
  rw [natural_dual_H1_finrank]
  omega

/-- Every original normalizing actor on the natural SL₂(4) quotient lifts to
its actual six-dimensional universal L-cover. Its central F₄-line is allowed
to move. The original quotient evaluation is preserved. -/
theorem linearTwoFour_original_lift
    (a : G →* MulAut SL) (η : Representation (ZMod 2) G V)
    (ha : ∀ g l v, η g (naturalRepresentation l v) =
      naturalRepresentation (a g l) (η g v)) :
    ∃ ζ : Representation (ZMod 2) G Space,
      (∀ g l u, ζ g (binaryAction l u) = binaryAction (a g l) (ζ g u)) ∧
      (∀ g u, projection (ζ g u) = η g (projection u)) := by
  obtain ⟨ζ, hζ, hp, _⟩ := exists_action projection projection_isCover
    four_kernel_dimension a η ha
  exact ⟨ζ, hζ, hp⟩

/-- I.2.3(3) on the ORIGINAL central G-cover when the normal layer is the
marked SL₂(4). The root acts through the literal embedding H→G and the
original model equivalence, without a universal ambient-cover dimension claim. -/
theorem linearTwoFour_original_cover_root_geometry
    [FiniteDimensional (ZMod 2) W]
    (H : Subgroup G) [H.Normal] (e : H ≃* SL)
    (η : Representation (ZMod 2) G V)
    (hη : ∀ h : H, ∀ v, η h v = naturalRepresentation (e h) v)
    (τ : Representation (ZMod 2) G W) (q : τ.IntertwiningMap η) (hq : IsCover q) :
    fixed (τ.comp H.subtype) ≤ LinearTwoFour.firstLine.comap q.toLinearMap ∧
      LinearTwoFour.firstLine.comap q.toLinearMap =
        Coinvariants.ker (τ.comp
          ((H.subtype.comp e.symm.toMonoidHom).comp
            (Matrix.SpecialLinearGroup.upperUnipotent F).subtype)) ∧
      LinearTwoFour.firstLine.comap q.toLinearMap ≤
        fixed (τ.comp ((H.subtype.comp e.symm.toMonoidHom).comp
          (Matrix.SpecialLinearGroup.upperUnipotent F).subtype)) := by
  have hηeq : η.comp H.subtype = naturalRepresentation.comp e.toMonoidHom := by
    apply MonoidHom.ext
    intro h
    exact LinearMap.ext (hη h)
  have hN : Coinvariants.ker (η.comp H.subtype) = ⊤ := by
    rw [hηeq, commutator_comp_equiv]
    rw [← map_coinvariants_of_surjective projection projection_isCover.1,
      projection_isCover.2.2, Submodule.map_top,
      LinearMap.range_eq_top.mpr projection_isCover.1]
  let φ := H.subtype.comp e.symm.toMonoidHom
  let q₀ : Representation.IntertwiningMap (τ.comp φ) naturalRepresentation :=
    q.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ (by
      intro l w
      change q (τ (e.symm l : H) w) = naturalRepresentation l (q w)
      rw [q.isIntertwining, hη, e.apply_symm_apply])
  have hfull : Coinvariants.ker (τ.comp φ) = ⊤ := by
    change Coinvariants.ker ((τ.comp H.subtype).comp e.symm.toMonoidHom) = ⊤
    rw [commutator_comp_equiv]
    exact restrict_full H q hq hN
  have hq₀ : IsCover q₀ :=
    ⟨hq.1, fun w hw l => hq.2.1 hw _, hfull⟩
  obtain ⟨hfix, hroot, hcentral⟩ := LinearTwoFour.cover_root_geometry q₀ hq₀
  have hfixed : fixed (τ.comp φ) = fixed (τ.comp H.subtype) :=
    fixed_comp_equiv (τ.comp H.subtype) e.symm
  rw [hfixed] at hfix
  exact ⟨hfix, hroot, hcentral⟩

end LinearTwoFour

end CFSG.Quasithin.ChapterI.ModuleCovers.OriginalAction
