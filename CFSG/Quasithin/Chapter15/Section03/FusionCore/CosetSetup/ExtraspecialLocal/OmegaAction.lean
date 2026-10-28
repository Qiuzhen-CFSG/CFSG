module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.OmegaAction.Planes
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.OmegaAction.CenterKernel
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.OmegaAction.QuotientAction

/-!
# The extraspecial quotient-centralizer calculation in 15.3.49

The genuine extraspecial inputs give [O₂(H),Y₀] ≤ O₂(Y₀), while the
specified Sylow subgroup contains O₂(H). Therefore the two-core lies in
the actual quotient centralizer. Mapping its involutions through the
natural action gives the first inequality in the calculation after
15.3.49(b). The inclusion-induced equivalence Y₀/O₂(Y₀) ≃ Z(Y/O₂(Y))
identifies the image of that quotient centralizer with the center-fixing
subgroup of the faithful action of the actual Sylow image on Y/O₂(Y).
The imported center-kernel calculation gives its omega subgroup as Z(T̄).
Finally this center preserves each definite plane, proving Ω₁(O₂(H)) ≤ S.

The final theorem retains the source identities Y = residualY M Mc,
V = localModule T M, and Mc = C_G(Ω₁(Z(T))). Every action witness is
constructed from the stated earlier-source inputs; no action calculation
or property of either conjugate span is assumed. The quotient centralizer
uses relative normality in Y₀T, and the bar covers the entire centralizer
before omega is taken.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
the calculation following 15.3.49(b), printed p.1143.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

open Subgroup Stellmacher

variable {G : Type*} [Group G] [Finite G]

/-- The actual local two-core lies in the actual quotient centralizer. -/
theorem extraspecial_local_core_le_quotientCentralizer
    (M Mc H Y V : Subgroup G) (T : Sylow 2 G)
    (hYM : Y ≤ M) (h : ExtraspecialCase M Y V)
    (hM : M ≤ normalizer (V : Set G))
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H)
    (hH : H ≤ Mc) (hCH : Y ⊓ centralizer (V : Set G) ≤ H)
    (hfactor : ∀ x ∈ M ⊓ Mc,
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x) :
    let Y₀ := twoResidualAmbient (Y ⊓ centralizer (V : Set G))
    H.pCoreIn 2 ≤ commutatorPreimage (T : Subgroup G) Y₀ (Y₀.pCoreIn 2) := by
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    rintro x ⟨x, hx, rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype hTH) hx
  exact le_commutatorPreimage hQT
    (extraspecial_local_algebra M Mc H Y V T hYM h hM hTM hTH hH hCH hfactor).2.2.2.2.2

omit [Finite G] in
/-- Images of involutions belong to the first omega subgroup of the image.
This only asserts the valid inclusion; involutions need not lift. -/
theorem orthogonal_omega_image_le {M V Q C : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hQM : Q ≤ M) (hQC : Q ≤ C) :
    d.image (omegaOneAmbient Q) ≤ omegaOneAmbient (d.image C) := by
  have hpre : omegaOneAmbient Q ≤
      ((omegaOneAmbient (d.image C)).comap d.actor).map M.subtype := by
    apply (omegaOneAmbient_le_iff _ _).mpr
    intro x hx hpow
    let m : M := ⟨x, hQM hx⟩
    refine ⟨m, ?_, rfl⟩
    apply (omegaOneAmbient_le_iff (d.image C) _).mp le_rfl (d.actor m)
    · exact ⟨m, hQC hx, rfl⟩
    · rw [← map_pow, show m ^ 2 = 1 from Subtype.ext hpow, map_one]
  rintro z ⟨m, hm, rfl⟩
  obtain ⟨n, hn, hnm⟩ := hpre hm
  have he : n = m := Subtype.ext hnm
  exact he ▸ hn

/-- The first inequality in the printed barred calculation follows from
the earlier-source inputs and the actual action map. -/
theorem extraspecial_local_omega_image_le
    (M Mc H Y V : Subgroup G) (T : Sylow 2 G)
    (d : NaturalOrthogonalAction M V)
    (hYM : Y ≤ M) (h : ExtraspecialCase M Y V)
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H)
    (hH : H ≤ Mc) (hCH : Y ⊓ centralizer (V : Set G) ≤ H)
    (hfactor : ∀ x ∈ M ⊓ Mc,
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x) :
    let Y₀ := twoResidualAmbient (Y ⊓ centralizer (V : Set G))
    d.image (omegaOneAmbient (H.pCoreIn 2)) ≤
      omegaOneAmbient (d.image (commutatorPreimage (T : Subgroup G) Y₀ (Y₀.pCoreIn 2))) := by
  have hc := extraspecial_local_core_le_quotientCentralizer M Mc H Y V T hYM h
    d.normalizes hTM hTH hH hCH hfactor
  exact orthogonal_omega_image_le d
    ((hc.trans (commutatorPreimage_le _ _ _)).trans hTM) hc

/-- The omega subgroup of the image of the actual quotient centralizer is
the center of the specified orthogonal Sylow image, embedded in the actor. -/
theorem extraspecial_local_quotientCentralizer_omega
    (M Mc H Y V : Subgroup G) (T : Sylow 2 G)
    (d : NaturalOrthogonalAction M V) (h : ExtraspecialCase M Y V)
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H)
    (hH : H ≤ Mc) (hCH : Y ⊓ centralizer (V : Set G) ≤ H)
    (hfactor : ∀ x ∈ M ⊓ Mc,
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x)
    (hcore : (Y ⊔ (T : Subgroup G)).pCoreIn 2 =
      (T : Subgroup G) ⊓ centralizer (V : Set G))
    (himage : d.image Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    let Y₀ := twoResidualAmbient (Y ⊓ centralizer (V : Set G))
    omegaOneAmbient (d.image (commutatorPreimage (T : Subgroup G) Y₀ (Y₀.pCoreIn 2))) =
      (center (d.image (T : Subgroup G))).map (d.image (T : Subgroup G)).subtype := by
  dsimp only
  let _ := h.extraspecial
  obtain ⟨_, ρ, _, hinj, _, hC⟩ :=
    extraspecial_quotient_action M Mc H Y V T d h hTM hTH hH hCH hfactor hcore himage
  rw [hC]
  exact orthogonal_sylow_centerFixingImage_omega
    (orthogonalSylowImage d T hTM) h.quotient_card ρ hinj

/-- The omega subgroup of the local two-core stabilizes each definite plane.
The quotient action and its faithfulness are constructed from the earlier inputs. -/
theorem extraspecial_local_omega_le_planeStabilizer
    (M Mc H Y V : Subgroup G) (T : Sylow 2 G)
    (d : NaturalOrthogonalAction M V) (h : ExtraspecialCase M Y V)
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H)
    (hH : H ≤ Mc) (hCH : Y ⊓ centralizer (V : Set G) ≤ H)
    (hfactor : ∀ x ∈ M ⊓ Mc,
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x)
    (hcore : (Y ⊔ (T : Subgroup G)).pCoreIn 2 =
      (T : Subgroup G) ⊓ centralizer (V : Set G))
    (himage : d.image Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (i : OrthogonalPlaneIndex) :
    omegaOneAmbient (H.pCoreIn 2) ≤ planeStabilizer T (d.plane i) := by
  have hYM : Y ≤ M := by rw [h.theta_eq]; exact theta_le M
  have hc := extraspecial_local_core_le_quotientCentralizer M Mc H Y V T hYM h
    d.normalizes hTM hTH hH hCH hfactor
  apply le_planeStabilizer_of_image_le_center d T hTM
    ((omegaOneAmbient_le _).trans (hc.trans (commutatorPreimage_le _ _ _)))
  exact (extraspecial_local_omega_image_le M Mc H Y V T d hYM h
    hTM hTH hH hCH hfactor).trans_eq
    (extraspecial_local_quotientCentralizer_omega M Mc H Y V T d h
      hTM hTH hH hCH hfactor hcore himage)

/-- The calculation following 15.3.49(b), with the source definitions of
Y, V and M_c retained. This assembles normalization of the relative quotient
centralizer, its barred omega equality, and the local bound Ω₁(O₂(H)) ≤ S.
The only extra inputs are the displayed earlier conclusions of 15.3.7. -/
theorem extraspecial_local_omega_calculation
    (M Mc H Y V : Subgroup G) (T : Sylow 2 G)
    (d : NaturalOrthogonalAction M V)
    (hY : Y = residualY M Mc) (hV : V = localModule T M)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (h : ExtraspecialCase M Y V)
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H)
    (hH : H ≤ Mc) (hCH : Y ⊓ centralizer (V : Set G) ≤ H)
    (hfactor : ∀ x ∈ M ⊓ Mc,
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x)
    (hcore : (Y ⊔ (T : Subgroup G)).pCoreIn 2 =
      (T : Subgroup G) ⊓ centralizer (V : Set G))
    (himage : d.image Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    let Y₀ := twoResidualAmbient (Y ⊓ centralizer (V : Set G))
    let C := commutatorPreimage (T : Subgroup G) Y₀ (Y₀.pCoreIn 2)
    (T : Subgroup G) ≤ normalizer (Y₀ : Set G) ∧
      Y₀ ⊔ (T : Subgroup G) ≤ normalizer (Y₀.pCoreIn 2 : Set G) ∧
      (T : Subgroup G) ≤ normalizer (C : Set G) ∧
      omegaOneAmbient (d.image C) =
        (center (d.image (T : Subgroup G))).map (d.image (T : Subgroup G)).subtype ∧
      ∀ i : OrthogonalPlaneIndex,
        omegaOneAmbient (H.pCoreIn 2) ≤ planeStabilizer T (d.plane i) := by
  have hYM : Y ≤ M := by rw [h.theta_eq]; exact theta_le M
  subst Y V Mc
  obtain ⟨hn, hcoreN, hCN⟩ := extraspecial_local_normalization _ _ _ _ _ T hYM h
    d.normalizes hTM hTH hH hCH hfactor
  exact ⟨hn, hcoreN, hCN,
    extraspecial_local_quotientCentralizer_omega _ _ _ _ _ T d h
      hTM hTH hH hCH hfactor hcore himage,
    extraspecial_local_omega_le_planeStabilizer _ _ _ _ _ T d h
      hTM hTH hH hCH hfactor hcore himage⟩


end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

end
