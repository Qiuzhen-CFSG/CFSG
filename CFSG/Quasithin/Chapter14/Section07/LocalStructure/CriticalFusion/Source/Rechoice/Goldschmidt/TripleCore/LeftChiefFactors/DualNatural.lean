module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.CriticalIntersections.DualSection

/-!
# The natural contribution inside the original dual section

The source duality pairs U/C_U(Q_H) with Q_H/C_{Q_H}(U). The existing
central-cover argument puts C_U(Q_H) inside U₀, using the nontrivial
commutator identity [U,Q_H]=V₁. Thus the original natural projection factors
through the former quotient. Dualizing this actual surjection and composing
with the original pairing embeds the dual natural module into the latter.
The representative formula retains the original H-action and pairing.
The centralizer denominator is identified with C_H(U), and the actual
source subgroup chain is placed inside L₁T. No equality C_U(Q_H)=V₁,
module dimension count, or chief count is assumed.

SectionCentralizer is the earlier 14.5.15(4) input (qt-14-05); SourceDuality
and the commutator identity are 14.5.21(1–2) (qt-14-05-terminal-duality).
Their source discharge remains with the 14.7 assembly owner. The local
Borel restriction and the actual chief-series accounting are still needed.

This extension imports the original duality branch directly. Both this branch
and TripleCore use the common Source.FixedCoordinates API, so their original
section coordinates agree when the branches are imported together.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.5.21(1–2), printed pp.1019–1020, and 14.7.70, printed p.1074.
-/

@[expose] public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
  {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- The denominator in the source Q_H-section is exactly C_H(U).
The earlier section-kernel identity puts even C_G(U) inside Q_H. -/
theorem q_centralizer_eq_h_centralizer (hc : d.SectionCentralizer) :
    F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G) =
      F.H ⊓ centralizer (F.U : Set G) := by
  have h := CriticalIntersections.centralizer_U_le_core d hc
  rw [inf_eq_right.mpr h, inf_eq_right.mpr (h.trans (pCoreIn_le 2 F.H))]

/-- The actual source sections lie in the left vertex in the indicated order.
No containment of all of U in the smaller two-residual L₁ is asserted. -/
theorem source_filtration_containments (hc : d.SectionCentralizer) :
    F.Vi 1 ≤ F.U ∧
      F.U ≤ F.H ⊓ centralizer (F.U : Set G) ∧
      F.H ⊓ centralizer (F.U : Set G) ≤ F.H.pCoreIn 2 ∧
      F.H.pCoreIn 2 ≤ F.Li L 1 ⊔ (T : Subgroup G) := by
  let := d.abelian
  have hC := CriticalIntersections.centralizer_U_le_core d hc
  have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
      (map_subgroupOf_eq_of_le (F.invariant 1))
  exact ⟨d.conjugationSection.kernel_le,
    le_inf d.conjugationSection.section_le (le_centralizer _),
    inf_le_right.trans hC, hQT.trans le_sup_right⟩

/-- The source centralizer is contained in U₀; no equality with V₁ is used. -/
theorem u_centralizer_le_U₀ (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G) ≤ d.U₀ := by
  intro v hv
  apply (d.mem_U₀ ⟨v, hv.1⟩).mpr
  apply CriticalIntersections.DualSection.centralizer_image_le_projection_ker d hc s hcomm
  exact (d.conjugationSection.mem_imageSpace_iff _ _).mpr ⟨⟨v, hv.1⟩, hv, rfl⟩

/-- The original natural quotient descends through the actual U-centralizer
section, retaining its original H-action and its formula on representatives. -/
theorem exists_natural_projection (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    ∃ p : s.uAction.IntertwiningMap (d.naturalQuotient.action.comp d.qH),
      Function.Surjective p ∧
      ∀ v : F.U, p (s.uSection.coordinates v).toAdd =
        d.projection (d.conjugationSection.coordinates v).toAdd := by
  let n : F.U →* Multiplicative Representation.SL2FourNatural.V :=
    d.projection.toLinearMap.toAddMonoidHom.toMultiplicative.comp d.conjugationSection.coordinates
  have hker : s.uSection.coordinates.ker ≤ n.ker := by
    intro v hv
    have hv' := (s.uSection.coordinates_eq_one_iff v).mp hv
    exact (d.mem_U₀ v).mp (u_centralizer_le_U₀ d hc s hcomm hv')
  let f : Multiplicative X →* Multiplicative Representation.SL2FourNatural.V :=
    s.uSection.coordinates.liftOfSurjective s.uSection.onto ⟨n, hker⟩
  have hf (v : F.U) : f (s.uSection.coordinates v) = n v :=
    s.uSection.coordinates.liftOfRightInverse_comp_apply _ _ _ v
  let p₀ : X →ₗ[ZMod 2] Representation.SL2FourNatural.V :=
    (AddMonoidHom.toMultiplicative.symm f).toZModLinearMap 2
  have hp₀ (v : F.U) : p₀ (s.uSection.coordinates v).toAdd =
      d.projection (d.conjugationSection.coordinates v).toAdd := hf v
  have he (h : F.H) (x : X) : p₀ (s.uAction h x) =
      (d.naturalQuotient.action.comp d.qH) h (p₀ x) := by
    obtain ⟨v, hv⟩ := s.uSection.onto (Multiplicative.ofAdd x)
    have hv' : (s.uSection.coordinates v).toAdd = x := congrArg Multiplicative.toAdd hv
    rw [← hv', ← s.uSection.equivariant, hp₀, hp₀, d.conjugationSection.equivariant]
    exact LinearMap.congr_fun (d.projection.isIntertwining' h) _
  let p := p₀.intertwiningMap_of_isIntertwiningMap s.uAction
    (d.naturalQuotient.action.comp d.qH) he
  refine ⟨p, ?_, hp₀⟩
  intro w
  obtain ⟨v, hv⟩ := d.projection_onto w
  obtain ⟨u, hu⟩ := d.conjugationSection.onto (Multiplicative.ofAdd v)
  refine ⟨(s.uSection.coordinates u).toAdd, ?_⟩
  change p₀ _ = w
  rw [hp₀, hu]
  exact hv

/-- Duality embeds the dual of the original natural quotient into the
literal Q_H/C_{Q_H}(U) section. This supplies an actual invariant submodule,
with all H-actions retained, for the subsequent two-factor calculation. -/
theorem exists_dual_natural_embedding (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    ∃ j : Representation.IntertwiningMap
      (Representation.dual (d.naturalQuotient.action.comp d.qH)) s.qAction,
      Function.Injective j ∧
      ∀ (a : Module.Dual (ZMod 2) Representation.SL2FourNatural.V) (v : F.U),
        s.duality (j a) (s.uSection.coordinates v).toAdd =
          a (d.projection (d.conjugationSection.coordinates v).toAdd) := by
  obtain ⟨p, hp, hcoord⟩ := exists_natural_projection d hc s hcomm
  let j := s.duality.symm.toIntertwiningMap.comp
    (Representation.OneCohomology.dualIntertwining p)
  refine ⟨j, s.duality.symm.toLinearEquiv.injective.comp
    (LinearMap.dualMap_injective_of_surjective hp), ?_⟩
  intro a v
  change s.duality (s.duality.symm (p.toLinearMap.dualMap a)) _ = _
  rw [s.duality.apply_symm_apply]
  change a (p _) = _
  rw [hcoord]

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors
