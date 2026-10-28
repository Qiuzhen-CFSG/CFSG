module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Assembly.Marked
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonbinaryNaturalClassical
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.Assembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Exceptional.Sp4.Seed

/-!
# The chosen-natural contradiction on the original shadow endgame

The linear branch combines the checked closure and amalgam arguments with
11.5.3. The symplectic branch uses the same terminal contradiction, deriving
one simultaneous basis and the two local residual images from the supplied
marked flag. Both branches use the actual selected H and its generation
parameter, the literal point residual, and the point-stabilizer orbit proved
from the original natural action. The source identity [V,L₁]=V₃ is supplied
by the full-cover point calculation.

The common application splits the genuine SL₃/Sp₄ marking retained by the
preceding geometry. Neither a terminal closure conclusion nor a contradiction
record is assumed. The hypotheses name the earlier Cartan and shadow geometry,
11.2.5, the point-normalizer decomposition and component, the global parameter,
the Cartan movement, the second local movement and its unique noncentral
component. Their source discharge remains with qt-d-1222-nonbinary-natural
and its local-geometry and shadow producers.

The independent nonbinary symplectic MS-pair recognition is still explicit.
Its producer is qt-c132-nonbinary-symplectic, and qt-d-1222-natural-closure
retains its discharge before declaring the final SL₃/Sp₄ theorem complete.
The field-four case and the repaired core argument in 11.5.7 are unchanged.
Source: Aschbacher--Smith, 11.5.2--8, printed pp.779--784; C.1.32, p.136.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
open LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

/-- The linear branch on the selected original endgame, with the point residual,
point orbit and seed-normalizer premises constructed from its marked action. -/
theorem sl3_impossible_of_endgame
    (s : E.CartanPrecedingGeometry) (e : ShadowReduction.EndgameAt E)
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
    (f : InvariantFlag (.sl3 m)) (hf : Amalgam.Even.FlagMatch E f)
    (hweak : Source.WeakClosureObstruction (T : Subgroup G) V E.V₁ E.H)
    (hsplit : L ⊓ E.G₁ = (E.L₁ ⊔ L.pCoreIn 2) ⊔ E.X)
    (hLi : Source.ComponentIn E.M₁ E.L₁)
    (hs : letI := D.elementary; ChapterE.globalS V = (E.input.field.degree : ℕ∞)) :
    False := by
  let F₀ : Nonabelian.MarkedFlag E :=
    ⟨.sl3 m, f, hf.point.symm, hf.plane.symm, hf.threeSpace.symm⟩
  exact ChosenModule.nonbinary_sl3_impossible_of_preceding_of_many E E.input.many s m f hf
    e.fixed_trivial (WeakClosure.seed_normalizer_le D E.input)
    e.point_mem e.point_ne_one e.transitive e.comparison e.outside hweak
    e.local_parameter e.generation_one hsplit hLi
    (Nonabelian.PointModels.pointResidual_eq F₀ e.fixed_trivial e.point_mem e.point_ne_one)
    (F₀.point_orbit e.fixed_trivial e.point_mem e.point_ne_one e.transitive) hs

/-- The symplectic branch in one constructed basis. Both local quotient images,
the point parabolic, point orbit and normalizer control are proved internally.
The independent nonbinary MS-pair classification remains explicit. -/
theorem sp4_impossible_of_endgame
    (s : E.CartanPrecedingGeometry) (e : ShadowReduction.EndgameAt E)
    (m : Symplectic.MarkedFlag E)
    (hweak : Source.WeakClosureObstruction (T : Subgroup G) V E.V₁ E.H)
    (hsplit : L ⊓ E.G₁ = (E.L₁ ⊔ L.pCoreIn 2) ⊔ E.X)
    (hLi : Source.ComponentIn E.M₁ E.L₁)
    (hs : letI := D.elementary; ChapterE.globalS V = (E.input.field.degree : ℕ∞))
    (hVX : ⁅V,E.X⁆ = V)
    (hunique : Source.UniqueNoncentralComponent (normalizer (E.V₂ : Set G)) E.V₂ E.L₂)
    (hmoved₂ : ⁅V,E.L₂⁆ = V)
    (hrecognition : Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2) → ChapterC.IsSp4FourBlock L) : False := by
  let F₀ : Nonabelian.MarkedFlag E :=
    ⟨.sp4 m.action, m.flag, m.point_eq, m.plane_eq, m.threeSpace_eq⟩
  have hmoved₁ : ⁅V,E.L₁⁆ = E.V₃ := by
    change ⁅V,localResidual L E.V₁⁆ = E.V₃
    rw [m.point_preimage, m.threeSpace_preimage]
    exact Normalizers.FixedSummand.Sp4.seed_first_commutator D E.input m.action m.flag
  apply ChosenModule.nonbinary_sp4_impossible_of_preceding_of_many E E.input.many s m
    (Sp4.alignment m.action)⁻¹
    (by simpa only [inv_inv] using m.point_coordinates)
    (by simpa only [inv_inv] using m.three_coordinates)
    m.plane_membership m.three_membership
    (by simpa only [inv_inv] using m.cartan_image (s.cartan.1.trans inf_le_left) hsplit)
    hVX (MulAut.conj (Sp4.alignment m.action)⁻¹)
    m.point_local_image m.plane_local_image hunique hmoved₁ hmoved₂
    (m.normalizer_control hunique) hrecognition e.fixed_trivial
    (WeakClosure.seed_normalizer_le D E.input) e.point_mem e.point_ne_one
    e.transitive e.comparison e.outside hweak e.local_parameter e.generation_one hsplit hLi
    (Nonabelian.PointModels.pointResidual_eq F₀ e.fixed_trivial e.point_mem e.point_ne_one)
    (F₀.point_orbit e.fixed_trivial e.point_mem e.point_ne_one e.transitive) hs

/-- The surviving SL₃/Sp₄ endgame on the original Chapter12 chosen module.
No abelianness, nonabelianness, equality K=L₁, or terminal closure record is
an input. The C.1.32 recognition premise must still be discharged. -/
theorem impossible_of_endgame
    (s : E.CartanPrecedingGeometry) (e : ShadowReduction.EndgameAt E)
    (hweak : Source.WeakClosureObstruction (T : Subgroup G) V E.V₁ E.H)
    (hsplit : L ⊓ E.G₁ = (E.L₁ ⊔ L.pCoreIn 2) ⊔ E.X)
    (hLi : Source.ComponentIn E.M₁ E.L₁)
    (hs : letI := D.elementary; ChapterE.globalS V = (E.input.field.degree : ℕ∞))
    (hVX : ⁅V,E.X⁆ = V)
    (hunique : Source.UniqueNoncentralComponent (normalizer (E.V₂ : Set G)) E.V₂ E.L₂)
    (hmoved₂ : ⁅V,E.L₂⁆ = V)
    (hrecognition : Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2) → ChapterC.IsSp4FourBlock L) : False := by
  obtain ⟨a,f,hp,hpl,ht⟩ := s.marking
  cases a with
  | sl3 m =>
    exact sl3_impossible_of_endgame E s e m f ⟨hp.symm,hpl.symm,ht.symm⟩
      hweak hsplit hLi hs
  | sp4 a =>
    let m : Symplectic.MarkedFlag E := ⟨a,f,hp,hpl,ht⟩
    exact sp4_impossible_of_endgame E s e m hweak hsplit hLi hs
      hVX hunique hmoved₂ hrecognition

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
