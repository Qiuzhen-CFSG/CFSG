module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.Orientation

/-!
# The first natural moving section on the actual subgroups

The quotient image of [X,Ltilde] is the intrinsic moving subgroup of X/hatW.
The source residual surjects onto SL3(2), so the previous natural coordinates
transport to [X,Ltilde]hatW/hatW, preserving the exact kernel and the original
marking. This is the first of the two factors needed in (4.5.4)(iv); it does
not assume or assert generation of the whole third moving layer.

Source: Meierfrankenfeld--Stellmacher (1993), proof of (4.5.4)(iv), p.899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
open DistanceFour.Linear
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- A single natural factor with the original marking, quotient and kernel. -/
structure MarkedNaturalSection (source : LocalSource L R) (common : CommonFacts R source geometry)
    (A N : Subgroup (FreeAmalgam R)) where
  local_group : A ≤ stabilizer R (alpha R)
  lower_le : N ≤ A
  normalized : Mbar R ≤ normalizer A
  quotient : A →* Multiplicative W
  onto : Function.Surjective quotient
  kernel : quotient.ker = N.subgroupOf A
  action : ∀ (m : M) (x y : A),
    (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
    (quotient y).toAdd = (common.natural.marking (source.projection m)).val.mulVec (quotient x).toAdd

/-- The actual residual-moving subgroup of the first source orbit factor. -/
@[expose] noncomputable def residualMovingGroup (p : Higher.SourcePath (alpha R)) : Subgroup (FreeAmalgam R) :=
  ⁅orbitMovingGroup p,Ltilde R (alpha R)⁆ ⊔
    hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)

omit [Finite M] in
private theorem local_residual_normalized (R : Subgroup M) (a : Vertex R) :
    stabilizer R a ≤ normalizer (Ltilde R a) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨z,hz,rfl⟩ := hx
  refine ⟨⟨g,hg⟩ * z * ⟨g,hg⟩⁻¹,?_,rfl⟩
  exact (inferInstance : (pResidual 2 (stabilizer R a)).Normal).conj_mem z hz ⟨g,hg⟩

omit [Finite M] in
/-- The actual moving group stays inside the source orbit group. -/
theorem residualMovingGroup_le_orbit (p : Higher.SourcePath (alpha R)) :
    residualMovingGroup p ≤ orbitMovingGroup p := by
  apply sup_le ?_ le_sup_right
  apply le_normalizer_iff_commutator_le_left.mp
  exact (Ltilde_le_stabilizer _).trans (by
    simpa only [alpha,stabilizer_m_base] using orbitMovingGroup_normalized p)

omit [Finite M] in
/-- The original local group normalizes the residual-moving subgroup. -/
theorem residualMovingGroup_normalized (p : Higher.SourcePath (alpha R)) :
    Mbar R ≤ normalizer (residualMovingGroup p) := by
  intro g hg
  have hgP : g ∈ stabilizer R (alpha R) := by simpa only [alpha,stabilizer_m_base] using hg
  rw [mem_normalizer_iff_map_conj_eq, residualMovingGroup, Subgroup.map_sup, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (orbitMovingGroup_normalized p hg),
    mem_normalizer_iff_map_conj_eq.mp (local_residual_normalized R _ hgP),
    mem_normalizer_iff_map_conj_eq.mp (hatW_normalized R _ _ _ hgP)]

/-- The ambient residual commutator maps onto the intrinsic moving summand. -/
theorem MovingModule.residual_image (p : Higher.SourcePath (alpha R))
    (s : MovingModule source p) : let := s.normal
    (⁅orbitMovingGroup p,Ltilde R (alpha R)⁆.subgroupOf (orbitMovingGroup p)).map
      (QuotientGroup.mk' ((hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)).subgroupOf
        (orbitMovingGroup p))) = commutatorAction s.action.range (MovingSpace p) := by
  let := s.normal
  let P := stabilizer R (alpha R)
  let e := FirstDirect.baseEquiv R
  let ζ : P →* SL := source.projection.comp e.symm.toMonoidHom
  let τ : P →* MulAut (MovingSpace p) := s.action.comp ζ
  have hPX : P ≤ normalizer (orbitMovingGroup p) := by
    simpa only [P,alpha,stabilizer_m_base] using orbitMovingGroup_normalized p
  have hconj (g : P) (x : orbitMovingGroup p) :
      τ g (QuotientGroup.mk x) = QuotientGroup.mk
        (⟨(g : FreeAmalgam R) * (x : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹,
          (mem_normalizer_iff.mp (hPX g.property) x).mp x.property⟩ : orbitMovingGroup p) := by
    obtain ⟨m,rfl⟩ := e.surjective g
    change s.action (source.projection (e.symm (e m))) _ = _
    rw [e.symm_apply_apply]
    exact s.conjugation m x _ rfl
  have hLm : L.map source.projection = ⊤ := by
    have hm := congrArg (Subgroup.map source.projection) source.residual_sup_core
    rw [Subgroup.map_sup, ← source.projection_kernel, map_ker_self, sup_bot_eq,
      map_top_of_surjective _ source.projection_surjective] at hm
    exact hm
  have hJ : ((Ltilde R (alpha R)).subgroupOf P).map τ = s.action.range := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨ζ x,rfl⟩
    · rintro _ ⟨g,rfl⟩
      obtain ⟨m,hm,hg⟩ := hLm.ge (mem_top g)
      refine ⟨e m,?_,?_⟩
      · change embedM R m ∈ Ltilde R (alpha R)
        rw [Ltilde_alpha,source.residual]
        exact mem_map_of_mem _ hm
      · change s.action (source.projection (e.symm (e m))) = s.action g
        rw [e.symm_apply_apply,hg]
  have hi := quotient_conjugation_commutatorAction_eq_image P (orbitMovingGroup p)
    (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)) (Ltilde R (alpha R))
    hPX (Ltilde_le_stabilizer _) s.normal τ hconj
  rw [hJ] at hi
  exact hi.symm

/-- Natural coordinates of the intrinsic summand give an exact section of
[X,Ltilde]hat W/hat W on the original ambient subgroups. -/
theorem naturalSection_of_coordinates (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (s : MovingModule source p)
    (f : let := s.normal; commutatorAction s.action.range (MovingSpace p) ≃* Multiplicative W)
    (hf : let := s.normal; ∀ g x, (f (movingAction s.action g x)).toAdd =
      (common.natural.marking g).val.mulVec (f x).toAdd) :
    Nonempty (MarkedNaturalSection source common (residualMovingGroup p)
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))) := by
  let := s.normal
  let X := orbitMovingGroup p
  let N := hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)
  let D := residualMovingGroup p
  let C := commutatorAction s.action.range (MovingSpace p)
  let π := QuotientGroup.mk' (N.subgroupOf X)
  have hDX : D ≤ X := residualMovingGroup_le_orbit p
  have hcomm : ⁅X,Ltilde R (alpha R)⁆ ≤ X :=
    le_sup_left.trans hDX
  have himage : (⁅X,Ltilde R (alpha R)⁆.subgroupOf X).map π = C := s.residual_image p
  have hDC : D ≤ (C.comap π).map X.subtype := by
    refine sup_le ?_ ?_
    · intro x hx
      refine ⟨⟨x,hcomm hx⟩,?_,rfl⟩
      change π ⟨x,hcomm hx⟩ ∈ C
      rw [← himage]
      exact mem_map_of_mem _ hx
    · intro x hx
      let u : X := ⟨x,(show N ≤ X from le_sup_right) hx⟩
      refine ⟨u,?_,rfl⟩
      change π u ∈ C
      rw [show π u = 1 from (QuotientGroup.eq_one_iff u).mpr hx]
      exact C.one_mem
  let t : D →* C := (π.comp (inclusion hDX)).codRestrict C (by
    intro x
    obtain ⟨y,hy,he⟩ := hDC x.property
    have he' : y = inclusion hDX x := Subtype.ext he
    change π (inclusion hDX x) ∈ C
    rw [← he']
    exact hy)
  have ht : Function.Surjective t := by
    intro z
    obtain ⟨x,hx,he⟩ := himage.ge z.property
    let y : D := ⟨x,(show ⁅X,Ltilde R (alpha R)⁆ ≤ D from le_sup_left) hx⟩
    exact ⟨y,Subtype.ext he⟩
  let q := f.toMonoidHom.comp t
  refine ⟨⟨hDX.trans ((orbitMovingGroup_le_Q earlier p).trans (fun _ hx => hx.1)),
    le_sup_right,residualMovingGroup_normalized p,q,f.surjective.comp ht,?_,?_⟩⟩
  · ext x
    change f (t x) = 1 ↔ _
    rw [map_eq_one_iff f f.injective]
    change (t x : C) = 1 ↔ _
    rw [Subtype.ext_iff]
    change π (inclusion hDX x) = 1 ↔ _
    exact QuotientGroup.eq_one_iff (inclusion hDX x)
  · intro m x y hy
    have he : t y = movingAction s.action (source.projection m) (t x) := by
      apply Subtype.ext
      exact (s.conjugation m (inclusion hDX x) (inclusion hDX y) hy).symm
    change (f (t y)).toAdd = _
    rw [he]
    exact hf (source.projection m) (t x)

/-- The first natural source section in the original commutator convention. -/
theorem source_first_natural_section (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    Nonempty (MarkedNaturalSection source common
      (⁅orbitMovingGroup (Early.Orbit.SourceApplications.higherPath geometry p),Ltilde R (alpha R)⁆ ⊔
        hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))) := by
  obtain ⟨s,f,hf⟩ := source_moving_natural_coordinates common earlier p
  exact naturalSection_of_coordinates common earlier _ s f hf

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
