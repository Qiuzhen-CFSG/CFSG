module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.SecondLayer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.Nonabelian.SourceLayers
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.Nonabelian.Realization

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniPairing
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical.Assembly

/-!
# Nonabelian Frattini centralizers from the actual MS93 orbit layers

Write C for the commutator core and D = C_C(Phi(C)). The regular source
path has a nonabelian second orbit layer W. Its doubled-dual quotient has
full residual movement, so W lies in [W,Ltilde] times the first orbit layer.
That first layer is central in the radius-four group. The proved third-layer
core bound and its derived-group bound place the moved radius-four group in D.
Thus W's noncommutation survives in D.

All higher-layer assertions are supplied by the existing source proofs.
The sole geometric input is the preceding MS93 (4.4) record `Earlier`.
A second theorem constructs it from distance greater than four and prescribed
replacement. Neither of those preceding source obligations is asserted here.

The application transports through the literal amalgam-core isomorphism and
proves the checked-center commutator identity used in 13.6.22. It discharges
nonabelianness, center control and the large Frattini-commutator premise;
`Earlier` remains explicit for final source assembly.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.4), (4.5.4)(iii),(vi), and (4.5.5), printed pp.890--899;
Aschbacher--Smith, combined manuscript (1 March 2004), C.1.34(4),
pp.136--137, and 13.6.22, pp.932--933.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.Nonabelian.Source
open NormalizerTransfer Higher
local notation "sCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

private theorem second_moving (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) ≤
      ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),Ltilde R (alpha R)⁆ ⊔
      hatV R (alpha R) (p.walk.getVert 6) := by
  let A := hatV R (alpha R) (p.walk.getVert 6)
  let B := hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)
  let D := ⁅B,Ltilde R (alpha R)⁆ ⊔ A
  let P := stabilizer R (alpha R)
  have hnL : P ≤ normalizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pResidual 2 P))
  have hE : P ≤ normalizer ((⁅B,Ltilde R (alpha R)⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅B,Ltilde R (alpha R)⁆).map (MulAut.conj g).toMonoidHom = _
    dsimp only [B]
    rw [map_commutator, MulEquiv.toMonoidHom_eq_coe,
      mem_normalizer_iff_map_conj_eq.mp (hatW_normalized R _ _ _ hg),
      mem_normalizer_iff_map_conj_eq.mp (hnL hg)]
  have hND : P ≤ normalizer D :=
    (le_inf hE (hatV_normalized R _ _)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hZA : Z R (alpha R) ≤ A :=
    Early.Z_le_hatV rfl (by simpa only [p.center_eq] using
      (p.distance (geometry := geometry) (i := 4) (j := 6) (by decide) (by decide)))
  have hBC : ⁅B,P⁆ ≤ D := by
    let C := commutatorPreimage P B D
    have hL : Ltilde R (alpha R) ≤ C := by
      apply le_commutatorPreimage (Ltilde_le_stabilizer _)
      rw [commutator_comm]
      exact le_sup_left
    have hQ : Q R (alpha R) ≤ C := by
      apply le_commutatorPreimage (show Q R (alpha R) ≤ P from fun _ hx => hx.1)
      rw [commutator_comm]
      exact (Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p).hatW_commutator.trans
        (hZA.trans le_sup_right)
    have hPC : P ≤ C := by
      change stabilizer R (alpha R) ≤ C
      rw [← source.local_generation (alpha R) rfl]
      exact sup_le hL hQ
    rw [commutator_comm]
    exact (commutator_mono hPC le_rfl).trans (commutator_commutatorPreimage_le P B D hND)
  obtain ⟨s⟩ := Quotients.SecondLayer.OrbitSource.marked_pair common earlier p
  exact s.le_of_commutator_le le_sup_right (by
    simpa only [D,A,B,P,alpha,stabilizer_m_base] using hBC)

omit [Finite M] in
private theorem derived_sup_center (A V : Subgroup M) (hA : A ≤ V) :
    ⁅A ⊔ sCenter V,A ⊔ sCenter V⁆ = ⁅A,A⁆ := by
  let B := A ⊔ sCenter V
  have hB : B ≤ V := sup_le hA (map_subtype_le _)
  have hc : sCenter V ≤ centralizer (B : Set M) :=
    ((centerIn_eq V).le.trans inf_le_right).trans (centralizer_le hB)
  have hgen : sCenter V ⊔ A = B := sup_comm _ _
  have h₁ := commutator_eq_of_centralizing_sup hgen
    (hc.trans (centralizer_le (show A ≤ B from le_sup_left))) A.le_normalizer
  have h₂ := commutator_eq_of_centralizing_sup hgen hc
    ((show A ≤ B from le_sup_left).trans B.le_normalizer)
  exact h₂.symm.trans ((commutator_comm B A).trans h₁.symm)

/-- The actual higher layers discharge the radius-four Frattini-centralizer
noncommutation, conditional only on the independently preceding MS93 (4.4). -/
theorem frattiniCentralizer_derived_ne_bot (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) :
    let D := core R (alpha R) ⊓
      centralizer (frattiniIn (core R (alpha R)) : Set (FreeAmalgam R))
    ⁅D,D⁆ ≠ ⊥ := by
  obtain ⟨p⟩ := Early.sourcePath_nonempty source common earlier (alpha R) rfl
  let W := hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)
  let V₄ := VBall R (alpha R) 4
  let E := ⁅V₄,Ltilde R (alpha R)⁆
  let q := Early.Orbit.SourceApplications.higherPath geometry p
  have hW : W ≤ V₄ := hatW_le_radius R
    q.two_step_distances.1.le q.two_step_distances.2.1.le
  have hE : E ≤ V₄ := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer _).trans (Escape.Propagation.RadiusFour.VBall_normalized (alpha R) 4))
  have hfactor : W ≤ E ⊔ sCenter V₄ := (second_moving common earlier p).trans
    (sup_le_sup (commutator_mono hW le_rfl)
      ((hatV_le_radius R q.two_step_distances.1.le).trans
        (SourceLayers.radiusTwo_le_radiusFour_center (by rw [earlier.distance]; decide))))
  have hD : E ≤ core R (alpha R) ⊓
      centralizer (frattiniIn (core R (alpha R)) : Set (FreeAmalgam R)) :=
    SourceLayers.moved_le_frattiniCentralizer_of_sixthOrbit source earlier.distance
      q.two_step_distances.1.le q.two_step_distances.2.1.le q.two_step_distances.2.2.le
      (Early.Orbit.Source.Complete.core_le_third_hat common earlier p)
      (le_sup_left.trans (Higher.OrbitGeometry.Source.commutator_layers common earlier p).2.le)
  dsimp only
  intro hz
  apply Center.second_nonabelian common earlier p
  apply le_bot_iff.mp
  apply (commutator_mono hfactor hfactor).trans
  rw [derived_sup_center E V₄ hE]
  exact (commutator_mono hD hD).trans hz.le

open DistanceEight.PathCentrality

/-- The original source facts and prescribed replacement supply all higher-layer
premises; no radius-four factorization is retained. -/
theorem frattiniCentralizer_derived_ne_bot_of_replacement
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (replacement : ∀ {a a'} (p : CriticalPath R geometry a a'),
      HasTurnConjugators R p → PrescribedReplacement R p) :
    let D := core R (alpha R) ⊓
      centralizer (frattiniIn (core R (alpha R)) : Set (FreeAmalgam R))
    ⁅D,D⁆ ≠ ⊥ :=
  frattiniCentralizer_derived_ne_bot common
    (Source44.SourceEarlier.earlier common hb replacement)

open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection

universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : CFSG.Quasithin.GroupClass.{u}} {K T S : Subgroup G}

/-- Transport to the literal finite source core through the constructed amalgam,
characteristic replacement and join inclusions. -/
theorem realized_frattiniCentralizer_derived_ne_bot
    {hMS : LinearThreeMSPair κ K T 1 (ZMod 2)}
    {e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group}
    (d : Realization.Data hMS e)
    (earlier : Earlier d.setup.reduction.radical d.setup.geometry) :
    let D := msQ K T ⊓ centralizer (frattiniIn (msQ K T) : Set G)
    ⁅D,D⁆ ≠ ⊥ :=
  (frattiniCentralizer_derived_ne_bot_iff d.coreEquiv).mp
    (frattiniCentralizer_derived_ne_bot d.common earlier)

/-- The actual fourth-case quotient calculation in 13.6.22. The sole additional
MS93 input is its preceding (4.4) record; nonabelianness, center control and the
large Frattini commutator are all discharged. -/
theorem sourceSpecialized_checked_commutator_of_earlier
    (L T : Subgroup G) (z v : G) (hK : K ∈ Yz L T z v) (hv : v ^ 2 = 1)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hMS : LinearThreeMSPair κ K (Tv T v) 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (h : CaseFour K (Tv T v) S e)
    (earlier : Earlier
      (Realization.ofSourceSpecialized L T z v hK hn hMS e h).setup.reduction.radical
      (Realization.ofSourceSpecialized L T z v hK hn hMS e h).setup.geometry) :
    ⁅sourceZ0 K v hK.1.1,K⁆ = sourceU K :=
  CenterRadical.caseFour_checked_commutator_of_nonabelian T v hK.1.1 hv hMS e h
    (realized_frattiniCentralizer_derived_ne_bot
      (Realization.ofSourceSpecialized L T z v hK hn hMS e h) earlier)
    (caseFour_frattiniCommutatorLarge hMS e h)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.Nonabelian.Source
