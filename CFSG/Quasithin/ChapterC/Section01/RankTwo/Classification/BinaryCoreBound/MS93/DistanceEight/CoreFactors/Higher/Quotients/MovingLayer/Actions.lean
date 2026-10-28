module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.NontrivialAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.Complete
public import Theory.GroupAction.SubgroupQuotientFullAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Decomposition

/-!
# Descent of the actual moving orbit action

The higher commutator bound puts [X,Q_a] in hat V_a, hence in hat W_a.
Together with nontrivial residual action this identifies the action kernel
with Q_a. Conjugation on the literal quotient X/hat W_a therefore descends
through the original LocalSource projection to a faithful SL3(2) action.

The higher bound is supplied by the independent (4.5.5) geometry, using the
previous doubled-dual section and the independently proved first dual section.
No natural coordinates or moving-factor independence is assumed here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(iv), p.899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
open NormalizerTransfer
variable {M : Type*} [Group M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- The source X is contained in the actual third hat layer. -/
theorem orbitMovingGroup_le_third [Finite M] (p : Higher.SourcePath (alpha R)) :
    orbitMovingGroup p ≤
      hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10) := by
  refine sup_le ?_ ?_
  · apply iSup_mono
    intro g
    apply map_mono
    exact Escape.Initial.Natural.conjugatesIn_contains _ _
  · exact OrbitGeometry.hatW_le_hatSix
      ((PathCentrality.RegularPaths.walk_vertex_color p.start_color p.walk
        (by rw [p.length_eq]; decide)).mpr (by decide))
      (by rw [SimpleGraph.dist_comm]; exact p.two_step_distances.2.2)

/-- The higher commutator bound kills the literal local two-core action. -/
theorem orbitMovingGroup_Q_commutator_le [Finite M] (p : Higher.SourcePath (alpha R))
    (hQ : ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      Q R (alpha R)⁆ ≤ hatV R (alpha R) (p.walk.getVert 6)) :
    ⁅orbitMovingGroup p, Q R (alpha R)⁆ ≤
      hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) :=
  (commutator_mono (orbitMovingGroup_le_third p) le_rfl).trans
    (hQ.trans (SecondLayer.lower_le_second p))

/-- The reverse inclusion in the original action-kernel calculation. -/
theorem Q_le_orbitActionKernel [Finite M] (p : Higher.SourcePath (alpha R))
    (hQ : ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      Q R (alpha R)⁆ ≤ hatV R (alpha R) (p.walk.getVert 6)) :
    Q R (alpha R) ≤ orbitActionKernel p := by
  apply le_commutatorPreimage
  · simpa only [alpha,stabilizer_m_base] using
      (show Q R (alpha R) ≤ stabilizer R (alpha R) from fun _ hx => hx.1)
  · rw [commutator_comm]
    exact orbitMovingGroup_Q_commutator_le p hQ

/-- Both source bounds identify the actual action kernel exactly. -/
theorem orbitActionKernel_eq_Q [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : Early.SourcePath R (alpha R))
    (hQ : ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      Q R (alpha R)⁆ ≤ hatV R (alpha R) (p.walk.getVert 6)) :
    orbitActionKernel (Early.Orbit.SourceApplications.higherPath geometry p) = Q R (alpha R) :=
  le_antisymm (orbitActionKernel_le_Q common earlier _
    (Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p).hatV_eq)
    (Q_le_orbitActionKernel _ hQ)

/-- The literal quotient of the source orbit group, before choosing coordinates. -/
abbrev MovingSpace (p : Higher.SourcePath (alpha R)) :=
  orbitMovingGroup p ⧸
    (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)).subgroupOf (orbitMovingGroup p)

/-- Constructed quotient-action data on X/hat W, with the original projection. -/
structure MovingModule (source : LocalSource L R) (p : Higher.SourcePath (alpha R)) where
  normal : ((hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)).subgroupOf
    (orbitMovingGroup p)).Normal
  finite : Finite (MovingSpace p)
  action : let := normal; SL →* MulAut (MovingSpace p)
  conjugation : let := normal
    ∀ (m : M) (x y : orbitMovingGroup p),
      (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
      action (source.projection m) (QuotientGroup.mk x) = QuotientGroup.mk y

/-- Descent through the exact source projection; no action is an input. -/
theorem movingModule [Finite M] (source : LocalSource L R)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hQ : ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      Q R (alpha R)⁆ ≤ hatV R (alpha R) (p.walk.getVert 6)) :
    Nonempty (MovingModule source p) := by
  let A := orbitMovingGroup p
  let N := hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)
  have hlocal : A ≤ Mbar R := (orbitMovingGroup_le_Q earlier p).trans (by
    simpa only [alpha,stabilizer_m_base] using
      (show Q R (alpha R) ≤ stabilizer R (alpha R) from fun _ hx => hx.1))
  have hA : Mbar R ≤ normalizer A := orbitMovingGroup_normalized p
  have hN : Mbar R ≤ normalizer N := by
    dsimp only [N]
    simpa only [alpha,stabilizer_m_base] using
      hatW_normalized R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)
  let hnormal : (N.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer (hlocal.trans hN)
  let : Finite (Mbar R) := Finite.of_surjective (embedM R).rangeRestrict
    (embedM R).rangeRestrict_surjective
  let : Finite A := Finite.of_injective (inclusion hlocal) (inclusion_injective _)
  obtain ⟨ρ,hρ⟩ := exists_quotient_conjugation_action (Mbar R) A N hA hN hnormal
  have hkill := quotient_conjugation_action_kills_commutator_layer (Mbar R) A N
    (Q R (alpha R)) hnormal hA (orbitMovingGroup_Q_commutator_le p hQ) ρ hρ
  let μ : M →* MulAut (MovingSpace p) := ρ.comp (embedM R).rangeRestrict
  have hk : source.projection.ker ≤ μ.ker := by
    intro m hm
    rw [source.projection_kernel] at hm
    apply hkill
    change embedM R m ∈ Q R (alpha R)
    rw [Q_alpha R source.two_group source.core_le]
    exact mem_map_of_mem _ hm
  let σ : SL →* MulAut (MovingSpace p) :=
    source.projection.liftOfSurjective source.projection_surjective ⟨μ,hk⟩
  refine ⟨⟨hnormal,inferInstance,σ,?_⟩⟩
  dsimp only
  intro m x y hy
  change σ (source.projection m) (QuotientGroup.mk' (N.subgroupOf A) x) = _
  dsimp only [σ]
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  change ρ ((embedM R).rangeRestrict m) (QuotientGroup.mk' (N.subgroupOf A) x) = _
  exact (hρ ⟨embedM R m,⟨m,rfl⟩⟩ x).trans
    (congrArg (QuotientGroup.mk' (N.subgroupOf A)) (Subtype.ext hy.symm))

/-- The descended action is faithful by the genuine residual nontriviality. -/
theorem MovingModule.faithful [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : Early.SourcePath R (alpha R))
    (s : MovingModule source (Early.Orbit.SourceApplications.higherPath geometry p)) :
    let := s.normal; Function.Injective s.action := by
  let := s.normal
  let q := Early.Orbit.SourceApplications.higherPath geometry p
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  rcases (inferInstance : s.action.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact s.action.ker_eq_bot_iff.mp hb
  exfalso
  have hone : s.action = 1 := MonoidHom.ker_eq_top_iff.mp ht
  apply orbitMovingGroup_residual_not_le_second common earlier q
    (Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p).hatV_eq
  rw [commutator_comm]
  apply commutator_le.mpr
  intro g hg x hx
  have hgM : g ∈ Mbar R := by
    simpa only [alpha,stabilizer_m_base] using Ltilde_le_stabilizer (alpha R) hg
  obtain ⟨m,rfl⟩ := hgM
  let u : orbitMovingGroup q := ⟨x,hx⟩
  let v : orbitMovingGroup q := ⟨embedM R m * x * (embedM R m)⁻¹,
    le_normalizer_iff.mp (orbitMovingGroup_normalized q) _ ⟨m,rfl⟩ _ hx⟩
  have he := s.conjugation m u v rfl
  rw [hone] at he
  have hn := QuotientGroup.eq_iff_div_mem.mp he.symm
  change embedM R m * x * (embedM R m)⁻¹ / x ∈
    hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) at hn
  simpa only [q,Early.Orbit.SourceApplications.higherPath,commutatorElement_def,div_eq_mul_inv] using hn

/-- The literal quotient is elementary abelian: its commutators are killed,
and the orbit generators come from the elementary first hat group at d. -/
theorem MovingModule.elementary [Finite M] (earlier : Earlier R geometry)
    (p : Higher.SourcePath (alpha R)) (s : MovingModule source p)
    (hQ : ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      Q R (alpha R)⁆ ≤ hatV R (alpha R) (p.walk.getVert 6)) :
    let := s.normal; IsElementaryAbelian 2 (MovingSpace p) := by
  let := s.normal
  let A := orbitMovingGroup p
  let N := hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)
  let π := QuotientGroup.mk' (N.subgroupOf A)
  have hcomm : ⁅A,A⁆ ≤ N := (commutator_mono le_rfl (orbitMovingGroup_le_Q earlier p)).trans
    (orbitMovingGroup_Q_commutator_le p hQ)
  let : IsMulCommutative (MovingSpace p) := ⟨⟨by
    intro x y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf A) x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf A) y
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hcomm (commutator_mem_commutator x.property y.property)⟩⟩
  let K := ((powMonoidHom 2 : MovingSpace p →* MovingSpace p).comp π).ker
  have hK : A ≤ K.map A.subtype := by
    apply sup_le
    · apply iSup_le
      intro g x hx
      obtain ⟨v,hv,rfl⟩ := hx
      have hxA : (MulAut.conj (g : FreeAmalgam R)⁻¹) v ∈ A :=
        (show conjugatesIn (hatV R (p.walk.getVert 8) (p.walk.getVert 10))
          (stabilizer R (alpha R)) ≤ A from le_sup_left)
          ((le_iSup (fun k : stabilizer R (alpha R) =>
            rightConjugate (hatV R (p.walk.getVert 8) (p.walk.getVert 10)) k) g)
            (mem_map_of_mem _ hv))
      refine ⟨⟨_,hxA⟩,?_,rfl⟩
      change (π ⟨_,hxA⟩)^2 = 1
      rw [← map_pow]
      have hd : color R (p.walk.getVert 8) = false :=
        (PathCentrality.RegularPaths.walk_vertex_color p.start_color p.walk
          (by rw [p.length_eq]; decide)).mpr (by decide)
      let : IsElementaryAbelian 2 (hatV R (p.walk.getVert 8) (p.walk.getVert 10)) :=
        PathCentrality.localZSpan_elementary R (a := p.walk.getVert 10)
        (c := p.walk.getVert 8) hd p.two_step_distances.2.2.le
        (by rw [earlier.distance]; decide)
      have he : (⟨(MulAut.conj (g : FreeAmalgam R)⁻¹) v,hxA⟩ : A)^2 = 1 := by
        apply Subtype.ext
        change ((MulAut.conj (g : FreeAmalgam R)⁻¹) v)^2 = 1
        rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian v hv, map_one]
      rw [he,map_one]
    · intro x hx
      let u : A := ⟨x,(show N ≤ A from le_sup_right) hx⟩
      refine ⟨u,?_,rfl⟩
      change (π u)^2 = 1
      have he : π u = 1 := (QuotientGroup.eq_one_iff u).mpr hx
      rw [he,one_pow]
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro z
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf A) z
  obtain ⟨y,hy,he⟩ := hK x.property
  have he' : y = x := Subtype.ext he
  subst y
  exact hy

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
