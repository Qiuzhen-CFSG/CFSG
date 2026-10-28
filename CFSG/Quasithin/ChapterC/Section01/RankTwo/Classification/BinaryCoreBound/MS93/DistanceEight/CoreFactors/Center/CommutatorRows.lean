module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.SecondLayer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.Frattini
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.HomSaturation

/-!
# Commutator rows on the first hat section

The core pairs with the first hat layer into the central two-dimensional
subgroup H. Descending this pairing through the literal marked dual quotient
produces all homomorphisms into H: the original local action stabilizes its
image, and the evaluations generate H. Consequently the first-layer
centralizer has index 64 in the core.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5), printed pp.895,899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
open NormalizerTransfer PathCentrality Higher DistanceFour.Linear
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

theorem core_eq_third_residual (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    core R (alpha R) =
      ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
        Ltilde R (alpha R)⁆ := by
  apply le_antisymm
  · rw [← source.core_full_commutation (alpha R) rfl]
    exact commutator_mono (Early.Orbit.Source.Complete.core_le_third_hat common earlier p) le_rfl
  · exact commutator_mono
      ((Early.Orbit.SourceApplications.higherPath geometry p).hatSix_le_Q earlier) le_rfl

theorem first_core_commutator (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    ⁅core R (alpha R),hatV R (alpha R) (p.walk.getVert 6)⁆ = H R (alpha R) := by
  have h := commutator_eq_of_centralizing_sup
    (show Z R (alpha R) ⊔ Vcirc R (alpha R) = hatV R (alpha R) (p.walk.getVert 6) by
      rw [sup_comm]; exact (Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p).hatV_eq.symm)
    (Quotients.FirstDirect.Z_centralizes_core common earlier)
    ((Vcirc_le_V R _).trans ((geometry.V_local _ rfl common.large_distance).trans
      (DistanceTwo.core_normalized _)))
  rw [← h,commutator_comm]
  exact moving_core_commutator common earlier

omit [Finite M] in
private theorem H_centralizes_local (earlier : Earlier R geometry) :
    H R (alpha R) ≤ centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R)) := by
  rintro z hz m hm
  obtain ⟨c,hc,he⟩ := H_le_localCenter_of_central R _ (earlier.centrality _ rfl) hz
  rw [← he]
  exact congrArg Subtype.val ((mem_center_iff.mp hc) ⟨m,hm⟩)

variable [IsMulCommutative (H R (alpha R))]

omit [IsMulCommutative (H R (alpha R))] in
private def coreRawRow (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (x : core R (alpha R)) : hatV R (alpha R) (p.walk.getVert 6) →* H R (alpha R) where
  toFun a := ⟨⁅(x : FreeAmalgam R),(a : FreeAmalgam R)⁆,
    (first_core_commutator common earlier p).le (commutator_mem_commutator x.property a.property)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by
    apply Subtype.ext
    change ⁅(x : FreeAmalgam R),(a : FreeAmalgam R) * b⁆ =
      ⁅(x : FreeAmalgam R),(a : FreeAmalgam R)⁆ * ⁅(x : FreeAmalgam R),(b : FreeAmalgam R)⁆
    have hz := H_centralizes_local earlier
      ((first_core_commutator common earlier p).le (commutator_mem_commutator x.property b.property))
      a ((hatV_le_radius R
        (Early.Orbit.SourceApplications.higherPath geometry p).two_step_distances.1.le).trans
          (geometry.V_local _ rfl common.large_distance) a.property)
    rw [commutatorElement_mul_right_eq_mul_conj,mul_assoc _ (a : FreeAmalgam R),hz]
    group

private def coreRawPairing (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    core R (alpha R) →* (hatV R (alpha R) (p.walk.getVert 6) →* H R (alpha R)) where
  toFun := coreRawRow common earlier p
  map_one' := by ext a; simp [coreRawRow]
  map_mul' x y := by
    ext a
    change ⁅(x : FreeAmalgam R) * y,(a : FreeAmalgam R)⁆ =
      ⁅(x : FreeAmalgam R),(a : FreeAmalgam R)⁆ * ⁅(y : FreeAmalgam R),(a : FreeAmalgam R)⁆
    have hc := (first_core_commutator common earlier p).le
      (commutator_mem_commutator y.property a.property)
    have hx := H_centralizes_local earlier hc x ((DistanceTwo.core_le_Q _ x.property).1)
    rw [commutatorElement_mul_left_eq_conj_mul,hx,mul_inv_cancel_right]
    exact congrArg Subtype.val (mul_comm (coreRawRow common earlier p y a)
      (coreRawRow common earlier p x a))


omit [IsMulCommutative (H R (alpha R))] in
private theorem coreRawRow_kills_denominator (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (s : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (x : core R (alpha R)) : s.quotient.ker ≤ (coreRawRow common earlier p x).ker := by
  intro a ha
  rw [s.kernel] at ha
  apply MonoidHom.mem_ker.mpr
  apply Subtype.ext
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    (Quotients.FirstDirect.Z_centralizes_core common earlier ha x x.property)

noncomputable def coreCommutatorRow (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (s : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R))) :
    core R (alpha R) →* (Multiplicative W →* H R (alpha R)) where
  toFun x := s.quotient.liftOfSurjective s.onto
    ⟨coreRawRow common earlier p x, coreRawRow_kills_denominator common earlier p s x⟩
  map_one' := by
    apply MonoidHom.ext
    intro v
    obtain ⟨a,rfl⟩ := s.onto v
    rw [s.quotient.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv s.onto)]
    apply Subtype.ext
    simp [coreRawRow]
  map_mul' x y := by
    apply MonoidHom.ext
    intro v
    obtain ⟨a,rfl⟩ := s.onto v
    simp only [MonoidHom.mul_apply]
    simp only [s.quotient.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv s.onto)]
    exact congrArg (fun f => f a) (coreRawPairing common earlier p |>.map_mul x y)

theorem coreCommutatorRow_apply (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (s : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (x : core R (alpha R)) (a : hatV R (alpha R) (p.walk.getVert 6)) :
    ((coreCommutatorRow common earlier p s x (s.quotient a)) : FreeAmalgam R) =
      ⁅(x : FreeAmalgam R),(a : FreeAmalgam R)⁆ := by
  change (((s.quotient.liftOfSurjective s.onto
    ⟨coreRawRow common earlier p x, coreRawRow_kills_denominator common earlier p s x⟩)
      (s.quotient a) : H R (alpha R)) : FreeAmalgam R) = _
  rw [s.quotient.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv s.onto)]
  rfl

theorem coreCommutatorRow_evaluations_generate (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (s : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R))) :
    (⨆ x : core R (alpha R), (coreCommutatorRow common earlier p s x).range) = ⊤ := by
  let D := ⨆ x : core R (alpha R), (coreCommutatorRow common earlier p s x).range
  have hHD : H R (alpha R) ≤ D.map (H R (alpha R)).subtype := by
    apply (first_core_commutator common earlier p).ge.trans
    apply commutator_le.mpr
    intro x hx a ha
    refine ⟨coreCommutatorRow common earlier p s ⟨x,hx⟩ (s.quotient ⟨a,ha⟩), ?_, ?_⟩
    · exact (le_iSup (fun x : core R (alpha R) =>
        (coreCommutatorRow common earlier p s x).range) ⟨x,hx⟩) ⟨_,rfl⟩
    · exact coreCommutatorRow_apply common earlier p s _ _
  apply top_unique
  intro x _
  obtain ⟨y,hy,he⟩ := hHD x.property
  exact (Subtype.ext he : y = x) ▸ hy


theorem coreCommutatorRow_action (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (s : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (m : M) (x y : core R (alpha R))
    (hy : (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹)
    (v : W) :
    coreCommutatorRow common earlier p s y
      (Multiplicative.ofAdd (dual (common.natural.marking (source.projection m)) v)) =
      coreCommutatorRow common earlier p s x (Multiplicative.ofAdd v) := by
  obtain ⟨a,ha⟩ := s.onto (Multiplicative.ofAdd v)
  let a' : hatV R (alpha R) (p.walk.getVert 6) :=
    ⟨embedM R m * (a : FreeAmalgam R) * (embedM R m)⁻¹,
      le_normalizer_iff.mp s.normalized _ ⟨m,rfl⟩ _ a.property⟩
  have ha' : s.quotient a' =
      Multiplicative.ofAdd (dual (common.natural.marking (source.projection m)) v) := by
    apply Multiplicative.toAdd.injective
    rw [s.action m a a' rfl,ha]
    simp only [toAdd_ofAdd]
  apply Subtype.ext
  rw [← ha',← ha,coreCommutatorRow_apply,coreCommutatorRow_apply]
  have hc := H_centralizes_local earlier
    ((first_core_commutator common earlier p).le
      (commutator_mem_commutator x.property a.property)) (embedM R m)
    (by change embedM R m ∈ stabilizer R (alpha R)
        simpa only [alpha,stabilizer_m_base] using (show embedM R m ∈ Mbar R from ⟨m,rfl⟩))
  rw [hy]
  change ⁅embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹,
    embedM R m * (a : FreeAmalgam R) * (embedM R m)⁻¹⁆ = _
  calc
    _ = embedM R m * ⁅(x : FreeAmalgam R),(a : FreeAmalgam R)⁆ * (embedM R m)⁻¹ := by group
    _ = _ := by rw [hc,mul_inv_cancel_right]

theorem coreCommutatorRow_mem_ker_iff (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (s : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (x : core R (alpha R)) :
    x ∈ (coreCommutatorRow common earlier p s).ker ↔
      (x : FreeAmalgam R) ∈
        centralizer (hatV R (alpha R) (p.walk.getVert 6) : Set (FreeAmalgam R)) := by
  constructor
  · intro hx a ha
    have he := congrArg (fun f : Multiplicative W →* H R (alpha R) =>
      (f (s.quotient ⟨a,ha⟩) : FreeAmalgam R)) (MonoidHom.mem_ker.mp hx)
    rw [coreCommutatorRow_apply] at he
    exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
  · intro hx
    apply MonoidHom.mem_ker.mpr
    apply MonoidHom.ext
    intro v
    obtain ⟨a,rfl⟩ := s.onto v
    apply Subtype.ext
    rw [coreCommutatorRow_apply]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hx a a.property).symm

theorem core_inf_second_le_row_kernel (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (s : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R))) :
    core R (alpha R) ⊓ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) ≤
      ((coreCommutatorRow common earlier p s).ker).map (core R (alpha R)).subtype := by
  rintro x ⟨hx,hW⟩
  refine ⟨⟨x,hx⟩,(coreCommutatorRow_mem_ker_iff common earlier p s _).mpr ?_,rfl⟩
  exact (le_centralizer_iff.mp
    (Quotients.SecondLayer.Recognition.denominator_centralizes_second earlier
      (Early.Orbit.SourceApplications.higherPath geometry p))) hW

theorem core_center_le_row_kernel (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (s : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R))) :
    (center (core R (alpha R))).map (core R (alpha R)).subtype ≤
      ((coreCommutatorRow common earlier p s).ker).map (core R (alpha R)).subtype := by
  rintro x ⟨x,hx,rfl⟩
  refine ⟨x,(coreCommutatorRow_mem_ker_iff common earlier p s x).mpr ?_,rfl⟩
  exact (centralizer_le (Quotients.SecondLayer.lower_le_second
    (Early.Orbit.SourceApplications.higherPath geometry p)))
      (core_center_centralizes_second common earlier p ⟨x,hx,rfl⟩)


/-- The actual commutator rows exhaust all maps from the original first dual section to H. -/
theorem coreCommutatorRow_surjective (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (s : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R))) :
    Function.Surjective (coreCommutatorRow common earlier p s) :=
  HomSaturation.core_row_surjective common earlier _
    (coreCommutatorRow_action common earlier p s)
    (coreCommutatorRow_evaluations_generate common earlier p s)

omit [IsMulCommutative (H R (alpha R))] in
theorem first_centralizer_relIndex_eq_sixtyFour (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    (core R (alpha R) ⊓ centralizer
      (hatV R (alpha R) (p.walk.getVert 6) : Set (FreeAmalgam R))).relIndex
        (core R (alpha R)) = 64 := by
  let := H_elementary_of_central R (alpha R)
    (geometry.V_local _ rfl common.large_distance) (earlier.centrality _ rfl)
  obtain ⟨s⟩ := Quotients.FirstDirect.markedDualSection common earlier p
  have hi := HomSaturation.core_row_kernel_index common earlier
    (coreCommutatorRow common earlier p s)
    (coreCommutatorRow_action common earlier p s)
    (coreCommutatorRow_evaluations_generate common earlier p s)
  have he : (coreCommutatorRow common earlier p s).ker =
      (centralizer (hatV R (alpha R) (p.walk.getVert 6) : Set (FreeAmalgam R))).subgroupOf
        (core R (alpha R)) := by
    ext x
    exact coreCommutatorRow_mem_ker_iff common earlier p s x
  rw [he] at hi
  rw [inf_relIndex_left]
  exact hi

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
