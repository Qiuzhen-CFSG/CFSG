module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.CentralTarget
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Path

/-!
# The unquotiented moving-layer commutator homomorphism

For the actual X on printed p.899, the earlier bound [hat W,Q_a] ≤ Z_a
places [X,hat W] in Z_a. Both arguments lie in Q_a and hence centralize
Z_a, so the commutator is multiplicative in each argument. The preceding
(4.4) centrality kills hat V in the second argument modulo Z(G_a).
The supplied (iii) section then gives coordinates on that literal quotient.
The target coordinates are the actual central quotient from `CentralTarget`.

Only the allowed earlier commutator bound and the (iii) witness are extra
inputs. No first-argument descent, faithfulness, or moving-section witness
is assumed or claimed. In particular the homomorphism may be nonzero on
hat W. Its kernel consists exactly of elements whose commutators with
hat W are central in G_a; controlling that subgroup is a further obligation.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4), (4.5.3), and the
commutator argument in the proof of (4.5.4)(iv), printed pp.895--899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
open DistanceFour.Linear NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- The actual X of the proof of (4.5.4)(iv), before taking any quotient. -/
@[expose] noncomputable def orbitMovingGroup (p : Higher.SourcePath (alpha R)) : Subgroup (FreeAmalgam R) :=
  conjugatesIn (hatV R (p.walk.getVert 8) (p.walk.getVert 10)) (stabilizer R (alpha R)) ⊔
    hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)

omit [Finite M] in
/-- The source group X lies in the local two-core, by radius six. -/
theorem orbitMovingGroup_le_Q (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R)) :
    orbitMovingGroup p ≤ Q R (alpha R) := by
  apply sup_le ?_ ?_
  · apply le_trans (b := hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10))
    · apply iSup_mono
      intro g
      apply map_mono
      intro x hx
      apply le_iSup (fun k : stabilizer R (p.walk.getVert 6) =>
        rightConjugate (hatV R (p.walk.getVert 8) (p.walk.getVert 10)) k) 1
      exact ⟨x,hx,by simp⟩
    · exact p.hatSix_le_Q earlier
  · exact (hatW_le_radius R p.two_step_distances.1.le p.two_step_distances.2.1.le).trans
      (Escape.Propagation.RadiusFour.VBall_le_Q (alpha R) rfl 4 (by rw [earlier.distance]; decide))

omit [Finite M] in
/-- Normalization uses the actual local stabilizer and both actual orbit factors. -/
theorem orbitMovingGroup_normalized (p : Higher.SourcePath (alpha R)) :
    Mbar R ≤ normalizer (orbitMovingGroup p) := by
  intro g hg
  have hg' : g ∈ stabilizer R (alpha R) := by
    simpa only [alpha, stabilizer_m_base] using hg
  rw [mem_normalizer_iff_map_conj_eq, orbitMovingGroup, Subgroup.map_sup,
    mem_normalizer_iff_map_conj_eq.mp
      (conjugatesIn_normalized (hatV R (p.walk.getVert 8) (p.walk.getVert 10))
        (stabilizer R (alpha R)) hg'),
    mem_normalizer_iff_map_conj_eq.mp
      (hatW_normalized R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) hg')]

private noncomputable def zMap (common : CommonFacts R source geometry) :
    Z R (alpha R) →* Multiplicative W :=
  (centralQuotientCoordinates common).toMonoidHom.comp (centralQuotientMap R)

private noncomputable def row (common : CommonFacts R source geometry)
    {A B : Subgroup (FreeAmalgam R)} (hB : B ≤ Q R (alpha R))
    (hc : ⁅A,B⁆ ≤ Z R (alpha R)) (a : A) : B →* Multiplicative W where
  toFun b := zMap common ⟨⁅(a : FreeAmalgam R),(b : FreeAmalgam R)⁆,
    hc (commutator_mem_commutator a.property b.property)⟩
  map_one' := by
    exact (congrArg (zMap common) (Subtype.ext (by simp))).trans (zMap common).map_one
  map_mul' b c := by
    rw [← map_mul]
    apply congrArg (zMap common)
    apply Subtype.ext
    change ⁅(a : FreeAmalgam R),(b : FreeAmalgam R) * (c : FreeAmalgam R)⁆ =
      ⁅(a : FreeAmalgam R),(b : FreeAmalgam R)⁆ * ⁅(a : FreeAmalgam R),(c : FreeAmalgam R)⁆
    have hz := commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes (alpha R) rfl)
      (hc (commutator_mem_commutator a.property c.property)) b (hB b.property)
    rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc _ (b : FreeAmalgam R), hz]
    group

private noncomputable def rawHom (common : CommonFacts R source geometry)
    {A B : Subgroup (FreeAmalgam R)} (hA : A ≤ Q R (alpha R)) (hB : B ≤ Q R (alpha R))
    (hc : ⁅A,B⁆ ≤ Z R (alpha R)) : A →* (B →* Multiplicative W) where
  toFun := row common hB hc
  map_one' := by
    apply MonoidHom.ext
    intro b
    change zMap common _ = 1
    exact (congrArg (zMap common) (Subtype.ext (by simp))).trans (zMap common).map_one
  map_mul' a c := by
    apply MonoidHom.ext
    intro b
    change zMap common _ = zMap common _ * zMap common _
    rw [mul_comm, ← map_mul]
    apply congrArg (zMap common)
    apply Subtype.ext
    change ⁅(a : FreeAmalgam R) * (c : FreeAmalgam R),(b : FreeAmalgam R)⁆ =
      ⁅(c : FreeAmalgam R),(b : FreeAmalgam R)⁆ * ⁅(a : FreeAmalgam R),(b : FreeAmalgam R)⁆
    have hz := commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes (alpha R) rfl)
      (hc (commutator_mem_commutator c.property b.property)) a (hA a.property)
    rw [commutatorElement_mul_left_eq_conj_mul, hz, mul_inv_cancel_right]

private theorem zMap_eq_one_iff (common : CommonFacts R source geometry) (z : Z R (alpha R)) :
    zMap common z = 1 ↔ (z : FreeAmalgam R) ∈
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
  change (centralQuotientCoordinates common) (centralQuotientMap R z) = 1 ↔ _
  rw [map_eq_one_iff _ (centralQuotientCoordinates common).injective,
    show centralQuotientMap R z = 1 ↔ z ∈ centralDenominator R from QuotientGroup.eq_one_iff z,
    centralDenominator_eq]
  exact ⟨fun h => h.2, fun h => ⟨z.property,h⟩⟩

private noncomputable def descend {A B C T : Type*} [Group A] [Group B] [Group C] [CommGroup T]
    (q : B →* C) (hq : Function.Surjective q) (b : A →* (B →* T))
    (hkill : ∀ a, q.ker ≤ (b a).ker) : A →* (C →* T) where
  toFun a := q.liftOfSurjective hq ⟨b a, hkill a⟩
  map_one' := by
    ext x
    obtain ⟨y,rfl⟩ := hq x
    simp only [MonoidHom.liftOfSurjective, MonoidHom.liftOfRightInverse_comp_apply,
      map_one, MonoidHom.one_apply]
  map_mul' a c := by
    ext x
    obtain ⟨y,rfl⟩ := hq x
    simp only [MonoidHom.liftOfSurjective, MonoidHom.liftOfRightInverse_comp_apply,
      map_mul, MonoidHom.mul_apply]

private theorem descend_apply {A B C T : Type*} [Group A] [Group B] [Group C] [CommGroup T]
    (q : B →* C) (hq : Function.Surjective q) (b : A →* (B →* T))
    (hkill : ∀ a, q.ker ≤ (b a).ker) (a : A) (x : B) :
    descend q hq b hkill a (q x) = b a x :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

private theorem second_denominator_killed (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hc : ⁅orbitMovingGroup p, hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)⁆ ≤ Z R (alpha R))
    (hB : hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) ≤ Q R (alpha R))
    (d : MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true) :
    ∀ a, d.quotient.ker ≤ (rawHom common (orbitMovingGroup_le_Q earlier p) hB hc a).ker := by
  intro a v hv
  rw [d.kernel] at hv
  change zMap common _ = 1
  apply (zMap_eq_one_iff common _).mpr
  change ⁅(a : FreeAmalgam R),(v : FreeAmalgam R)⁆ ∈ _
  rw [← commutatorElement_inv]
  apply Subgroup.inv_mem
  exact earlier.centrality (alpha R) rfl
    (commutator_mem_commutator
      (hatV_le_radius R p.two_step_distances.1.le hv) (orbitMovingGroup_le_Q earlier p a.property))



omit [Finite M] in
private theorem second_le_Q (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R)) :
    hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) ≤ Q R (alpha R) :=
  (hatW_le_radius R p.two_step_distances.1.le p.two_step_distances.2.1.le).trans
    (Escape.Propagation.RadiusFour.VBall_le_Q (alpha R) rfl 4 (by rw [earlier.distance]; decide))

omit [Finite M] in
private theorem comm_bound (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hWQ : ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8), Q R (alpha R)⁆ ≤
      Z R (alpha R)) :
    ⁅orbitMovingGroup p, hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)⁆ ≤ Z R (alpha R) := by
  rw [commutator_comm]
  exact (commutator_mono le_rfl (orbitMovingGroup_le_Q earlier p)).trans hWQ

/-- The unquotiented first-argument homomorphism into Hom(hat W / hat V, Z / Z ∩ Z(G)).
Both the second argument and the target use their proved, originally marked coordinates. -/
noncomputable def commutatorHom (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hWQ : ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8), Q R (alpha R)⁆ ≤
      Z R (alpha R))
    (d : MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true) :
    orbitMovingGroup p →* (Multiplicative (W × W) →* Multiplicative W) :=
  descend d.quotient d.onto
    (rawHom common (orbitMovingGroup_le_Q earlier p) (second_le_Q earlier p) (comm_bound earlier p hWQ))
    (second_denominator_killed common earlier p _ _ d)

/-- Evaluation is the literal ambient commutator followed by the actual central quotient. -/
theorem commutatorHom_apply (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hWQ : ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8), Q R (alpha R)⁆ ≤
      Z R (alpha R))
    (d : MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true)
    (x : orbitMovingGroup p) (w : hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)) :
    commutatorHom common earlier p hWQ d x (d.quotient w) =
      centralQuotientCoordinates common (centralQuotientMap R
        ⟨⁅(x : FreeAmalgam R),(w : FreeAmalgam R)⁆,
          by exact comm_bound earlier p hWQ (commutator_mem_commutator x.property w.property)⟩) :=
  descend_apply _ _ _ _ _ _

/-- Exact kernel criterion: central commutators with every element of hat W.
This does not assert containment of the kernel in hat W. -/
theorem mem_commutatorHom_ker (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hWQ : ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8), Q R (alpha R)⁆ ≤
      Z R (alpha R))
    (d : MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true) (x : orbitMovingGroup p) :
    x ∈ (commutatorHom common earlier p hWQ d).ker ↔
      ∀ w : hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),
        ⁅(x : FreeAmalgam R),(w : FreeAmalgam R)⁆ ∈
          (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx w
    have h := congrArg (fun f => f (d.quotient w)) hx
    rw [commutatorHom_apply] at h
    exact (zMap_eq_one_iff common _).mp h
  · intro hx
    apply MonoidHom.ext
    intro v
    obtain ⟨w,rfl⟩ := d.onto v
    rw [commutatorHom_apply]
    exact (zMap_eq_one_iff common _).mpr (hx w)

/-- Equivariance for the same CommonFacts marking and LocalSource projection. -/
theorem commutatorHom_action (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hWQ : ⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8), Q R (alpha R)⁆ ≤
      Z R (alpha R))
    (d : MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true)
    (m : M) (x y : orbitMovingGroup p)
    (hy : (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹)
    (v : W × W) :
    (commutatorHom common earlier p hWQ d y (Multiplicative.ofAdd
      (dual (common.natural.marking (source.projection m)) v.1,
       dual (common.natural.marking (source.projection m)) v.2))).toAdd =
    (common.natural.marking (source.projection m)).val.mulVec
      (commutatorHom common earlier p hWQ d x (Multiplicative.ofAdd v)).toAdd := by
  obtain ⟨w,hw⟩ := d.onto (Multiplicative.ofAdd v)
  let w' : hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) :=
    ⟨embedM R m * (w : FreeAmalgam R) * (embedM R m)⁻¹,
      le_normalizer_iff.mp d.normalized _ ⟨m,rfl⟩ _ w.property⟩
  have hw' : d.quotient w' = Multiplicative.ofAdd
      (dual (common.natural.marking (source.projection m)) v.1,
       dual (common.natural.marking (source.projection m)) v.2) := by
    apply Multiplicative.toAdd.injective
    simpa only [Bool.true_eq, reduceIte, hw, toAdd_ofAdd] using d.action m w w' rfl
  rw [← hw', ← hw, commutatorHom_apply, commutatorHom_apply]
  let z : Z R (alpha R) := ⟨⁅(x : FreeAmalgam R),(w : FreeAmalgam R)⁆,
    comm_bound earlier p hWQ (commutator_mem_commutator x.property w.property)⟩
  let z' : Z R (alpha R) := ⟨⁅(y : FreeAmalgam R),(w' : FreeAmalgam R)⁆,
    comm_bound earlier p hWQ (commutator_mem_commutator y.property w'.property)⟩
  have hz : (z' : FreeAmalgam R) = embedM R m * (z : FreeAmalgam R) * (embedM R m)⁻¹ := by
    change ⁅(y : FreeAmalgam R),(w' : FreeAmalgam R)⁆ = _
    rw [hy]
    exact (conjugate_commutatorElement _ _ _).symm
  change (centralQuotientCoordinates common (centralQuotientMap R z')).toAdd = _
  rw [← centralConjugate_mk m z z' hz]
  exact centralQuotientCoordinates_action common m _

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
