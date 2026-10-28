module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalRootCoordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.CoreReconstruction.NonFrattini
public import Theory.Representation.SymplecticNaturalNormalizer.FixedLineInner

/-!
# The original kernel action on the opposite natural layer

Reciprocal critical indices identify the image of Z_a as a natural
transvection root. Its displacement field line is covered by the actual
critical commutator. The original Q_a centralizes that commutator, so the
faithful ambient action fixes the whole field line. Field-line rigidity
puts this restricted action inside the actual symplectic component.

The resulting homomorphism Q_a to Sp4 retains exactly Q_a intersect Q_z
as its kernel, and Z_a has natural displacement at most one. This constructs
the marking consumed by GenerationTwoSymplecticRootAction, without replacing
the original group or assuming that its whole quotient is inner.
Source: MS93 (3.3) and (3.6), printed pp.867 and871.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterB.QuasisimpleSource Representation.SymplecticFourOrthogonalCover MSCentralOrbit Theory.GroupTheory
variable {M : Type*} [Group M] {R : Subgroup M} {a z : Vertex R}
  {F W J : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module (ZMod 2) W] [Group J]

omit [Finite F] [CharP F 2] in
private theorem critical_displacement_lifts
    (σ : Representation (ZMod 2) J W)
    (j : Multiplicative W →* FreeAmalgam R) (hjr : j.range = U R z)
    (β : Z R a →* J)
    (hβ : ∀ x : Z R a, ∀ w : W,
      j (Multiplicative.ofAdd (σ (β x) w)) =
        (x:FreeAmalgam R)*j (Multiplicative.ofAdd w)*(x:FreeAmalgam R)⁻¹)
    (p : W →ₗ[ZMod 2] Vector F) (hp : Function.Surjective p)
    (α : Z R a →* Sp F)
    (hα : ∀ x : Z R a, ∀ w : W, p (σ (β x) w) = α x • p w) :
    ∀ v ∈ displacementSpace α.range, ∃ w : W,
      j (Multiplicative.ofAdd w) ∈ ⁅Z R a,Z R z⁆ ∧ p w = v := by
  intro v hv
  let τ : Representation (ZMod 2) (Z R a) (Vector F) :=
    restrictScalars ((symplecticNatural 2).comp α)
  let pA : Representation.IntertwiningMap (σ.comp β) τ :=
    p.intertwiningMap_of_isIntertwiningMap _ _ hα
  have hv' : v ∈ Coinvariants.ker τ := by
    rw [coinvariants_restrictScalars]
    rwa [displacementSpace_range_eq] at hv
  rw [←map_coinvariants_of_surjective pA hp] at hv'
  obtain ⟨w,hw,rfl⟩ := hv'
  let P : Submodule (ZMod 2) W := AddSubgroup.toZModSubmodule 2
    ((⁅Z R a,Z R z⁆).comap j).toAddSubgroup'
  have hP : Coinvariants.ker (σ.comp β) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x,w⟩,rfl⟩
    change j (Multiplicative.ofAdd (σ (β x) w-w)) ∈ ⁅Z R a,Z R z⁆
    rw [ofAdd_sub,map_div,div_eq_mul_inv,hβ]
    apply commutator_mem_commutator x.property
    apply U_le_Z z
    rw [←hjr]
    exact ⟨Multiplicative.ofAdd w,rfl⟩
  exact ⟨w,hP hw,rfl⟩

private theorem marking_eq_one {A B : Type*} [Group A] [Group B]
    (P : Subgroup A) (Q : Subgroup B) (e : P ≃* Q) (x : P) :
    (e x : B) = 1 ↔ (x : A) = 1 := by
  constructor
  · intro h
    have he : e x = 1 := Subtype.ext h
    exact congrArg Subtype.val (e.injective (he.trans e.map_one.symm))
  · intro h
    have hx : x = 1 := Subtype.ext h
    exact congrArg Subtype.val ((congrArg e hx).trans e.map_one)

private theorem restricted_kernel_map {A B C : Type*} [Group A] [Group B] [Group C]
    (P S Q : Subgroup A) (hPS : P ≤ S) (κ : S →* B)
    (hκ : κ.ker.map S.subtype = Q) (f : P →* C)
    (hf : ∀ u : P, f u = 1 ↔ κ (inclusion hPS u) = 1) :
    f.ker.map P.subtype = P ⊓ Q := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    refine ⟨u.property,?_⟩
    rw [←hκ]
    exact ⟨inclusion hPS u,(hf u).mp hu,rfl⟩
  · rintro ⟨hxP,hxQ⟩
    let u : P := ⟨x,hxP⟩
    refine ⟨u,?_,rfl⟩
    apply (hf u).mpr
    rw [←hκ] at hxQ
    obtain ⟨w,hw,hwx⟩ := hxQ
    have heq : w = inclusion hPS u := Subtype.ext hwx
    exact heq ▸ hw

variable [Finite M] [Finite J]

/-- At an original distance-two critical pair, the action of Q_a on the
opposite natural layer is inner, with its entire kernel retained. -/
theorem original_kernel_root_action
    (R : Subgroup M) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 M ≤ R)
    (hself : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hfaith : centralizer (omegaOrbit R : Set M) = pCore 2 M)
    (q : M →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 M)
    [((pResidual 2 M).map q).Normal]
    [IsSimpleGroup ((pResidual 2 M).map q)] [IsQuasisimple ((pResidual 2 M).map q)]
    (hc : Nat.card ((pResidual 2 M).map q) = 979200)
    (hC : centralizer ((pResidual 2 M).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 M).map q))
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : geometry.b R = 2)
    (hlarge : ¬ core R a ≤ (frattini (Q R a)).map (Q R a).subtype ⊔ X R a) :
    ∃ F : BinaryField, F.degree = 2 ∧
      ∃ f : Q R a →* Sp F.Carrier,
        f.ker.map (Q R a).subtype = Q R a ⊓ Q R z ∧
        (∀ u : Q R a, (u:FreeAmalgam R) ∈ Z R a →
          Module.finrank F.Carrier (InvolutionTypes.movedSpace (f u)) ≤ 1) := by
  have hpos : 0 < geometry.b R := by omega
  obtain ⟨ha4,hz4⟩ := CoreReconstruction.original_critical_indices_eq_four_of_nonfrattini
    R hms hp hne hQR hself hfaith q hq hcore hc hC hsq path hb hlarge
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 M)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 M)) q hq hk) ((pResidual 2 M).map q)
  obtain ⟨F,hF,e,he,j,hj,hjr,κ,_hκ,hκQ,_hκC,_hκL,_hψ,hconj,_hproj,_hker⟩ :=
    ambient_initial_cover_at_vertex R hms hp hne hQR hself hfaith q hq hcore
      hc hC hsq path.end_color
  have hFc : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  have hAZ : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hQAZ : Q R a ≤ stabilizer R z :=
    Q_le_stabilizer_of_dist_two R a z path.start_color
      (path.critical.1.trans ((geometry.distance_constant a path.start_color).trans hb))
  let δ : Z R a →* J := κ.comp (inclusion hAZ)
  have hδcard : Nat.card δ.range = 4 :=
    (quotient_image_card _ _ _ hAZ κ hκQ).trans ha4
  have hδ : ∀ x : Z R a, ∀ w : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) w)) =
        (x:FreeAmalgam R)*j (Multiplicative.ofAdd w)*(x:FreeAmalgam R)⁻¹ :=
    fun x w => hconj (inclusion hAZ x) w
  obtain ⟨β,_hβcard,hβmark,hβ,hd,_hquad⟩ := critical_inner_root_actor path hpos
    (MSCentralOrbit.C_eq_Q R hp hQR hfaith a path.start_color) hFc s e he hC
      j hj hjr δ hδ hδcard hz4
  let α : Z R a →* Sp F.Carrier := (commutator (Sp F.Carrier)).subtype.comp β
  have hαrange : α.range = β.range.map (commutator (Sp F.Carrier)).subtype :=
    MonoidHom.range_comp _ _
  have hdim : Module.finrank F.Carrier (displacementSpace α.range) = 1 := hαrange.symm ▸ hd
  have hα : ∀ x : Z R a, ∀ w : s.space.toSubmodule,
      MovedSection.coverProjection s e (MovedSection.coverAction s e (β x) w) =
        α x • MovedSection.coverProjection s e w :=
    fun x w => LinearMap.congr_fun ((MovedSection.coverProjection s e).isIntertwining' (β x)) w
  have hlifts := critical_displacement_lifts (MovedSection.coverAction s e) j hjr β hβ
    (MovedSection.coverProjection s e).toLinearMap he.1 α hα
  have hnonzero : displacementSpace α.range ≠ ⊥ := by
    intro heq
    rw [heq,finrank_bot] at hdim
    omega
  obtain ⟨v,hv,hv0⟩ := (displacementSpace α.range).ne_bot_iff.mp hnonzero
  have hZaX : Z R a ≤ X R a := geometry.omega_bound a path.start_color
    (lt_of_lt_of_eq hpos (geometry.distance_constant a path.start_color).symm)
  have hcomm : Q R a ≤ centralizer ((⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
    (Q_le_centralizer_X R a).trans (centralizer_le
      ((CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path).trans hZaX))
  let d : L (K := F.Carrier) ≃* Sp F.Carrier :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top (by omega : 2 < Nat.card F.Carrier))).trans
      Subgroup.topEquiv
  have hinner (x : Q R a) : κ (inclusion hQAZ x) ∈ (pResidual 2 M).map q := by
    apply SymplecticNaturalNormalizer.mem_component_of_fixes_field_line
      ((pResidual 2 M).map q) (hC ▸ bot_le) (by omega) (e.groupEquiv.trans d)
      (MovedSection.ambientAction s e)
      (fun b w => MovedSection.ambientAction_component s e b w) _ v hv0
    intro c
    obtain ⟨w,hw,hwv⟩ := hlifts (c • v) ((displacementSpace α.range).smul_mem c hv)
    have hwfix : s.space.toRepresentation (κ (inclusion hQAZ x)) w = w := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hconj]
      change (x:FreeAmalgam R) * j (Multiplicative.ofAdd w) * (x:FreeAmalgam R)⁻¹ = _
      rw [←hcomm x.property _ hw,mul_inv_cancel_right]
    rw [←hwv]
    change MovedSection.ambientAction s e (κ (inclusion hQAZ x))
      (MovedSection.coverProjection s e w) = MovedSection.coverProjection s e w
    rw [←MovedSection.coverProjection_ambient s e,hwfix]
  let f : Q R a →* Sp F.Carrier := (commutator (Sp F.Carrier)).subtype.comp
    (e.groupEquiv.toMonoidHom.comp ((κ.comp (inclusion hQAZ)).codRestrict _ hinner))
  refine ⟨F,hF,f,?_,?_⟩
  · apply restricted_kernel_map (Q R a) (stabilizer R z) (Q R z) hQAZ κ hκQ f
    intro u
    exact marking_eq_one ((pResidual 2 M).map q) (commutator (Sp F.Carrier)) e.groupEquiv
      ⟨κ (inclusion hQAZ u),hinner u⟩
  · intro u hu
    let x : Z R a := ⟨u,hu⟩
    have hfu : f u = α x := by
      apply congrArg (commutator (Sp F.Carrier)).subtype
      apply e.groupEquiv.symm.injective
      change e.groupEquiv.symm (e.groupEquiv ⟨κ (inclusion hQAZ u),hinner u⟩) = e.groupEquiv.symm (β x)
      rw [e.groupEquiv.symm_apply_apply]
      apply Subtype.ext
      exact (hβmark x).symm
    rw [hfu]
    calc
      Module.finrank F.Carrier (InvolutionTypes.movedSpace (α x)) ≤
          Module.finrank F.Carrier (displacementSpace α.range) := Submodule.finrank_mono (by
        rintro w ⟨v,rfl⟩
        exact Coinvariants.sub_mem_ker
          (ρ := (symplecticNatural 2).comp α.range.subtype) ⟨α x,⟨x,rfl⟩⟩ v)
      _ = 1 := hdim
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
