module
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalRootCoordinates
public import Theory.Representation.SymplecticNaturalNormalizer.FixedLineInner

/-!
# The original local core actor at a critical root

At any critical distance, a subgroup of Q_a that fixes the opposite vertex
centralizes the critical commutator. When the two critical images have order
four, that commutator covers a nonzero natural field line. Field-line rigidity
therefore puts the actor in the symplectic component. The construction retains
the exact intersection with Q_z and the natural conjugation action, including
its full central kernel.

The original truncated radius kernel is the consumer in
GenerationTwoSymplecticRootRadius. If its image has the order of the original
critical root, equality of the two images puts its displacement in Z_a. This
supplies a backward critical path on the original geometry. No assertion that
all of Q_a fixes the opposite vertex is made beyond distance two.
Source: MS93 (3.3), p.867, and the kernel in (5.7), p.919.
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

/-- A local subgroup of the original starting core acts internally on the
opposite root module, with its entire kernel and natural action retained. -/
theorem original_core_actor_root_action
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
    (path : CriticalPath R geometry a z) (hpos : 0 < geometry.b R)
    (ha4 : (Q R z).relIndex (Z R a) = 4)
    (hz4 : (Q R a).relIndex (Z R z) = 4)
    (Y : Subgroup (FreeAmalgam R)) (hYQ : Y ≤ Q R a)
    (hYZ : Y ≤ stabilizer R z) :
    ∃ F : BinaryField, F.degree = 2 ∧
      ∃ f : Y →* Sp F.Carrier,
        f.ker = (Q R z).subgroupOf Y ∧
        (∀ u : Y, (u:FreeAmalgam R) ∈ Z R a →
          Module.finrank F.Carrier (InvolutionTypes.movedSpace (f u)) ≤ 1) ∧
        ∃ π : U R z →* Multiplicative (Vector F.Carrier), Function.Surjective π ∧
          (∀ u : U R z, π u = 1 ↔
            (u : FreeAmalgam R) ∈ centralizer (Ltilde R z : Set _)) ∧
          (∀ (y : Y) (u : U R z),
            π ⟨y.val*u.val*y.val⁻¹,
              (mem_normalizer_iff.mp (U_normalized z (hYZ y.property)) u.val).mp u.property⟩ =
              Multiplicative.ofAdd (f y • (π u).toAdd)) := by
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 M)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 M)) q hq hk) ((pResidual 2 M).map q)
  obtain ⟨F,hF,e,he,j,hj,hjr,κ,_hκ,hκQ,_hκC,_hκL,_hψ,hconj,_hproj,hker⟩ :=
    ambient_initial_cover_at_vertex R hms hp hne hQR hself hfaith q hq hcore
      hc hC hsq path.end_color
  have hFc : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  have hAZ : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
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
  have hinner (x : Y) : κ (inclusion hYZ x) ∈ (pResidual 2 M).map q := by
    apply SymplecticNaturalNormalizer.mem_component_of_fixes_field_line
      ((pResidual 2 M).map q) (hC ▸ bot_le) (by omega) (e.groupEquiv.trans d)
      (MovedSection.ambientAction s e)
      (fun b w => MovedSection.ambientAction_component s e b w) _ v hv0
    intro c
    obtain ⟨w,hw,hwv⟩ := hlifts (c • v) ((displacementSpace α.range).smul_mem c hv)
    have hwfix : s.space.toRepresentation (κ (inclusion hYZ x)) w = w := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hconj]
      change (x:FreeAmalgam R) * j (Multiplicative.ofAdd w) * (x:FreeAmalgam R)⁻¹ = _
      rw [←hcomm (hYQ x.property) _ hw,mul_inv_cancel_right]
    rw [←hwv]
    change MovedSection.ambientAction s e (κ (inclusion hYZ x))
      (MovedSection.coverProjection s e w) = MovedSection.coverProjection s e w
    rw [←MovedSection.coverProjection_ambient s e,hwfix]
  let f : Y →* Sp F.Carrier := (commutator (Sp F.Carrier)).subtype.comp
    (e.groupEquiv.toMonoidHom.comp ((κ.comp (inclusion hYZ)).codRestrict _ hinner))
  refine ⟨F,hF,f,?_,?_,?_⟩
  · have hm : f.ker.map Y.subtype = Y ⊓ Q R z := by
      apply restricted_kernel_map Y (stabilizer R z) (Q R z) hYZ κ hκQ f
      intro u
      exact marking_eq_one ((pResidual 2 M).map q) (commutator (Sp F.Carrier)) e.groupEquiv
        ⟨κ (inclusion hYZ u),hinner u⟩
    rw [←subgroupOf_map_subtype_eq f.ker,hm,inf_subgroupOf_left]
  · intro u hu
    let x : Z R a := ⟨u,hu⟩
    have hfu : f u = α x := by
      apply congrArg (commutator (Sp F.Carrier)).subtype
      apply e.groupEquiv.symm.injective
      change e.groupEquiv.symm (e.groupEquiv ⟨κ (inclusion hYZ u),hinner u⟩) = e.groupEquiv.symm (β x)
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
  · obtain ⟨π,hπ,hπj,hπact⟩ := exists_equivariant_embedded_projection
      (U R z) Y (hYZ.trans (U_normalized z)) s.space.toRepresentation
      (MovedSection.ambientAction s e) j hj hjr
      (MovedSection.coverProjection s e).toLinearMap he.1
      (MovedSection.coverProjection_ambient s e) (κ.comp (inclusion hYZ))
      (fun y w => hconj (inclusion hYZ y) w)
    refine ⟨π,hπ,?_,?_⟩
    · intro u
      obtain ⟨w,hw⟩ := (show u.val ∈ j.range from hjr.symm ▸ u.property)
      have heq : (⟨j (Multiplicative.ofAdd w.toAdd),by rw [←hjr]; exact ⟨_,rfl⟩⟩ : U R z) = u :=
        Subtype.ext hw
      have hπw := hπj w.toAdd
      rw [heq] at hπw
      rw [hπw]
      change MovedSection.coverProjection s e w.toAdd = 0 ↔ _
      rw [hker]
      exact hw ▸ Iff.rfl
    · intro y u
      rw [hπact]
      exact congrArg Multiplicative.ofAdd
        (MovedSection.ambientAction_component s e
          (⟨κ (inclusion hYZ y),hinner y⟩ : (pResidual 2 M).map q) (π u).toAdd)

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison

namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open scoped commutatorElement
variable {M A : Type*} [Group M] [Group A] [Finite A]
  {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}

/-- If the truncated actor has no more images than the critical root, its
whole action differs from that root only by the literal opposite two-core. -/
theorem critical_displacement_of_root_image_bound
    (path : CriticalPath R geometry a z)
    (Y : Subgroup (FreeAmalgam R)) (hYQ : Y ≤ Q R a) (hZY : Z R a ≤ Y)
    (f : Y →* A) (hf : f.ker = (Q R z).subgroupOf Y)
    (ha4 : (Q R z).relIndex (Z R a) = 4)
    (hsmall : (Q R z).relIndex Y ≤ 4) :
    ⁅Y,Z R z⁆ ≤ Z R a := by
  let g : Z R a →* A := f.comp (inclusion hZY)
  have hg : g.ker = (Q R z).subgroupOf (Z R a) := by
    ext x
    change f (inclusion hZY x) = 1 ↔ x.val ∈ Q R z
    change inclusion hZY x ∈ f.ker ↔ x.val ∈ Q R z
    rw [hf]
    rfl
  have hgc : Nat.card g.range = 4 := by
    rw [←index_ker,hg]
    exact ha4
  have hfc : Nat.card f.range ≤ 4 := by
    rw [←index_ker,hf]
    exact hsmall
  have heq : g.range = f.range := eq_of_le_of_card_ge
    (by rintro _ ⟨x,rfl⟩; exact ⟨inclusion hZY x,rfl⟩) (by omega)
  have hjoin : Y ≤ Z R a ⊔ (Y ⊓ Q R z) := by
    intro y hy
    have hfy : f ⟨y,hy⟩ ∈ g.range := heq ▸ (show f ⟨y,hy⟩ ∈ f.range from ⟨_,rfl⟩)
    obtain ⟨x,hx⟩ := hfy
    let k : Y := (inclusion hZY x)⁻¹ * ⟨y,hy⟩
    have hk : k ∈ f.ker := by
      change f k = 1
      simp only [k,map_mul,map_inv]
      change (g x)⁻¹ * f ⟨y,hy⟩ = 1
      rw [hx,inv_mul_cancel]
    have hkz : (k : FreeAmalgam R) ∈ Q R z := by rwa [hf] at hk
    have hm : (x : FreeAmalgam R) * (k : FreeAmalgam R) ∈ Z R a ⊔ (Y ⊓ Q R z) :=
      mul_mem (mem_sup_left x.property) (mem_sup_right ⟨k.property,hkz⟩)
    change (x : FreeAmalgam R) * ((x : FreeAmalgam R)⁻¹ * y) ∈ _ at hm
    simpa only [mul_inv_cancel_left] using hm
  have hnorm : Q R a ≤ normalizer (Z R a : Set (FreeAmalgam R)) :=
    (show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (Z_normalized R a)
  have hcomm : ⁅Y ⊓ Q R z,Z R z⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact inf_le_right.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color)))
  exact (commutator_mono hjoin le_rfl).trans
    (commutator_sup_le_of_relative_normal (Q R a) (Z R a) (Y ⊓ Q R z) (Z R z) (Z R a)
      hnorm (hZY.trans hYQ) (inf_le_left.trans hYQ)
      (ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path)
      (hcomm ▸ bot_le))
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

