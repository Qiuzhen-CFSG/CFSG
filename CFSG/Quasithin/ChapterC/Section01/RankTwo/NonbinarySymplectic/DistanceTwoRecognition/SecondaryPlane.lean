module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SecondaryKernel
public import Theory.Representation.SymplecticFourOrthogonalCover.SecondaryPlane

/-!
# Secondary component movement in the inner-edge branch

An actual inner action of the common edge two-group on the opposite natural
cover supplies a compatible self-orthogonal plane. Its full preimage has
edge-fixed displacement, hence displacement in the literal edge omega-center.
Maximality puts that preimage in the secondary seed. The earlier full-kernel
and normal-closure arguments now prove nontrivial component action on A/Z,
with the original quotient maps and at the original field degree.

The application to the characteristic replacement retains the precise inner-
edge premise. The source condition M=M* implies it via the actual residual
and two-core embeddings. The weaker inner action of Q_a alone does not imply
it: over F4, a unipotent actor with an edge Frobenius has secondary preimage
only its fixed line. This local diagnostic does not refute the full MS input.

Source: MS93 (3.6), printed p.871, after the (3.4) reduction M=M*, and
Aschbacher--Smith I.2.3, printed p.413. Discharging that reduction, the paired
secondary-orbit contradiction, whole-core bound and (3.7) field restriction
remain necessary for the distance-two recognition theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
open Representation.SymplecticFourOrthogonalCover
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open ChapterB.QuasisimpleSource MSCentralOrbit
section Plane
variable {M E W : Type*} [Group M] [Finite M]
  [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {R : Subgroup M} {g : Geometry R} {a z t : Vertex R}

omit [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] in
private theorem edge_isPGroup (hR : IsPGroup 2 R) (ht : color R t = true) :
    IsPGroup 2 (Q R t) := by
  have hex : ∃ v, t = hVertex R v := by
    cases t with
    | inl q =>
      change false = true at ht
      cases ht
    | inr q =>
      induction q using Quotient.inductionOn
      exact ⟨_,rfl⟩
  obtain ⟨v,rfl⟩ := hex
  have he := Q_act R v (beta R)
  simp only [beta,act_hVertex,one_mul] at he
  rw [he]
  change IsPGroup 2 ((Q R (beta R)).map _)
  rw [Q_beta]
  exact (hR.map (embedM R)).map _

private theorem secondary_plane_from_edge_cover
    (hR : IsPGroup 2 R) (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (σ : Representation (ZMod 2) (L (K := E)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := E))) (hp : IsCover p)
    (j : Multiplicative W →* FreeAmalgam R) (hjr : j.range = U R z)
    (β : Q R t →* L (K := E))
    (hβ : ∀ (u : Q R t) (w : W), j (Multiplicative.ofAdd (σ (β u) w)) =
      u.val*j (Multiplicative.ofAdd w)*u.val⁻¹) :
    ∃ P : Submodule E (Vector E), (form E).orthogonal P = P ∧
      ∀ w : W, p w ∈ P → j (Multiplicative.ofAdd w) ∈ Sp4Four.secondarySeed R a t z := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQt := edge_isPGroup hR ht
  have hβp := hQt.of_surjective β.rangeRestrict β.rangeRestrict_surjective
  obtain ⟨P,hP,hdisp⟩ := exists_plane_with_fixed_cover_displacement p hp β.range hβp
  let D : Subgroup (FreeAmalgam R) :=
    ((((P.restrictScalars (ZMod 2)).comap p.toLinearMap).toAddSubgroup).toSubgroup).map j
  have hDU : D ≤ U R z := hjr ▸ map_le_range j _
  have hUQt : U R z ≤ Q R t :=
    ((U_le_Z z).trans ((g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]
      change 0 < g.b R
      omega)).trans (omegaCenter_le _))).trans (Q_le_adjacent_h R ht hzt)
  let := g.Z_elementary (by omega : 0 < g.b R) z path.end_color
  have hDQt : ⁅D,Q R t⁆ ≤ Z R t := by
    rw [commutator_comm]
    apply commutator_le.mpr
    rintro u hu y ⟨w,hw,rfl⟩
    change p w.toAdd ∈ P at hw
    let δ := σ (β ⟨u,hu⟩) w.toAdd-w.toAdd
    have hd : δ ∈ Representation.OneCohomology.fixed (σ.comp β.range.subtype) := hdisp _ ⟨⟨u,hu⟩,rfl⟩ _ hw
    have he : j (Multiplicative.ofAdd δ) = ⁅u,j w⁆ := by
      dsimp only [δ]
      rw [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,hβ]
      rfl
    rw [←he]
    have hdU : j (Multiplicative.ofAdd δ) ∈ U R z := hjr ▸ ⟨_,rfl⟩
    change j (Multiplicative.ofAdd δ) ∈ Z R t
    simp only [Z,ht,Bool.true_eq_false,↓reduceIte,edgeOmega]
    apply mem_omegaCenter_iff.mpr
    refine ⟨hUQt hdU,elemPow_eq_one_of_isElementaryAbelian _ (U_le_Z z hdU),?_⟩
    intro v hv
    have hh := congrArg (fun w => j (Multiplicative.ofAdd w)) (hd ⟨β ⟨v,hv⟩,⟨⟨v,hv⟩,rfl⟩⟩)
    change j (Multiplicative.ofAdd (σ (β ⟨v,hv⟩) δ)) = j (Multiplicative.ofAdd δ) at hh
    rw [hβ] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hDY : D ≤ Sp4Four.secondarySeed R a t z :=
    (Sp4Four.secondarySeed_greatest R g path.end_color hzt (by omega)).2.2 D
      (hDU.trans (U_le_Z z))
      ((commutator_mono le_rfl (Q_le_adjacent_h R ht hat)).trans hDQt)
  refine ⟨P,hP,?_⟩
  intro w hw
  exact hDY (mem_map_of_mem j (show Multiplicative.ofAdd w ∈
    (((P.restrictScalars (ZMod 2)).comap p.toLinearMap).toAddSubgroup).toSubgroup from hw))

private theorem secondary_cover_projection
    (hR : IsPGroup 2 R) (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (σ : Representation (ZMod 2) (L (K := E)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := E))) (hp : IsCover p)
    (j : Multiplicative W →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range = U R z)
    (β : Q R t →* L (K := E))
    (hβ : ∀ (u : Q R t) (w : W), j (Multiplicative.ofAdd (σ (β u) w)) =
      u.val*j (Multiplicative.ofAdd w)*u.val⁻¹)
    (hker : ∀ w : W, p w = 0 ↔
      j (Multiplicative.ofAdd w) ∈ centralizer (Ltilde R z : Set (FreeAmalgam R))) :
    ∃ (π : U R z →* Multiplicative (Vector E)) (α : Q R a →* Sp E)
      (P : Submodule E (Vector E)),
      (∀ (u : Q R a) (v : U R z) (hv : u.val*v.val*u.val⁻¹ ∈ U R z),
        π ⟨u.val*v.val*u.val⁻¹,hv⟩ = Multiplicative.ofAdd (α u • (π v).toAdd)) ∧
      π.ker.map (U R z).subtype = U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) ∧
      (form E).orthogonal P = P ∧
      (∀ v ∈ P, ∃ y : (Sp4Four.secondarySeed R a t z ⊓ U R z : Subgroup (FreeAmalgam R)),
        (π ⟨y.val,y.property.2⟩).toAdd = v) := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have htS : Q R t ≤ stabilizer R z := by
    rw [Q_h_eq_edge R ht hzt]
    exact inf_le_left
  have hn : Q R t ≤ normalizer (U R z) := htS.trans (U_normalized z)
  obtain ⟨π,hπ,hπj,hact⟩ := exists_equivariant_embedded_projection
    (U R z) (Q R t) hn σ (binaryNatural (K := E)) j hj hjr p.toLinearMap
    hp.1 (fun b w => LinearMap.congr_fun (p.isIntertwining' b) w) β hβ
  have hπker : π.ker.map (U R z).subtype =
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
    have hv (u : U R z) : π u = 1 ↔
        u.val ∈ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
      obtain ⟨w,hw⟩ := (show u.val ∈ j.range from hjr.symm ▸ u.property)
      have hu : u = ⟨j w,by rw [←hjr]; exact ⟨w,rfl⟩⟩ := Subtype.ext hw.symm
      rw [hu]
      exact (Iff.of_eq (congrArg (fun v => v = 1) (hπj w.toAdd))).trans (hker w.toAdd)
    ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u.property,(hv u).mp hu⟩
    · rintro ⟨hxu,hxc⟩
      exact ⟨⟨x,hxu⟩,(hv ⟨x,hxu⟩).mpr hxc,rfl⟩
  obtain ⟨P,hP,hlift⟩ := secondary_plane_from_edge_cover hR path hb hat hzt σ p hp j hjr β hβ
  let α := (commutator (Sp E)).subtype.comp (β.comp (inclusion (Q_le_adjacent_h R ht hat)))
  refine ⟨π,α,P,(fun u v _ => hact (inclusion (Q_le_adjacent_h R ht hat) u) v),hπker,hP,?_⟩
  intro v hv
  obtain ⟨w,hw⟩ := hp.1 v
  refine ⟨⟨j (Multiplicative.ofAdd w),hlift w (hw.symm ▸ hv),hjr ▸ ⟨_,rfl⟩⟩,?_⟩
  exact (congrArg Multiplicative.toAdd (hπj w)).trans hw

end Plane

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The source's inner-edge branch supplies the actual marked plane and hence
nontrivial component action on the secondary quotient. The entire projection
kernel is retained; the inner-edge premise is not inferred from the weaker
opposite-kernel containment. -/
theorem replacement_secondary_moves_of_inner_edge
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    (hinner : Q d.radical t ≤ Ltilde d.radical z ⊔ Q d.radical z) :
    ¬ ⁅Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z),
      Ltilde d.radical a⁆ ≤ Z d.radical a := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,hecov,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.end_color
  let S := stabilizer d.radical z
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all [path.start_color]
  have htS : Q d.radical t ≤ S := by
    rw [Q_h_eq_edge d.radical ht hzt]
    exact inf_le_left
  have hk : κ.ker = (Q d.radical z).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [hκQ,map_subgroupOf_eq_of_le (show Q d.radical z ≤ S from fun _ hx => hx.1)]
  have hpre : (replacementComponent d).comap κ =
      (Ltilde d.radical z ⊔ Q d.radical z).subgroupOf S := by
    rw [←hκL,comap_map_eq,hk,subgroupOf_sup (Ltilde_le_stabilizer z)
      (show Q d.radical z ≤ S from fun _ hx => hx.1)]
  let δ := κ.comp (inclusion htS)
  have hδ (u : Q d.radical t) : δ u ∈ replacementComponent d := by
    change inclusion htS u ∈ (replacementComponent d).comap κ
    rw [hpre]
    exact hinner u.property
  let β := e.groupEquiv.toMonoidHom.comp (δ.codRestrict _ hδ)
  have hmark (u : Q d.radical t) : (e.groupEquiv.symm (β u) : _) = δ u := by
    change (e.groupEquiv.symm (e.groupEquiv ⟨δ u,hδ u⟩) : _) = δ u
    rw [e.groupEquiv.symm_apply_apply]
  have hβ (u : Q d.radical t) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (β u) w)) =
        u.val*j (Multiplicative.ofAdd w)*u.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation (e.groupEquiv.symm (β u)) w)) = _
    exact (congrArg (fun b => j (Multiplicative.ofAdd (s.space.toRepresentation b w)))
      (hmark u)).trans (hconj (inclusion htS u) w)
  obtain ⟨π,α,P,hact,hπker,hP,hcover⟩ := secondary_cover_projection
    (replacement_isPGroup h d) path hb hat hzt (MovedSection.coverAction s e)
    (MovedSection.coverProjection s e) hecov j hj hjr β hβ hker
  exact replacement_secondary_moves_of_moving_plane h d path hb hat hzt hlarge
    π α hact hπker P hP hcover


/-- Apply the constructed plane to the literal secondary quotient and its
original component marking. In the inner-edge branch the nontrivial component
action is now proved along with the earlier quadratic and codimension bounds. -/
theorem replacement_secondary_section_of_inner_edge
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    (hinner : Q d.radical t ≤ Ltilde d.radical z ⊔ Q d.radical z) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    let := replacement_secondary_quotient_normal h d path hb hat hzt hlarge
    let := replacement_secondary_quotient_elementary h d path hb hat hzt hlarge
    ∃ (κ : stabilizer d.radical a →* (d.overgroup ⧸ pCore 2 d.overgroup)),
      Function.Surjective κ ∧
      κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
      ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ =
        replacementComponent d ∧
      ∃ (σ : Representation (ZMod 2) (d.overgroup ⧸ pCore 2 d.overgroup)
          (Additive (A ⧸ (Z d.radical a).subgroupOf A)))
        (c : BinaryConjugationSection (stabilizer d.radical a) A (Z d.radical a) (σ.comp κ)),
        (∀ u : A, (c.coordinates u).toAdd =
          Additive.ofMul (QuotientGroup.mk' ((Z d.radical a).subgroupOf A) u)) ∧
        Representation.BinaryOffender.IsQuadratic σ
          ((A'.subgroupOf (stabilizer d.radical a)).map κ) ∧
        Representation.BinaryOffender.fixedCodim σ
          ((A'.subgroupOf (stabilizer d.radical a)).map κ) ≤ 2*n ∧
        ∃ b : replacementComponent d, ∃ v, σ b.val v ≠ v := by
  let := replacement_secondary_quotient_normal h d path hb hat hzt hlarge
  let := replacement_secondary_quotient_elementary h d path hb hat hzt hlarge
  obtain ⟨κ,hκ,hk,hL,σ,c,hc,hquad,hcodim⟩ :=
    replacement_secondary_section h d path hb hat hzt hlarge
  refine ⟨κ,hκ,hk,hL,σ,c,hc,hquad,hcodim,?_⟩
  exact secondary_component_action_nontrivial d κ (replacementComponent d) hL σ c
    (replacement_secondary_moves_of_inner_edge h d path hb hat hzt hlarge hinner)


omit [Finite F] [CharP F 2] in
/-- The source condition M=M* gives the required inner action of the whole
edge, through the actual graph embeddings of the residual and two-core. -/
theorem replacement_inner_edge_of_component_core
    {z t : Vertex d.radical} (hz : color d.radical z = false)
    (hzt : Adjacent d.radical z t)
    (hwhole : K.subgroupOf d.overgroup ⊔ pCore 2 d.overgroup = ⊤) :
    Q d.radical t ≤ Ltilde d.radical z ⊔ Q d.radical z := by
  obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ :=
    Sp4Four.SourceComparison.vertex_coordinates_with_kernel d.radical
      (replacement_isPGroup h d) (replacement_core_le h d) hz
  have he : Ltilde d.radical z ⊔ Q d.radical z = stabilizer d.radical z := by
    rw [←hiL,←hiQ,←Subgroup.map_sup,replacement_residual h d,hwhole,
      ←MonoidHom.range_eq_map,hir]
  rw [he]
  intro u hu
  exact hu.2 z (adjacent_symm d.radical hzt)

/-- The whole-component replacement branch now has nontrivial secondary
component action, with no plane, fixed-kernel or displacement premise. -/
theorem replacement_secondary_moves_of_component_core
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    (hwhole : K.subgroupOf d.overgroup ⊔ pCore 2 d.overgroup = ⊤) :
    ¬ ⁅Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z),
      Ltilde d.radical a⁆ ≤ Z d.radical a :=
  replacement_secondary_moves_of_inner_edge h d path hb hat hzt hlarge
    (replacement_inner_edge_of_component_core h d path.end_color hzt hwhole)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
