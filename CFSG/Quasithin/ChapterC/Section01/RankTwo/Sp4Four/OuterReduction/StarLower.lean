module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.SeedMovement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.ReciprocalCoordinates
public import Theory.Representation.SymplecticNaturalNormalizer.RootHyperplaneImage
public import Theory.Representation.ConjugationFixedSubspace
public import Theory.Representation.SemilinearHyperplaneIndex

/-!
# The critical endpoint intersection has moving index at least four

If an endpoint actor fixed the natural root hyperplane, its image would lie
in the original root. Matching it with an element of the original start
layer leaves an element of the literal endpoint centralizer. Consequently
an actor moving the endpoint intersection must move the root hyperplane.

The field-four semilinear bound gives fixed index at least four on that
three-dimensional hyperplane. All its lifts lie in the original intersection;
projected centralizers therefore give the same lower bound there. No splitting
of central attachments or invariance of the hyperplane is required.

Source: Meierfrankenfeld--Stellmacher (1993), (3.4), printed p.868. The
original source specialization is in StarLowerSource.
-/
public section
noncomputable section
open Subgroup Representation Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open ChapterB.QuasisimpleSource Representation.SymplecticFourOrthogonalCover SourceComparison
variable {H J V F : Type*} [Group H] [Finite H] [Group J]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
  {R : Subgroup H} {geometry : Geometry R} {a z : Vertex R}

omit [Finite H] [FiniteDimensional (ZMod 2) V] in
theorem critical_hyperplane_moved_of_intersection_moved
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hCa : C R a = Q R a) (hF : 2 < Nat.card F)
    (s : MovedSection ρ B)
    (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (hcent : centralizer (B : Set J) = ⊥)
    (κ : stabilizer R z →* J)
    (hκC : κ.ker.map (stabilizer R z).subtype = C R z)
    (β : Z R a →* L (K := F))
    (hAZ : Z R a ≤ stabilizer R z)
    (hβmark : ∀ x : Z R a, (e.groupEquiv.symm (β x) : J)=κ (inclusion hAZ x))
    (hd : Module.finrank F (displacementSpace (β.range.map (commutator (Sp F)).subtype))=1)
    (hc : Nat.card β.range=Nat.card F)
    (Y : Subgroup (FreeAmalgam R)) (hYZ : Y ≤ stabilizer R z)
    (hmove : ¬ Y ≤ centralizer ((Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _)) :
    ∃ y : Y, ∃ v : TwoLocalCover.fixedSpace (β.range.map (commutator (Sp F)).subtype),
      MovedSection.ambientAction s e (κ (inclusion hYZ y)) v.val ≠ v.val := by
  let ψ := MovedSection.ambientAction s e
  let d : L (K := F) ≃* Sp F :=
    (MulEquiv.subgroupCongr
      (OneCohomology.SymplecticFour.LargeField.commutator_eq_top hF)).trans Subgroup.topEquiv
  let : IsElementaryAbelian 2 (Z R a) := geometry.Z_elementary hb a path.start_color
  have hP : IsPGroup 2 β.range :=
    (IsElementaryAbelian.isPGroup 2 (Z R a)).of_surjective β.rangeRestrict β.rangeRestrict_surjective
  by_contra! hfixed
  apply hmove
  intro y hy u hu
  obtain ⟨t,ht,he⟩ := SymplecticNaturalNormalizer.mem_root_image_of_fixes_natural_hyperplane
    B (hcent ▸ bot_le) hF (e.groupEquiv.trans d) ψ
    (fun b v => MovedSection.ambientAction_component s e b v)
    β.range hP hd hc (κ (inclusion hYZ ⟨y,hy⟩))
    (fun v hv => hfixed ⟨y,hy⟩ ⟨v,hv⟩)
  obtain ⟨x,rfl⟩ := ht
  have hx : κ (inclusion hAZ x) = κ (inclusion hYZ ⟨y,hy⟩) := by
    rw [←hβmark x]
    exact he
  let c : stabilizer R z := (inclusion hAZ x)⁻¹ * inclusion hYZ ⟨y,hy⟩
  have hc : c ∈ κ.ker := by
    change κ c=1
    simp only [c,map_mul,map_inv,hx,inv_mul_cancel]
  have hcC : (c : FreeAmalgam R) ∈ C R z := by
    rw [←hκC]
    exact ⟨c,hc,rfl⟩
  have huc : Commute u (c : FreeAmalgam R) := hcC.2 u hu.1
  have hux : Commute u (x : FreeAmalgam R) := by
    have huC : u ∈ C R a := hCa.symm ▸ hu.2
    exact (huC.2 x x.property).symm
  have hyc : y = (x : FreeAmalgam R) * (c : FreeAmalgam R) := by
    change y = (x : FreeAmalgam R) * ((x : FreeAmalgam R)⁻¹ * y)
    simp
  rw [hyc]
  exact hux.mul_right huc

theorem four_le_critical_intersection_centralizer_index
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hCa : C R a = Q R a) (hF : Nat.card F = 4)
    (s : MovedSection ρ B)
    (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hcent : centralizer (B : Set J) = ⊥)
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range = U R z)
    (κ : stabilizer R z →* J)
    (hκC : κ.ker.map (stabilizer R z).subtype = C R z)
    (hκ : ∀ x : stabilizer R z, ∀ w : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (κ x) w)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd w) * (x : FreeAmalgam R)⁻¹)
    (β : Z R a →* L (K := F))
    (hAZ : Z R a ≤ stabilizer R z)
    (hβmark : ∀ x : Z R a, (e.groupEquiv.symm (β x) : J)=κ (inclusion hAZ x))
    (hβ : ∀ x : Z R a, ∀ w : s.space.toSubmodule,
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (β x) w)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd w) * (x : FreeAmalgam R)⁻¹)
    (hd : Module.finrank F (displacementSpace (β.range.map (commutator (Sp F)).subtype))=1)
    (hc : Nat.card β.range=Nat.card F)
    (Y : Subgroup (FreeAmalgam R)) (hYZ : Y ≤ stabilizer R z)
    (hmove : ¬ Y ≤ centralizer ((Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _)) :
    4 ≤ (centralizer (Y : Set (FreeAmalgam R))).relIndex (Z R z ⊓ Q R a) := by
  let ψ := MovedSection.ambientAction s e
  let σ := MovedSection.coverAction s e
  let p := MovedSection.coverProjection s e
  let δ : Y →* J := κ.comp (inclusion hYZ)
  let P := TwoLocalCover.fixedSpace (β.range.map (commutator (Sp F)).subtype)
  let W := OneCohomology.fixed (σ.comp β.range.subtype)
  let D := (BinaryOffender.fixedSpace ψ δ.range).comap (P.restrictScalars (ZMod 2)).subtype
  have hWP (w : s.space.toSubmodule) : w ∈ W ↔ p w ∈ P := by
    change w ∈ OneCohomology.fixed (σ.comp β.range.subtype) ↔ p w ∈ P
    rw [cover_fixed_preimage p hp]
    constructor
    · intro hw g hg
      obtain ⟨t,ht,rfl⟩ := hg
      exact hw ⟨t,ht⟩
    · intro hw t
      exact hw t.val.val (mem_map_of_mem _ t.property)
  let pP : W →ₗ[ZMod 2] P := (p.toLinearMap.comp W.subtype).codRestrict
    (P.restrictScalars (ZMod 2)) (fun w => (hWP w.val).mp w.property)
  have hpP : Function.Surjective pP := by
    intro v
    obtain ⟨w,hw⟩ := hp.1 v.val
    refine ⟨⟨w,(hWP w).mpr (hw ▸ v.property)⟩,?_⟩
    exact Subtype.ext hw
  let jW : Multiplicative W →* FreeAmalgam R :=
    j.comp W.subtype.toAddMonoidHom.toMultiplicative
  have hZA : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant z path.end_color]
  have hWE : jW.range ≤ Z R z ⊓ Q R a := by
    rintro _ ⟨w,rfl⟩
    have hU : jW w ∈ U R z := by
      rw [←hjr]
      exact ⟨Multiplicative.ofAdd w.toAdd.val,rfl⟩
    refine ⟨U_le_Z z hU,?_⟩
    rw [←hCa]
    refine ⟨hZA (U_le_Z z hU),?_⟩
    intro x hx
    have he := w.toAdd.property (⟨β ⟨x,hx⟩,⟨⟨x,hx⟩,rfl⟩⟩ : β.range)
    change σ (β ⟨x,hx⟩) w.toAdd.val=w.toAdd.val at he
    have hh := hβ ⟨x,hx⟩ w.toAdd.val
    rw [he] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh.symm
  have hcentral (w : W)
      (hw : jW (Multiplicative.ofAdd w) ∈ centralizer (Y : Set (FreeAmalgam R))) :
      pP w ∈ D := by
    rintro ⟨g,⟨y,rfl⟩⟩
    change ψ (κ (inclusion hYZ y)) (p w.val) = p w.val
    rw [←MovedSection.coverProjection_ambient s e]
    apply congrArg p
    apply Multiplicative.ofAdd.injective
    apply hj
    rw [hκ]
    have he := hw y.val y.property
    change y.val * j (Multiplicative.ofAdd w.val) =
      j (Multiplicative.ofAdd w.val) * y.val at he
    change y.val * j (Multiplicative.ofAdd w.val) * y.val⁻¹ = _
    rw [he,mul_inv_cancel_right]
  have hdim : 2 ≤ Module.finrank F P := by
    have hdim' : Module.finrank F (TwoLocalCover.fixedSpace
        (β.range.map (commutator (Sp F)).subtype)) = 3 := by
      rw [←orthogonal_displacementSpace,
        LinearMap.BilinForm.finrank_orthogonal TwoLocalCover.form_nondegenerate,hd]
      simp [Theory.SpecificGroups.SymplecticFour.Vector]
    exact hdim'.ge.trans' (by decide : 2 ≤ 3)
  obtain ⟨y,v,hv⟩ := critical_hyperplane_moved_of_intersection_moved path hb hCa
    (by omega) s e hcent κ hκC β hAZ hβmark hd hc Y hYZ hmove
  have hlo : 4 ≤ Nat.card (P ⧸ D) :=
    four_le_submodule_fixed_quotient_card_of_semilinear hF ψ δ.range P hdim
      (fun g _ => ambient_marking_semilinear hF s e g) ⟨δ y,⟨y,rfl⟩,v,hv⟩
  let := finite_Z R z
  let : Finite (Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  let : Finite W := Module.finite_of_finite (ZMod 2)
  exact hlo.trans (quotient_card_le_centralizer_index_of_projection
    (Z R z ⊓ Q R a) Y jW hWE pP hpP D hcentral)

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
