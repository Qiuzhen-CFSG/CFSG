module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.CriticalIntersections.Basic
public import Theory.Representation.BinaryConjugationSection.Projection
public import Theory.Representation.FirstCohomologyDuality.SimpleCover
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Displacement through the two source-dual sections

The supplied coordinates induce a surjective H-map from U/V₁ to
U/C_U(O₂(H)). Its kernel is the image of the literal centralizer. The
identity [U,O₂(H)]=V₁ and |V₁|=2 make this kernel proper. Simplicity of
the natural SL₂(4) quotient and the central-cover property then place it
inside the original natural projection's kernel.

A displacement disjoint from that kernel retains its rank on the quotient.
Contragredience, including inversion of the actor, and the supplied source
duality transport rank two to O₂(H)/C_{O₂(H)}(U). This excludes fixed
hyperplanes. The coordinate preimage of the fixed space is exactly the
literal commutator preimage, giving its relative index at least four.
The final applications retain Uα, its earlier placement, and the actual
H-actor lifting a marked upper element.

These are conditional transports of the earlier 14.5.21 datum. Construction
of that datum and selection of the critical actor belong to their source
assembly owners. The resulting lower bound is the input to the contradiction
with `dual_section_fixed_index_le_two_of_point_le` in `CriticalIntersections.Basic`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.5.21(1)–(2), printed pp.1019–1020; proof of 14.7.69, printed p.1072.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation Chapter12.Section08
open Representation.OneCohomology Representation.SL2FourNatural
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]
namespace CriticalIntersections
namespace DualSection

private theorem point_le_uKernel (d : Data T L V F W) :
    F.Vi 1 ≤ F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G) := by
  refine le_inf d.conjugationSection.kernel_le ?_
  rw [d.point]
  apply zpowers_le.mpr
  intro q hq
  exact ((show q ∈ centralizer ({d.z} : Set G) from
    d.centralizer_eq ▸ pCoreIn_le 2 F.H hq) d.z (Set.mem_singleton d.z)).symm

/-- The quotient map uses the supplied coordinates on both sections. -/
theorem exists_projection (d : Data T L V F W) (s : SourceDuality F X Y) :
    ∃ f : d.action.IntertwiningMap s.uAction,
      Function.Surjective f ∧
      (∀ v : F.U, f (d.conjugationSection.coordinates v).toAdd =
        (s.uSection.coordinates v).toAdd) ∧
      f.toLinearMap.ker = d.conjugationSection.imageSpace
        (F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G)) := by
  exact BinaryConjugationSection.exists_projection F.H F.H F.U (F.Vi 1)
    (F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G)) le_rfl (point_le_uKernel d)
    (MonoidHom.id F.H) (MonoidHom.id F.H) Function.surjective_id (MonoidHom.id F.H)
    (fun _ => rfl) d.action s.uAction d.conjugationSection s.uSection

private theorem proper_invariant_le_projection_ker (d : Data T L V F W)
    (hc : d.SectionCentralizer) (A : Submodule (ZMod 2) W)
    (hA : ∀ h w, w ∈ A → d.action h w ∈ A) (hne : A ≠ ⊤) :
    A ≤ d.projection.toLinearMap.ker := by
  let p := restrictedProjection d.naturalQuotient (d.descendedProjection hc)
  have hp : IsCover p := SL2FourCentralCover.isCover_of_natural_indecomposable p
    d.projection_onto (le_of_eq (d.descended_fixed_kernel hc))
    (d.descended_indecomposable hc)
  have hi : ∀ g w, w ∈ A →
      d.descendedAction hc (alternatingActor d.naturalQuotient g) w ∈ A := by
    intro g w hw
    obtain ⟨k, hk⟩ := d.alternatingActor_lift g
    rw [← hk, d.descendedAction_apply]
    exact hA k w hw
  have him : ∀ g v, v ∈ A.map p.toLinearMap →
      naturalRepresentation g v ∈ A.map p.toLinearMap := by
    rintro g _ ⟨w, hw, rfl⟩
    exact ⟨_, hi g w hw, LinearMap.congr_fun (p.isIntertwining' g) w⟩
  have hbot : A.map p.toLinearMap = ⊥ := by
    by_contra hn
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
    have ht : A.map p.toLinearMap = ⊤ := by
      apply top_unique
      intro w _
      by_cases hw : w = 0
      · exact hw ▸ (A.map p.toLinearMap).zero_mem
      obtain ⟨g, hg⟩ := transitive_nonzero v w hv0 hw
      exact hg ▸ him g v hv
    exact hne (invariant_eq_top_of_cover_image_eq_top p hp A hi ht)
  intro w hw
  have : p w ∈ A.map p.toLinearMap := ⟨w, hw, rfl⟩
  rw [hbot] at this
  exact this

/-- The centralizer image is killed by the original natural projection.
The earlier nontrivial commutator identity makes this image proper. -/
theorem projection_kernel_le (d : Data T L V F W) (hc : d.SectionCentralizer)
    (s : SourceDuality F X Y) (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (f : d.action.IntertwiningMap s.uAction)
    (hf : ∀ v : F.U, f (d.conjugationSection.coordinates v).toAdd =
      (s.uSection.coordinates v).toAdd) :
    f.toLinearMap.ker ≤ d.projection.toLinearMap.ker := by
  apply proper_invariant_le_projection_ker d hc
  · intro h w hw
    change f (d.action h w) = 0
    rw [show f (d.action h w) = s.uAction h (f w) from
      LinearMap.congr_fun (f.isIntertwining' h) w]
    change f w = 0 at hw
    rw [hw, map_zero]
  · intro ht
    have hcent : F.U ≤ centralizer (F.H.pCoreIn 2 : Set G) := by
      intro v hv
      have hz : f (d.conjugationSection.coordinates ⟨v, hv⟩).toAdd = 0 := by
        exact (show (d.conjugationSection.coordinates ⟨v, hv⟩).toAdd ∈
          f.toLinearMap.ker from ht ▸ Submodule.mem_top)
      rw [hf] at hz
      exact ((s.uSection.coordinates_eq_one_iff ⟨v, hv⟩).mp hz).2
    have hb : F.Vi 1 = ⊥ := hcomm.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr hcent)
    have hh : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    rw [hb, Subgroup.card_bot] at hh
    omega

/-- The centralizer image in U/V₁ lies in the original natural projection's kernel. -/
theorem centralizer_image_le_projection_ker (d : Data T L V F W)
    (hc : d.SectionCentralizer) (s : SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    d.conjugationSection.imageSpace (F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G)) ≤
      d.projection.toLinearMap.ker := by
  obtain ⟨f, _, hf, hk⟩ := exists_projection d s
  rw [← hk]
  exact projection_kernel_le d hc s hcomm f hf

private theorem displacement_rank_transport
    {D M N : Type*} [Group D] [AddCommGroup M] [Module (ZMod 2) M]
    [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) D M) (σ : Representation (ZMod 2) D N)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) (h : D)
    (hd : Disjoint (ρ h - LinearMap.id).range f.toLinearMap.ker) :
    Module.finrank (ZMod 2) (σ h - LinearMap.id).range =
      Module.finrank (ZMod 2) (ρ h - LinearMap.id).range := by
  have he : f.toLinearMap.comp (ρ h - LinearMap.id) =
      (σ h - LinearMap.id).comp f.toLinearMap := by
    ext w
    change f (ρ h w - w) = σ h (f w) - f w
    rw [map_sub]
    exact congrArg (fun v => v - f w) (LinearMap.congr_fun (f.isIntertwining' h) w)
  have hr : (ρ h - LinearMap.id).range.map f.toLinearMap =
      (σ h - LinearMap.id).range := by
    rw [← LinearMap.range_comp, he,
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hf)]
  rw [← hr, ← LinearMap.range_domRestrict]
  exact LinearMap.finrank_range_of_inj (LinearMap.injective_domRestrict_iff.mpr hd)

/-- Displacement survives the actual U-centralizer quotient and its actual dual.
The inverse in the contragredient action is retained by the dual-rank theorem. -/
theorem displacement_finrank (d : Data T L V F W) (hc : d.SectionCentralizer)
    (s : SourceDuality F X Y) (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h : F.H) (hr : Module.finrank (ZMod 2) (d.action h - LinearMap.id).range = 2)
    (hd : Disjoint (d.action h - LinearMap.id).range d.projection.toLinearMap.ker) :
    Module.finrank (ZMod 2) (s.qAction h - LinearMap.id).range = 2 := by
  let : Finite X := Finite.of_surjective
    (fun v : F.U => (s.uSection.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.uSection.onto)
  obtain ⟨f, hf, hcoord, hk⟩ := exists_projection d s
  have hu : Module.finrank (ZMod 2) (s.uAction h - LinearMap.id).range = 2 :=
    (displacement_rank_transport d.action s.uAction f hf h
      (hd.mono_right (projection_kernel_le d hc s hcomm f hcoord))).trans hr
  have hdual : Module.finrank (ZMod 2) (s.uAction.dual h - LinearMap.id).range = 2 := by
    rw [← BinaryOffender.fixedCodim_zpowers_eq_displacement_rank,
      BinaryOffender.fixedCodim_zpowers_dual,
      BinaryOffender.fixedCodim_zpowers_eq_displacement_rank, hu]
  have he := displacement_rank_transport s.qAction s.uAction.dual
    s.duality.toIntertwiningMap s.duality.toLinearEquiv.surjective h
    (show Disjoint (s.qAction h - LinearMap.id).range
      s.duality.toIntertwiningMap.toLinearMap.ker from by
        rw [LinearMap.ker_eq_bot.mpr s.duality.toLinearEquiv.injective]
        exact disjoint_bot_right)
  exact he.symm.trans hdual

/-- The actor fixes no hyperplane of the original Q-section from 14.5.21(1). -/
theorem no_fixed_hyperplane (d : Data T L V F W) (hc : d.SectionCentralizer)
    (s : SourceDuality F X Y) (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h : F.H) (hr : Module.finrank (ZMod 2) (d.action h - LinearMap.id).range = 2)
    (hd : Disjoint (d.action h - LinearMap.id).range d.projection.toLinearMap.ker)
    (P : Submodule (ZMod 2) Y)
    (hP : Module.finrank (ZMod 2) P + 1 = Module.finrank (ZMod 2) Y) :
    ¬ ∀ y ∈ P, s.qAction h y = y := by
  let : Finite Y := Finite.of_surjective
    (fun q : F.H.pCoreIn 2 => (s.qSection.coordinates q).toAdd)
    (Multiplicative.toAdd.surjective.comp s.qSection.onto)
  intro hfix
  have hle : P ≤ (s.qAction h - LinearMap.id).ker := by
    intro y hy
    exact sub_eq_zero.mpr (hfix y hy)
  have hm := Submodule.finrank_mono hle
  have hn := (s.qAction h - LinearMap.id).finrank_range_add_finrank_ker
  rw [displacement_finrank d hc s hcomm h hr hd] at hn
  omega

omit [Finite G] in
/-- The literal commutator preimage is exactly the coordinate preimage of
 the Q-section's fixed space. No ambient normality is imposed. -/
theorem commutatorPreimage_eq_fixed_preimage (s : SourceDuality F X Y)
    (A : Subgroup G) (hAH : A ≤ F.H) :
    (commutatorPreimage (F.H.pCoreIn 2) A
      (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G))).subgroupOf (F.H.pCoreIn 2) =
      ((Representation.invariants (s.qAction.comp (Subgroup.inclusion hAH))).toAddSubgroup.toSubgroup).comap
        s.qSection.coordinates := by
  let Q := F.H.pCoreIn 2
  let Z := Q ⊓ centralizer (F.U : Set G)
  let I := Representation.invariants (s.qAction.comp (Subgroup.inclusion hAH))
  let B : Subgroup Q := (I.toAddSubgroup.toSubgroup).comap s.qSection.coordinates
  have hQZ : Q ≤ normalizer (Z : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (inf_le_left : Z ≤ Q)).mp s.qSection.kernel_normal
  have hle : commutatorPreimage Q A Z ≤ B.map Q.subtype := by
    intro q hq
    have hqQ := commutatorPreimage_le Q A Z hq
    refine ⟨⟨q, hqQ⟩, ?_, rfl⟩
    change (s.qSection.coordinates ⟨q, hqQ⟩).toAdd ∈ I
    intro a
    exact s.qSection.fixed_on_imageSpace_of_commutator_le A (commutatorPreimage Q A Z)
      (by rw [commutator_comm]; exact commutator_commutatorPreimage_le Q A Z hQZ)
      (Subgroup.inclusion hAH a) a.property _
      ((s.qSection.mem_imageSpace_iff _ _).mpr ⟨⟨q, hqQ⟩, hq, rfl⟩)
  have hge : B.map Q.subtype ≤ commutatorPreimage Q A Z := by
    apply le_commutatorPreimage
    · rintro _ ⟨q, hq, rfl⟩
      exact q.property
    · apply commutator_le.mpr
      rintro _ ⟨q, hq, rfl⟩ a ha
      let actor : F.H := ⟨a, hAH ha⟩
      let qa : Q := ⟨a * q * a⁻¹,
        (mem_normalizer_iff.mp (s.qSection.normalized actor.property) q).mp q.property⟩
      have hfix : s.qAction actor (s.qSection.coordinates q).toAdd =
          (s.qSection.coordinates q).toAdd := hq ⟨a, ha⟩
      have hcoord : s.qSection.coordinates qa = s.qSection.coordinates q :=
        Multiplicative.toAdd.injective ((s.qSection.equivariant actor q).trans hfix)
      have hz : ⁅a, (q : G)⁆ ∈ Z := by
        exact (s.qSection.coordinates_eq_one_iff (qa * q⁻¹)).mp
          (by rw [map_mul, map_inv, hcoord, mul_inv_cancel])
      rw [← commutatorElement_inv]
      exact Z.inv_mem hz
  change (commutatorPreimage Q A Z).comap Q.subtype = B
  rw [le_antisymm hle hge, Subgroup.comap_map_eq_self_of_injective Q.subtype_injective]

/-- A rank-two actor in A forces index at least four in the exact dual section. -/
theorem fixed_index_ge_four (d : Data T L V F W) (hc : d.SectionCentralizer)
    (s : SourceDuality F X Y) (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h : F.H) (hr : Module.finrank (ZMod 2) (d.action h - LinearMap.id).range = 2)
    (hd : Disjoint (d.action h - LinearMap.id).range d.projection.toLinearMap.ker)
    (A : Subgroup G) (hAH : A ≤ F.H) (hhA : (h : G) ∈ A) :
    4 ≤ (commutatorPreimage (F.H.pCoreIn 2) A
      (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G))).relIndex (F.H.pCoreIn 2) := by
  let : Finite Y := Finite.of_surjective
    (fun q : F.H.pCoreIn 2 => (s.qSection.coordinates q).toAdd)
    (Multiplicative.toAdd.surjective.comp s.qSection.onto)
  let r := s.qAction h - LinearMap.id
  let f : F.H.pCoreIn 2 →* Multiplicative r.range :=
    (AddMonoidHom.toMultiplicative r.rangeRestrict.toAddMonoidHom).comp s.qSection.coordinates
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨v, hv⟩ := y.toAdd.property
    obtain ⟨q, hq⟩ := s.qSection.onto (Multiplicative.ofAdd v)
    refine ⟨q, ?_⟩
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change r (s.qSection.coordinates q).toAdd = y.toAdd.val
    rw [hq]
    exact hv
  have hi : f.ker.index = 4 := by
    rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf, Subgroup.card_top]
    change Nat.card r.range = 4
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card,
      show Module.finrank (ZMod 2) r.range = 2 from
        displacement_finrank d hc s hcomm h hr hd]
    rfl
  have hle : (commutatorPreimage (F.H.pCoreIn 2) A
      (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G))).subgroupOf (F.H.pCoreIn 2) ≤ f.ker := by
    rw [commutatorPreimage_eq_fixed_preimage s A hAH]
    intro q hq
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change s.qAction h (s.qSection.coordinates q).toAdd -
      (s.qSection.coordinates q).toAdd = 0
    exact sub_eq_zero.mpr (hq ⟨h, hhA⟩)
  exact hi ▸ Subgroup.index_antitone hle

/-- Literal critical subgroup application for the parent 14.7.69 contradiction. -/
theorem critical_fixed_index_ge_four (d : Data T L V F W) (hc : d.SectionCentralizer)
    (s : SourceDuality F X Y) (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (c : CriticalPath (L := L) F) (earlier : c.EarlierImages)
    (h : F.H) (hhA : (h : G) ∈ c.Uα)
    (hr : Module.finrank (ZMod 2) (d.action h - LinearMap.id).range = 2)
    (hd : Disjoint (d.action h - LinearMap.id).range d.projection.toLinearMap.ker) :
    4 ≤ (commutatorPreimage (F.H.pCoreIn 2) c.Uα
      (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G))).relIndex (F.H.pCoreIn 2) :=
  fixed_index_ge_four d hc s hcomm h hr hd c.Uα (c.Uα_le_H earlier) hhA

/-- A marked nonzero upper actor supplies the two original-section calculations. -/
theorem marked_displacement_finrank (d : Data T L V F W) (hc : d.SectionCentralizer)
    (s : SourceDuality F X Y) (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h : F.H) (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hh : d.qH h = alternatingActor d.naturalQuotient (upper t)) :
    Module.finrank (ZMod 2) (s.qAction h - LinearMap.id).range = 2 :=
  displacement_finrank d hc s hcomm h (d.original_displacement_finrank hc h t ht hh)
    (d.original_displacement_complement hc h t ht hh).1

/-- The literal marked-actor application to the original critical subgroup. -/
theorem marked_critical_fixed_index_ge_four (d : Data T L V F W)
    (hc : d.SectionCentralizer) (s : SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (c : CriticalPath (L := L) F) (earlier : c.EarlierImages)
    (h : F.H) (hhA : (h : G) ∈ c.Uα) (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hh : d.qH h = alternatingActor d.naturalQuotient (upper t)) :
    4 ≤ (commutatorPreimage (F.H.pCoreIn 2) c.Uα
      (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G))).relIndex (F.H.pCoreIn 2) :=
  critical_fixed_index_ge_four d hc s hcomm c earlier h hhA
    (d.original_displacement_finrank hc h t ht hh)
    (d.original_displacement_complement hc h t ht hh).1

end DualSection
end CriticalIntersections
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
