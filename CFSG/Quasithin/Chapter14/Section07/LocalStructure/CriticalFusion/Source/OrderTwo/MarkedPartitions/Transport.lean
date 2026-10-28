module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Normalizers
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.ModuleCover
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.MarkedPartitions.Coordinates
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.ModuleTransport

/-!
# Sylow coordinates on the original section

The actual relative Sylow of K* is transported through the given S₅ and
SL₂(4) markings. Sylow conjugacy then supplies a conjugator for Uα* in the
contradiction branch Uα*=Q*. Applying that conjugator to the universal-cover
surjection produces coordinates on the original W and retains the original
projection, kernel and actual H-actors.

The whole critical actor has equal fixed and moved spaces. Its fixed plane
has the five-line coordinate coverage; in the |U₀|=4 case a one-dimensional
central quotient gives the two-part coverage. These statements do not yet
identify the marked coordinate line with V/V₁, nor assert the ambient fusion
exclusion. The separate action marking and ambient lift must do that work.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.65–66 and 14.7.69(a), printed pp.1070, 1072–1073.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation Representation.OneCohomology
open Chapter12.Section08 Representation.SL2FourNatural Matrix.SpecialLinearGroup
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem alternatingActor_injective : Function.Injective (alternatingActor d.naturalQuotient) :=
  Subtype.coe_injective.comp d.naturalQuotient.marking.injective

theorem alternatingActor_range : (alternatingActor d.naturalQuotient).range =
    alternatingGroup (Fin 5) := by
  rw [alternatingActor, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr d.naturalQuotient.marking.surjective,
    ← MonoidHom.range_eq_map, range_subtype]

/-- A genuine Sylow conjugator puts the actual starred critical actor into
upper coordinates. The ambient quotient and its marking are unchanged. -/
theorem exists_critical_sylow_conjugator (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (hfull : star F c.Uα = star F (Q T L)) :
    ∃ g : SL, (c.Uα.subgroupOf F.H).map d.qH =
      (upperUnipotent SL2FourNatural.F).map
        ((alternatingActor d.naturalQuotient).comp (MulAut.conj g).toMonoidHom) := by
  let a := alternatingActor d.naturalQuotient
  let A := (c.Uα.subgroupOf F.H).map d.qH
  have hK : (star F (K F)).map d.model.toMonoidHom = alternatingGroup (Fin 5) := by
    rw [star, map_map]
    exact d.K_image
  have hA : Chapter1.IsSylowIn 2 A (alternatingGroup (Fin 5)) := by
    have h := (Chapter1.IsSylowIn.map_iff d.model.toMonoidHom d.model.injective).mpr
      ((hfull ▸ (c.lemma_14_7_66 earlier).2) : Chapter1.IsSylowIn 2
        (star F c.Uα) (star F (K F)))
    rw [hK] at h
    simpa only [A, Data.qH, star, map_map] using h
  have hAr : A ≤ a.range := by
    rw [d.alternatingActor_range]
    exact (Chapter1.isSylowIn_iff.mp hA).2.1
  have htop : (⊤ : Subgroup SL).map a = alternatingGroup (Fin 5) := by
    rw [← MonoidHom.range_eq_map, d.alternatingActor_range]
  have hP : Chapter1.IsSylowIn 2 (A.comap a) ⊤ := by
    apply (Chapter1.IsSylowIn.map_iff a d.alternatingActor_injective).mp
    rw [map_comap_eq_self hAr, htop]
    exact hA
  obtain ⟨hp, _, hm⟩ := Chapter1.isSylowIn_iff.mp hP
  let P : Sylow 2 SL := ⟨A.comap a, hp, fun hB hPB => hm _ hB hPB le_top⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL (upperUnipotentSylow SL2FourNatural.F 2) P
  refine ⟨g, ?_⟩
  change A = _
  rw [← map_map]
  have hc : (upperUnipotent SL2FourNatural.F).map (MulAut.conj g).toMonoidHom = A.comap a := by
    change (g • upperUnipotentSylow SL2FourNatural.F 2 : Sylow 2 SL).toSubgroup = _
    rw [hg]
  rw [hc, map_comap_eq_self hAr]

/-- The universal cover on the original W, with a Sylow conjugator and the
literal critical actor image. Only coordinates and actors are transported. -/
structure CriticalChart (hc : d.SectionCentralizer) (c : CriticalPath (L := L) F) where
  conjugator : SL
  cover : SL2FourCentralCover.Space →ₗ[ZMod 2] W
  equivariant : ∀ s w, cover (SL2FourCentralCover.binaryAction s w) =
    d.descendedAction hc (alternatingActor d.naturalQuotient
      (conjugator * s * conjugator⁻¹)) (cover w)
  onto : Function.Surjective cover
  projection : ∀ w, d.projection (cover w) =
    SL2FourNatural.action conjugator (SL2FourCentralCover.projection w)
  image : (c.Uα.subgroupOf F.H).map d.qH =
    (upperUnipotent SL2FourNatural.F).map
      ((alternatingActor d.naturalQuotient).comp (MulAut.conj conjugator).toMonoidHom)

theorem exists_criticalChart (hc : d.SectionCentralizer) (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (hfull : star F c.Uα = star F (Q T L)) :
    Nonempty (d.CriticalChart hc c) := by
  obtain ⟨g, hg⟩ := d.exists_critical_sylow_conjugator c earlier hfull
  obtain ⟨q, hq, hp, _, _⟩ := d.original_cover hc
  let σ : Representation (ZMod 2) SL W := (d.descendedAction hc).comp (alternatingActor d.naturalQuotient)
  let qg : SL2FourCentralCover.Space →ₗ[ZMod 2] W := (σ g).comp q.toLinearMap
  have he : ∀ s w, qg (SL2FourCentralCover.binaryAction s w) =
      (σ.comp (MulAut.conj g).toMonoidHom) s (qg w) := by
    intro s w
    change σ g (q (SL2FourCentralCover.binaryAction s w)) = σ (g * s * g⁻¹) (σ g (q w))
    rw [q.isIntertwining]
    change σ g (σ s (q w)) = _
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, σ.inv_self_apply]
  refine ⟨⟨g, qg, he, ?_, ?_, hg⟩⟩
  · intro w
    obtain ⟨v, hv⟩ := hq (σ g⁻¹ w)
    refine ⟨v, ?_⟩
    change σ g (q v) = w
    rw [hv, σ.self_inv_apply]
  · intro w
    change d.projection (d.descendedAction hc (alternatingActor d.naturalQuotient g) (q w)) = _
    rw [← show d.descendedProjection hc (d.descendedAction hc
      (alternatingActor d.naturalQuotient g) (q w)) =
      d.projection (d.descendedAction hc (alternatingActor d.naturalQuotient g) (q w)) from rfl]
    rw [(d.descendedProjection hc).isIntertwining]
    change d.naturalQuotient.action (alternatingActor d.naturalQuotient g) (d.projection (q w)) = _
    rw [hp]
    exact d.naturalQuotient.restriction g _

namespace CriticalChart
variable {d} {hc : d.SectionCentralizer} {c : CriticalPath (L := L) F}
  (b : d.CriticalChart hc c)

/-- The original projection expressed in the same Sylow coordinates as the cover. -/
def naturalCoordinates : W →ₗ[ZMod 2] SL2FourNatural.V :=
  (SL2FourNatural.action b.conjugator⁻¹).toLinearMap.comp d.projection.toLinearMap

theorem naturalCoordinates_cover (w : SL2FourCentralCover.Space) :
    b.naturalCoordinates (b.cover w) = SL2FourCentralCover.projection w := by
  change SL2FourNatural.action b.conjugator⁻¹ (d.projection (b.cover w)) = _
  rw [b.projection, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem naturalCoordinates_ker : b.naturalCoordinates.ker = d.projection.toLinearMap.ker := by
  ext w
  change SL2FourNatural.action b.conjugator⁻¹ (d.projection w) = 0 ↔ d.projection w = 0
  exact (SL2FourNatural.action b.conjugator⁻¹).map_eq_zero_iff

/-- A literal H-actor and its conjugated SL₂ coordinate act identically. -/
theorem actor_cover (h : F.H) (s : SL)
    (hh : d.qH h = alternatingActor d.naturalQuotient
      (b.conjugator * s * b.conjugator⁻¹)) (w : SL2FourCentralCover.Space) :
    d.action h (b.cover w) = b.cover (SL2FourCentralCover.binaryAction s w) := by
  rw [← d.descendedAction_apply hc h, hh]
  exact (b.equivariant s w).symm

/-- Every upper parameter has a lift in the actual Uα, through the literal star map. -/
theorem upper_lift (t : SL2FourNatural.F) :
    ∃ h : F.H, (h : G) ∈ c.Uα ∧ d.qH h = alternatingActor d.naturalQuotient
      (b.conjugator * upper t * b.conjugator⁻¹) := by
  have hm : alternatingActor d.naturalQuotient (b.conjugator * upper t * b.conjugator⁻¹) ∈
      (c.Uα.subgroupOf F.H).map d.qH := by
    rw [b.image]
    exact mem_map.mpr ⟨upper t, (mem_upperUnipotent _ _).mpr
      ⟨t, (SL2FourCentralCover.upper_transvection t).symm⟩, rfl⟩
  exact hm

/-- Conversely the parameter is taken from the image of the original actor. -/
theorem actor_parameter (h : F.H) (hh : (h : G) ∈ c.Uα) :
    ∃ t : SL2FourNatural.F, d.qH h = alternatingActor d.naturalQuotient
      (b.conjugator * upper t * b.conjugator⁻¹) := by
  have hm : d.qH h ∈ (c.Uα.subgroupOf F.H).map d.qH :=
    mem_map_of_mem d.qH hh
  rw [b.image] at hm
  obtain ⟨s, hs, he⟩ := hm
  obtain ⟨t, ht⟩ := (mem_upperUnipotent _ _).mp hs
  have hs' : s = upper t := ht.symm.trans (SL2FourCentralCover.upper_transvection t).symm
  exact ⟨t, he.symm.trans (congrArg _ hs')⟩

/-- Nonidentity is measured modulo O₂(H), exactly as in the literal commutator set. -/
theorem actor_parameter_ne_zero (h : F.H) (hh : (h : G) ∈ c.Uα)
    (hn : (h : G) ∉ F.H.pCoreIn 2) :
    ∃ t : SL2FourNatural.F, t ≠ 0 ∧ d.qH h = alternatingActor d.naturalQuotient
      (b.conjugator * upper t * b.conjugator⁻¹) := by
  obtain ⟨t, ht⟩ := b.actor_parameter h hh
  refine ⟨t, ?_, ht⟩
  intro hz
  have he : d.qH h = 1 := by
    rw [hz, show upper (0 : SL2FourNatural.F) = 1 from by
      rw [SL2FourCentralCover.upper_transvection, transvection_coeff_zero], mul_one,
      mul_inv_cancel, map_one] at ht
    exact ht
  apply hn
  have hm : h ∈ d.qH.ker := he
  rwa [d.qH_ker] at hm

/-- The fixed space on the same W is the inverse image of the upper natural line. -/
theorem mem_fixed_iff (w : W) :
    w ∈ BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H) ↔
      b.naturalCoordinates w 1 = 0 := by
  obtain ⟨v, rfl⟩ := b.onto w
  rw [b.naturalCoordinates_cover]
  constructor
  · intro hw
    obtain ⟨h, hh, he⟩ := b.upper_lift 1
    have hf := hw ⟨h, hh⟩
    change d.action h (b.cover v) = b.cover v at hf
    rw [b.actor_cover h (upper 1) he] at hf
    have hn := congrArg b.naturalCoordinates hf
    rw [b.naturalCoordinates_cover, b.naturalCoordinates_cover,
      SL2FourCentralCover.projection.isIntertwining] at hn
    change SL2FourNatural.action (upper 1) (SL2FourCentralCover.projection v) = _ at hn
    rw [upper_action] at hn
    simpa using congrFun hn 0
  · intro hv a
    obtain ⟨t, ht⟩ := b.actor_parameter a.val a.property
    change d.action a.val (b.cover v) = b.cover v
    rw [b.actor_cover a.val (upper t) ht]
    by_cases ht0 : t = 0
    · subst t
      rw [show upper (0 : SL2FourNatural.F) = 1 from by
        rw [SL2FourCentralCover.upper_transvection, transvection_coeff_zero], map_one]
      rfl
    · rw [(SL2FourCentralCover.upper_fixed_iff t ht0 v).mpr hv]

open SL2FourCentralCover MarkedPartitions

/-- Coordinates describe exactly the fixed space of the original Uα. -/
theorem mem_fixed_iff_point (w : W) :
    w ∈ BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H) ↔
      ∃ r x : SL2FourNatural.F, b.cover (MarkedPartitions.point r x) = w := by
  rw [b.mem_fixed_iff]
  constructor
  · intro hw
    obtain ⟨v, rfl⟩ := b.onto w
    rw [b.naturalCoordinates_cover] at hw
    exact ⟨(coordinates v).1, (coordinates v).2 0,
      congrArg b.cover (fixed_point v hw).symm⟩
  · rintro ⟨r, x, rfl⟩
    rw [b.naturalCoordinates_cover, point_projection]
    rfl

/-- The moved space uses the original H-representation restricted to the literal Uα. -/
def moved (_b : d.CriticalChart hc c) : Submodule (ZMod 2) W :=
  ⨆ h : c.Uα.subgroupOf F.H, (d.action h.val - LinearMap.id).range

theorem moved_eq_fixed : b.moved =
    BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H) := by
  have hd (t : SL2FourNatural.F) (w : Space) :
      b.cover (binaryAction (upper t) w - w) ∈ b.moved := by
    obtain ⟨h, hh, he⟩ := b.upper_lift t
    apply Submodule.mem_iSup_of_mem (⟨h, hh⟩ : c.Uα.subgroupOf F.H)
    refine ⟨b.cover w, ?_⟩
    change d.action h (b.cover w) - b.cover w = _
    rw [b.actor_cover h (upper t) he, map_sub]
  apply le_antisymm
  · apply iSup_le
    intro h
    rintro _ ⟨w, rfl⟩
    obtain ⟨v, rfl⟩ := b.onto w
    obtain ⟨t, ht⟩ := b.actor_parameter h.val h.property
    change d.action h.val (b.cover v) - b.cover v ∈ _
    rw [b.actor_cover h.val (upper t) ht, ← map_sub]
    apply (b.mem_fixed_iff _).mpr
    rw [b.naturalCoordinates_cover, displacement_point, point_projection]
    rfl
  · intro w hw
    obtain ⟨v, rfl⟩ := b.onto w
    have hv : (coordinates v).2 1 = 0 := by
      have h := (b.mem_fixed_iff _).mp hw
      rwa [b.naturalCoordinates_cover] at h
    obtain ⟨s, t, u, v, he⟩ := fixed_is_sum_of_upper_displacements v hv
    rw [he, map_add]
    exact (b.moved).add_mem (hd s u) (hd t v)

/-- The original universal-cover map is an isomorphism in the rank-three U₀ case. -/
theorem cover_injective_of_card_eight (hcard : Nat.card d.U₀ = 8) :
    Function.Injective b.cover := by
  let := d.finite_section
  have hd := d.projection.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr d.projection_onto, finrank_top, finrank_vector] at hd
  have hk := (d.original_cover hc).choose_spec.2.2.1
  have hn : Module.finrank (ZMod 2) d.projection.toLinearMap.ker = 2 := by
    rw [d.card_U₀] at hcard
    interval_cases he : Module.finrank (ZMod 2) d.projection.toLinearMap.ker <;> norm_num at *
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := b.cover) _).mpr b.onto
  rw [binary_finrank, ← hd, hn]

/-- The |U₀|=4 branch is a proper central quotient of this same universal cover. -/
theorem cover_not_injective_of_card_four (hcard : Nat.card d.U₀ = 4) :
    ¬ Function.Injective b.cover := by
  let := d.finite_section
  have hd := d.projection.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr d.projection_onto, finrank_top, finrank_vector] at hd
  have hk := (d.original_cover hc).choose_spec.2.2.1
  have hn : Module.finrank (ZMod 2) d.projection.toLinearMap.ker = 1 := by
    rw [d.card_U₀] at hcard
    interval_cases he : Module.finrank (ZMod 2) d.projection.toLinearMap.ker <;> norm_num at *
  intro hi
  have h := LinearMap.finrank_le_finrank_of_injective hi
  rw [binary_finrank, ← hd, hn] at h
  omega

/-- Coverage of the rank-three fixed plane on the original section. The middle
line is marked by the cubic action in `diagonal_displacement_point`. -/
theorem rank_three_partition (w : W)
    (hw : w ∈ BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H)) :
    (∃ r, b.cover (MarkedPartitions.point r 0) = w) ∨ (∃ x, b.cover (MarkedPartitions.point 0 x) = w) ∨
      ∃ t y : SL2FourNatural.F, t ≠ 0 ∧ y ≠ 0 ∧
        b.cover (MarkedPartitions.point (t ^ 2 * y) (t * y)) = w := by
  obtain ⟨r, x, rfl⟩ := (b.mem_fixed_iff_point _).mp hw
  rcases point_partition r x with hx | hr | ⟨t, y, ht, hy, he⟩
  · exact Or.inl ⟨r, by rw [hx]⟩
  · exact Or.inr (Or.inl ⟨x, by rw [hr]⟩)
  · exact Or.inr (Or.inr ⟨t, y, ht, hy, congrArg b.cover he.symm⟩)

/-- Coverage of the rank-two fixed plane, after the one-dimensional central quotient. -/
theorem rank_two_partition (hcard : Nat.card d.U₀ = 4) (w : W)
    (hw : w ∈ BinaryOffender.fixedSpace d.action (c.Uα.subgroupOf F.H)) :
    (∃ r, b.cover (MarkedPartitions.point r 0) = w) ∨
      ∃ t y : SL2FourNatural.F, t ≠ 0 ∧ y ≠ 0 ∧
        b.cover (MarkedPartitions.point (t ^ 2 * y) (t * y)) = w := by
  obtain ⟨r, x, rfl⟩ := (b.mem_fixed_iff_point _).mp hw
  rcases proper_quotient_partition b.cover b.naturalCoordinates b.naturalCoordinates_cover
    (b.cover_not_injective_of_card_four hcard) r x with hx | ⟨t, y, ht, hy, he⟩
  · exact Or.inl ⟨r, by rw [hx]⟩
  · exact Or.inr ⟨t, y, ht, hy, he.symm⟩

end CriticalChart


end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
