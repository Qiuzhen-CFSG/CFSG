module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.FaithfulRadius
public import Theory.GroupTheory.AbelianCommutatorIndex
public import Theory.Representation.BinaryPermutation.SixCentralDerived
/-!
# Derived-order obstruction for the faithful exceptional radius

At a critical pair, an escaping involution moves at least two binary
coordinates in the literal initial hexacode subgroup. The commutator row
therefore has order at least four. The initial moved subgroup is the
original U inside Z, so this row lies in the midpoint radius derived
group. Conjugation transports the bound to every original-group vertex,
and the established equality of full and moving derived groups retains it
on the entire moving radius.

An actual natural-four central quotient has derived order at most two
when its alternating actor fixes the commutators. We apply the checked
central-cover theorem to the same residual action, without splitting its
kernel or asserting that the natural alternating form vanishes. Thus the
natural-four central quotient is impossible in the faithful distance-four
branch. Whole-core exhaustion and the literal C.1.32 consumer are supplied
when such a marking is constructed; the unconditional alternatives retain
the remaining nonnatural radius explicitly.

Recognition or exclusion of the remaining quotient constituents, the cubic
larger-distance branch, and final reconstruction stay with the original
reconstruction owner. None is assumed proved by this obstruction.
Source: Meierfrankenfeld--Stellmacher (1993), (3.8), pp.878--879;
Aschbacher--Smith C.1.31--32, pp.135--136. The hexacode coordinate operators
retain the existing ATLAS attribution in the imported model modules.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance
open NaturalStructure.Exclusion
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => edge L R

/-- Every involution in the full hexacode group moves at least two binary dimensions. -/
private theorem hexacode_involution_fixedCodim (g : Atlas.Codes.HexAutomorphisms)
    (hg : g ^ 2 = 1) (hne : g ≠ 1) :
    2 ≤ fixedCodim Hexacode.action (zpowers g) := by
  by_cases he : g ∈ Atlas.Codes.hexSign.ker
  · let A := (zpowers g).subgroupOf Atlas.Codes.hexSign.ker
    have hA : zpowers g ≤ Atlas.Codes.hexSign.ker := zpowers_le.mpr he
    have hnA : A ≠ ⊥ := by
      intro hb
      have hm : (⟨g,he⟩ : Atlas.Codes.HexEvenAutomorphisms) ∈ A := mem_zpowers g
      rw [hb,mem_bot] at hm
      exact hne (congrArg Subtype.val hm)
    have hl := Hexacode.ThompsonOffenders.fixedCodim_ge_two A hnA
    change 2 ≤ fixedCodim (Hexacode.action.comp Atlas.Codes.hexSign.ker.subtype)
      ((zpowers g).subgroupOf Atlas.Codes.hexSign.ker) at hl
    rwa [fixedCodim_subgroupOf Hexacode.action hA] at hl
  · have ho : Atlas.Codes.hexSign g = -1 :=
      (Int.units_eq_one_or (Atlas.Codes.hexSign g)).resolve_left he
    rw [Hexacode.ThompsonOffenders.odd_involution_fixedCodim g ho hg]
    decide

/-- The literal abelian initial moved subgroup has a commutator of order at least four
with every element whose hexacode image is an involution. -/
theorem initialMoved_commutator_card_lower
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hk : layerKernel L R = pCore 2 (L ⊔ R : Subgroup G))
    (g : (L ⊔ R : Subgroup G)) (hg : g ^ 2 = 1)
    (hne : g ∉ pCore 2 (L ⊔ R : Subgroup G)) :
    4 ≤ Nat.card (⁅initialMoved L R,zpowers g⁆ : Subgroup (L ⊔ R : Subgroup G)) := by
  let := initialMoved_normal h
  obtain ⟨f,φ,hf,hφ⟩ := initial_moved_hexacode_model h e hz hk
  have hfn : f g ≠ 1 := by
    intro hh
    apply hne
    rw [←hf]
    exact hh
  have hl := hexacode_involution_fixedCodim (f g) (by rw [←map_pow,hg,map_one]) hfn
  let ρ := NormalElementaryQuotient.originalAction (initialMoved L R)
  have he : ∀ k v, φ (ρ k v) = Hexacode.action (f k) (φ v) := by
    intro k v
    have hh : ρ k v = Additive.ofMul (MulAut.conjNormal k v.toMul) :=
      Additive.toMul.injective (Subtype.ext
        (NormalElementaryQuotient.originalAction_apply (initialMoved L R) k v))
    rw [hh,hφ,ofMul_toMul]
  have heq := fixedCodim_map_equivariant ρ Hexacode.action f φ he (zpowers g)
  rw [MonoidHom.map_zpowers] at heq
  have hindex := NormalElementaryQuotient.original_fixed_index (initialMoved L R) (zpowers g)
  rw [inf_relIndex_left,heq] at hindex
  have hcomm := centralizer_relIndex_le_card_of_abelian_commutator
    (initialMoved L R) (initialMoved L R) ⁅initialMoved L R,zpowers g⁆ le_rfl g
    (show g ∈ normalizer (initialMoved L R : Set (L ⊔ R : Subgroup G)) from
      le_normalizer_of_normal (mem_top g))
    (fun x hx => commutator_mem_commutator hx (mem_zpowers g))
  rw [←centralizer_closure,←Subgroup.zpowers_eq_closure] at hcomm
  rw [hindex] at hcomm
  exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hl).trans hcomm

variable (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = pCore 2 (L ⊔ R : Subgroup G))
include h e hz hk

/-- The critical involution forces four actual commutators in its midpoint radius. -/
theorem faithful_midpoint_derived_card_lower (hb : 2 < sourceDistance h)
    (b : Vertex T)
    (hcrit : CriticalPair T (alpha T) b ((sourceGeometry h).exists_critical (alpha T) rfl))
    (c : Vertex T) (hc : color T c = false)
    (hac : (cosetGraph T).dist (alpha T) c = 2)
    (hcb : (cosetGraph T).dist c b = 2) :
    4 ≤ Nat.card (⁅V T c,V T c⁆ : Subgroup (FreeAmalgam T)) := by
  let f := embedM T
  have hbColor := critical_endpoint_color T (alpha T) rfl _ hcrit
  have hreverse := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    (alpha T) rfl (sourceDistance_pos h) b hbColor hcrit
  obtain ⟨x,hx,hxQ⟩ := SetLike.not_le_iff_exists.mp hreverse.2
  have hZS : Z T b ≤ stabilizer T (alpha T) :=
    ((sourceGeometry h).omega_bound b hbColor (by
      rw [(sourceGeometry h).distance_constant b hbColor]; exact sourceDistance_pos h)).trans
      (critical_X_le_vertex h e b hbColor (alpha T) hreverse)
  obtain ⟨g,hg⟩ := show x ∈ f.range from (by
    change x ∈ (embedM T).range
    have hxS := hZS hx
    change x ∈ stabilizer T (mVertex T 1) at hxS
    rwa [stabilizer_m_base] at hxS)
  have hgne : g ∉ pCore 2 (L ⊔ R : Subgroup G) := by
    intro hgQ
    apply hxQ
    rw [←hg,Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact mem_map_of_mem f hgQ
  have hg2 : g ^ 2 = 1 := by
    apply embedM_injective T
    rw [map_pow,hg,map_one]
    let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) b hbColor
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hfour := initialMoved_commutator_card_lower h e hz hk g hg2 hgne
  have hUa : (initialMoved L R).map f = U T (alpha T) := by
    rw [graph_U_eq_X_commutator h e hz,graph_X h,graph_component h,←map_commutator]
  have hZa : Z T (alpha T) ≤ V T c := le_iSup_of_le (alpha T) (le_iSup_of_le hac.le le_rfl)
  have hZb : Z T b ≤ V T c := le_iSup_of_le b (le_iSup_of_le
    (by rw [SimpleGraph.dist_comm,hcb]) le_rfl)
  have hcomm : (⁅initialMoved L R,zpowers g⁆).map f ≤ ⁅V T c,V T c⁆ := by
    rw [map_commutator,hUa,MonoidHom.map_zpowers,hg]
    exact commutator_mono ((U_le_Z (alpha T)).trans hZa) (zpowers_le.mpr (hZb hx))
  let := finite_stabilizer T c
  have hVS : V T c ≤ stabilizer T c :=
    ((sourceGeometry h).V_le_Q hb c hc).trans (fun _ hx => hx.1)
  let : Finite (⁅V T c,V T c⁆ : Subgroup (FreeAmalgam T)) :=
    Finite.of_injective (inclusion ((commutator_le_self _).trans hVS)) (inclusion_injective _)
  have hh := card_le_of_le hcomm
  rw [card_map_of_injective (embedM_injective T)] at hh
  exact hfour.trans hh

omit h e hz hk [Finite G] in
private theorem radius_derived_card_eq_base (a : Vertex T) (ha : color T a = false) :
    Nat.card (⁅V T a,V T a⁆ : Subgroup (FreeAmalgam T)) =
      Nat.card (⁅V T (alpha T),V T (alpha T)⁆ : Subgroup (FreeAmalgam T)) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color T ha
  have hv : V T (mVertex T g) = (V T (alpha T)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [alpha,act_mVertex,one_mul] using V_act T g (alpha T)
  rw [hv,←map_commutator,card_map_of_injective (MulAut.conj g⁻¹).injective]

/-- Every original-group radius has at least four elements in its derived subgroup. -/
theorem faithful_radius_derived_card_lower (hb : 2 < sourceDistance h)
    (a : Vertex T) (ha : color T a = false) :
    4 ≤ Nat.card (⁅V T a,V T a⁆ : Subgroup (FreeAmalgam T)) := by
  obtain ⟨b,hcrit⟩ := criticalPair_exists T (alpha T)
    ((sourceGeometry h).exists_critical (alpha T) rfl)
  let p := DistanceEight.PathCentrality.CriticalPath.ofPair (geometry := sourceGeometry h) rfl hcrit
  have hl : p.walk.length = 4 := p.length_eq_b.trans (faithful_distance_eq_four h e hz hk hb)
  have hle : 2 ≤ p.walk.length := by omega
  let c := p.walk.getVert 2
  have hc : color T c = false := (p.vertex_color hle).mpr (by decide)
  have hac : (cosetGraph T).dist (alpha T) c = 2 := p.dist_start hle
  have hcb : (cosetGraph T).dist c b = 2 := by rw [p.dist_end,hl]
  have hh := faithful_midpoint_derived_card_lower h e hz hk hb b hcrit c hc hac hcb
  rwa [radius_derived_card_eq_base c hc,←radius_derived_card_eq_base a ha] at hh

/-- The moving subgroup retains all these commutators, including their order bound. -/
theorem faithful_moving_derived_card_lower (hb : 2 < sourceDistance h)
    (a : Vertex T) (ha : color T a = false) :
    4 ≤ Nat.card (_root_.commutator (Vcirc T a)) := by
  obtain ⟨g,hga⟩ := exists_mVertex_of_color T ha
  let t := hVertex T g
  have hat : Adjacent T a t := (adjacent_iff_exists_common T a t).mpr ⟨g,Or.inl ⟨hga,rfl⟩⟩
  have hh := faithful_radius_derived_card_lower h e hz hk hb a ha
  rw [radius_derived_eq_moving_derived_original h (sourceGeometry h) hb a t ha hat
    (faithful_radius_derived_le_fixed h e hz hk hb a ha),←map_subtype_commutator,
    card_map_of_injective (Vcirc T a).subtype_injective] at hh
  exact hh

omit h e hz hk [Finite G] in
/-- An actual natural marking of the central quotient under the original residual.
The actor may have a kernel; its image contains the literal alternating subgroup. -/
def HasNaturalMovingQuotient (a : Vertex T) : Prop :=
  ∃ he : IsElementaryAbelian 2 ((Vcirc T a) ⧸ center (Vcirc T a)),
    letI := he
    ∃ π : pResidual 2 (stabilizer T a) →* Equiv.Perm (Fin 6),
      alternatingGroup (Fin 6) ≤ π.range ∧
      ∃ E : Additive ((Vcirc T a) ⧸ center (Vcirc T a)) ≃ₗ[ZMod 2]
          BinaryPermutation.natural (Fin 6),
        ∀ g v, E (Offenders.linearize (movingQuotientAction a) g.val v) =
          BinaryPermutation.naturalRepresentation (Fin 6) (π g) (E v)

omit h e hz hk [Finite G] in
/-- A natural residual marking forces the derived order to be at most two.
This uses invariance of commutators, not vanishing of the natural pairing. -/
theorem moving_derived_card_le_two_of_natural
    (a : Vertex T) (hfixed : ⁅V T a,V T a⁆ ≤ fixedCore T a)
    (hn : HasNaturalMovingQuotient (L := L) (R := R) a) :
    Nat.card (_root_.commutator (Vcirc T a)) ≤ 2 := by
  obtain ⟨he,π,hπ,E,hE⟩ := hn
  let := he
  let P := Vcirc T a
  let em : (P ⧸ center P) ≃* Multiplicative (BinaryPermutation.natural (Fin 6)) :=
    E.toAddEquiv.toMultiplicative
  let q := em.toMonoidHom.comp (QuotientGroup.mk' (center P))
  let ρ := (movingAction a).comp (pResidual 2 (stabilizer T a)).subtype
  apply BinaryPermutation.SixCentralDerived.card_derived_le_two q
    (em.surjective.comp (QuotientGroup.mk'_surjective (center P)))
    (by
      intro x hx
      apply (QuotientGroup.eq_one_iff x).mp
      apply em.injective
      exact hx.trans (map_one em).symm)
    ρ π hπ
  · intro g x
    have hh := hE g (Additive.ofMul (QuotientGroup.mk' (center P) x))
    change E (Additive.ofMul (movingQuotientAction a g.val
      (QuotientGroup.mk' (center P) x))) = _ at hh
    rw [movingQuotientAction_apply] at hh
    exact hh
  · intro g _ z hz
    apply Subtype.ext
    rw [show ρ g z = movingAction a g.val z from rfl,movingAction_apply]
    have hm : Vcirc T a ≤ V T a := le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer a).trans (V_normalized a))
    have hd : (z : FreeAmalgam T) ∈ ⁅Vcirc T a,Vcirc T a⁆ := by
      rw [←map_subtype_commutator]
      exact mem_map_of_mem (Vcirc T a).subtype hz
    have hdf := hfixed (commutator_mono hm hm hd)
    have hgl : (g.val : FreeAmalgam T) ∈ Ltilde T a :=
      mem_map_of_mem (stabilizer T a).subtype g.property
    rw [hdf.2 g.val hgl,mul_inv_cancel_right]

/-- The genuine natural-four quotient is excluded at every faithful exceptional radius. -/
theorem faithful_moving_not_natural (hb : 2 < sourceDistance h)
    (a : Vertex T) (ha : color T a = false) :
    ¬ HasNaturalMovingQuotient (L := L) (R := R) a := by
  intro hn
  have hl := faithful_moving_derived_card_lower h e hz hk hb a ha
  have hu := moving_derived_card_le_two_of_natural a
    (faithful_radius_derived_le_fixed h e hz hk hb a ha) hn
  omega

/-- A natural marking at one original-group radius excludes the larger-distance case. -/
theorem faithful_distance_eq_two_of_natural_radius
    (a : Vertex T) (ha : color T a = false)
    (hn : HasNaturalMovingQuotient (L := L) (R := R) a) : sourceDistance h = 2 := by
  apply sourceDistance_eq_two h
  by_contra! hb
  exact faithful_moving_not_natural h e hz hk hb a ha hn

/-- Whole intrinsic-core exhaustion under that actual natural radius marking. -/
theorem coreExhaustion_of_faithful_natural_radius
    (a : Vertex T) (ha : color T a = false)
    (hn : HasNaturalMovingQuotient (L := L) (R := R) a) : CoreExhaustion L R :=
  coreExhaustion_of_distanceTwo h e hz
    (faithful_distance_eq_two_of_natural_radius h e hz hk a ha hn)

/-- The literal C.1.32 application retains the original natural marking premise.
Its construction or the exclusion of the other quotient constituents stays with this owner. -/
theorem rankTwo_of_faithful_natural_radius
    (a : Vertex T) (ha : color T a = false)
    (hn : HasNaturalMovingQuotient (L := L) (R := R) a) : RankTwoAlternatives L R :=
  rankTwo_of_exhaustion h e hz (coreExhaustion_of_faithful_natural_radius h e hz hk a ha hn)

/-- The unconditional remaining faithful branch has derived order at least four
and cannot have the natural-four central quotient. -/
theorem faithful_coreExhaustion_or_nonNatural_radius :
    CoreExhaustion L R ∨
      sourceDistance h = 4 ∧ ∀ a : Vertex T, color T a = false →
        4 ≤ Nat.card (_root_.commutator (Vcirc T a)) ∧
        ¬ HasNaturalMovingQuotient (L := L) (R := R) a := by
  by_cases hb : 2 < sourceDistance h
  · exact Or.inr ⟨faithful_distance_eq_four h e hz hk hb,fun a ha =>
      ⟨faithful_moving_derived_card_lower h e hz hk hb a ha,
        faithful_moving_not_natural h e hz hk hb a ha⟩⟩
  · exact Or.inl (coreExhaustion_of_distanceTwo h e hz
      (sourceDistance_eq_two h (Nat.le_of_not_gt hb)))

/-- The same proved obstruction is attached to the actual rank-two consumer. -/
theorem faithful_rankTwo_or_nonNatural_radius :
    RankTwoAlternatives L R ∨
      sourceDistance h = 4 ∧ ∀ a : Vertex T, color T a = false →
        4 ≤ Nat.card (_root_.commutator (Vcirc T a)) ∧
        ¬ HasNaturalMovingQuotient (L := L) (R := R) a :=
  (faithful_coreExhaustion_or_nonNatural_radius h e hz hk).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
