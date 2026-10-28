module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryRank
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSetup
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledFF

/-!
# The original binary natural–dual orbit and its ambient two-rank

The original seed marking descends the inverse-conjugation twist through
the characteristic action kernel. Nonisomorphism forces its outer action,
so multiplication coordinates identify the entire chosen orbit with the
natural–dual module for that same SL₃(2) actor. The two coordinate axes
are exactly the original seed and its conjugate by the retained element of T.

The trivial invertible commutant transfers to this actual orbit. Relative
normality of its component image then embeds the full ambient automizer in
the model normalizer, giving two-rank at most two. No global r bound,
weak-closure bound or ambient centralizer-core geometry is assumed or proved.
Those remaining §7.7 obligations stay with qt-d-1222-nonff-doubled.

The internal import reuses the characteristic-kernel and literal coordinate
implementation from the companion FF transport without changing its public API.
Source: Aschbacher–Smith D.3.10, 3.2.5, Table 7.2.1 and 7.6–7.7,
printed pp.201,580,698,701–709.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem seed_binary_three_marking [IsElementaryAbelian 2 V]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (F : BinaryField) (hF : F.degree = 1)
    (m : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)) :
    ∃ q : L →* BinaryLinearThree.Group, Function.Surjective q ∧ q.ker.Characteristic ∧
      ∃ e : Additive V ≃ₗ[ZMod 2] BinaryLinearThree.Vector,
      ∀ l v, e (doubledSeedAction L V D.normalizes l v) =
        BinaryLinearThree.W (q l) (e v) := by
  let b := ExtensionConsequences.degreeOneNaturalEquiv F hF 3
  let f : D.componentImage ≃* BinaryLinearThree.Group := m.groupEquiv.trans b.groupEquiv
  let q : L →* BinaryLinearThree.Group := f.toMonoidHom.comp D.componentHom
  have hq : Function.Surjective q := f.surjective.comp D.componentHom_surjective
  let : Nontrivial BinaryLinearThree.Group := f.symm.toEquiv.nontrivial
  let : q.ker.Characteristic := quotient_center_kernel D h f Matrix.PSL3Two.center_eq_bot
  let e := ((seedCoordinates D).symm.trans m.linearEquiv).trans b.linearEquiv
  have he : ∀ l v, e (doubledSeedAction L V D.normalizes l v) =
      BinaryLinearThree.W (q l) (e v) := by
    intro l v
    obtain ⟨w,rfl⟩ := (seedCoordinates D).surjective v
    rw [← seedCoordinates_action D]
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    exact (congrArg b.linearEquiv (m.intertwines (D.componentHom l) w)).trans
      (b.intertwines (m.groupEquiv (D.componentHom l)) (m.linearEquiv w))
  exact ⟨q,hq,inferInstance,e,he⟩

/-- Same-actor coordinates retaining both original conjugate seed subgroups. -/
theorem sourceOrbit_binary_pair_coordinates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ q : L →* BinaryLinearThree.Group, Function.Surjective q ∧
      ∃ e : Additive D.sourceOrbit ≃ₗ[ZMod 2] BinaryLinearThree.NaturalDual.Space,
        (∀ l v, e (doubledSeedAction L D.sourceOrbit
          D.sourceOrbit_component_normalizes l v) =
            BinaryLinearThree.NaturalDual.action (q l) (e v)) ∧
        (∀ v, (e v).2 = 0 ↔ (v.toMul : G) ∈ V) ∧
        (∀ v, (e v).1 = 0 ↔ (v.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) := by
  let := D.elementary
  have hmark := @seed_binary_three_marking G _ _ T L V D D.elementary h F hF hmodel.some
  let q := hmark.choose
  have hq : Function.Surjective q := hmark.choose_spec.1
  let : q.ker.Characteristic := hmark.choose_spec.2.1
  let e := hmark.choose_spec.2.2.choose
  have he := hmark.choose_spec.2.2.choose_spec
  have hcoords := @sourceOrbit_marked_doubled_coordinates G _ T L V D D.elementary hd
  let t := hcoords.choose
  have ht : t ∈ (T : Subgroup G) := hcoords.choose_spec.choose
  have hpair := hcoords.choose_spec.choose_spec
  have hne := hpair.2.1
  let c := hpair.2.2.choose
  have hc : ∀ l v, c (doubledPairAction L V D.normalizes t
      (D.sylow_normalizes_component ht) l v) = doubledSeedAction L D.sourceOrbit
      D.sourceOrbit_component_normalizes l (c v) := hpair.2.2.choose_spec.2
  have hmul : ∀ v w, ((c (v,w)).toMul : G) =
      (v.toMul : G) * (t * (w.toMul : G) * t⁻¹) := hpair.2.2.choose_spec.1
  let α := doubledTwist L t (D.sylow_normalizes_component ht)
  have haut := descend_twist q hq α
  have hmodel := doubledBinary_pair_coordinates
    (doubledSeedAction L V D.normalizes) q e he α haut.choose haut.choose_spec hne
  let E := hmodel.choose
  have hE := hmodel.choose_spec.1
  have hzero := hmodel.choose_spec.2.2
  have hzero' (v : Additive V × Additive V) : (E v).1 = 0 ↔ v.1 = 0 := by
    rw [hmodel.choose_spec.2.1]
    exact e.map_eq_zero_iff
  let C := c.symm.trans E
  refine ⟨t,ht,hpair.1,q,hq,C,?_,?_,?_⟩
  · intro l v
    obtain ⟨w,rfl⟩ := c.surjective v
    rw [← hc]
    simp only [C, LinearEquiv.trans_apply, c.symm_apply_apply]
    exact hE l w
  · intro v
    change (E (c.symm v)).2 = 0 ↔ (v.toMul : G) ∈ V
    rw [hzero]
    have hc0 (w : Additive V) : ((c (w,0)).toMul : G) = (w.toMul : G) := by
      simpa using hmul w 0
    constructor
    · intro hz
      have hv : c ((c.symm v).1,0) = v := by
        rw [← hz]
        exact c.apply_symm_apply v
      rw [← hv, hc0]
      exact (c.symm v).1.toMul.property
    · intro hv
      let w : Additive V := Additive.ofMul ⟨v.toMul,hv⟩
      have hw : c (w,0) = v := by
        apply Additive.toMul.injective
        apply Subtype.ext
        exact hc0 w
      rw [← hw, c.symm_apply_apply]
  · intro v
    change (E (c.symm v)).1 = 0 ↔ _
    rw [hzero']
    have hc0 (w : Additive V) : ((c (0,w)).toMul : G) =
        t * (w.toMul : G) * t⁻¹ := by
      simpa using hmul 0 w
    constructor
    · intro hz
      have hv : c (0,(c.symm v).2) = v := by
        rw [← hz]
        exact c.apply_symm_apply v
      rw [← hv, hc0]
      exact mem_map_of_mem (MulAut.conj t).toMonoidHom (c.symm v).2.toMul.property
    · rintro ⟨w,hw,hv⟩
      let z : Additive V := Additive.ofMul ⟨w,hw⟩
      have hz : c (0,z) = v := by
        apply Additive.toMul.injective
        apply Subtype.ext
        exact (hc0 z).trans hv
      rw [← hz, c.symm_apply_apply]

/-- Every invertible linear operator commuting with L on the original orbit is the identity. -/
theorem sourceOrbit_binary_centralizer_eq_one
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (f : Additive D.sourceOrbit ≃ₗ[ZMod 2] Additive D.sourceOrbit)
    (hf : ∀ l v, f (doubledSeedAction L D.sourceOrbit
      D.sourceOrbit_component_normalizes l v) =
      doubledSeedAction L D.sourceOrbit D.sourceOrbit_component_normalizes l (f v)) :
    f = LinearEquiv.refl _ _ := by
  obtain ⟨_,_,_,q,hq,e,he,_⟩ := D.sourceOrbit_binary_pair_coordinates h hd F hF hmodel
  exact doubledBinary_centralizer _ q hq e he f hf

/-- The rank bound is on the actual ambient automizer of the whole orbit.
No identification of the whole orbit with the chosen seed is made. -/
theorem sourceOrbit_binary_automizer_rank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) : primeRank 2 (ChapterE.Automizer D.sourceOrbit) ≤ 2 := by
  let W := D.sourceOrbit
  let N := normalizer (W : Set G)
  let qN := W.normalizerMonoidHom.rangeRestrict
  let i : L →* ChapterE.Automizer W :=
    qN.comp (inclusion D.sourceOrbit_component_normalizes)
  have hi : i.range = (L.subgroupOf N).map qN := by
    ext a
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨inclusion D.sourceOrbit_component_normalizes l,l.property,rfl⟩
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l,hl⟩,rfl⟩
  let : (L.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer
    (D.sourceOrbit_normalizer_le h.toHypothesis1221)
  let : i.range.Normal := hi ▸ Normal.map inferInstance qN
    W.normalizerMonoidHom.rangeRestrict_surjective
  obtain ⟨_,_,_,q,hq,e,he,_⟩ := D.sourceOrbit_binary_pair_coordinates h hd F hF hmodel
  apply doubledBinary_rank_of_marked_normal_range (ChapterE.automizerRepresentation W)
    (ChapterE.automizerRepresentation_injective W) i q hq e
  intro l v
  exact he l v

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
