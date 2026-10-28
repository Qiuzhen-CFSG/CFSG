module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.Contracts
public import Theory.SpecificGroups.AlternatingSix.M10.Contracts
public import Theory.SpecificGroups.AlternatingSix.M10.Action
public import Theory.SpecificGroups.AlternatingSix.M10.LocalGeometry
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines

/-!
# The marked M₁₀ geometry in the source normalizer

The involution z fixes X and inverts X₁, whereas u inverts X and fixes X₁.
The direct-product decomposition of D = XX₁ therefore proves that uz inverts
all of D. Transport through the specified S₆ isomorphism gives the exact
input to the concrete automorphism-group calculation.

The compatible full-normalizer isomorphism gives an injective homomorphism
Aut(A₆) → G. Its equations on the entire marked S₆ identify the image of the
model nine-group with D, and identify both marked involutions individually.
The independent action and complement calculations in `AlternatingSix.M10`
construct the required geometry. The action theorem supplies normality of
the fixed extension, discharging the complement construction's only extra
premise. Thus `nonempty_m10NormalizerGeometry` needs only the compatible
normalizer isomorphism and the original symmetric-six data. In particular,
its three-transitivity concerns the literal quotient by L ∩ N_G(D), and
its quaternion isomorphism concerns the actual intersection P ∩ L.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), 4.9 and the proof of 4.10, pp.41–42.
-/

@[expose] public section

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup

open Subgroup

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h}

namespace SymmetricSixData

variable (s : SymmetricSixData h a)

private theorem markedNine_factor (x : G) (hx : x ∈ s.markedNine) :
    ∃ y ∈ cubicInG h, ∃ w ∈ s.X1, x = y * w := by
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (cubicInG h) s.X1 s.cubic_disjoint (le_centralizer_iff.mp s.X1_centralizes_X)
  obtain ⟨⟨y, w⟩, hyw⟩ := e.surjective ⟨x, hx⟩
  exact ⟨y, y.property, w, w.property, (congrArg Subtype.val hyw).symm.trans (he y w)⟩

private theorem z_conj_cubic (y : G) (hy : y ∈ cubicInG h) :
    z * y * z⁻¹ = y := by
  have hc := mem_centralizer_singleton_iff.mp ((map_subtype_le _) hy)
  rw [hc.symm, mul_inv_cancel_right]

theorem z_normalizes_markedNine : z ∈ normalizer (s.markedNine : Set G) := by
  have hz : z * z = 1 := by
    simpa only [h.involution, pow_two] using pow_orderOf_eq_one z
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hc : ∀ x ∈ s.markedNine, z * x * z⁻¹ ∈ s.markedNine := by
    intro x hx
    obtain ⟨y, hy, w, hw, rfl⟩ := s.markedNine_factor x hx
    have he : z * (y * w) * z⁻¹ = y * w⁻¹ := by
      calc
        z * (y * w) * z⁻¹ = (z * y * z⁻¹) * (z * w * z⁻¹) := by group
        _ = y * w⁻¹ := by rw [z_conj_cubic y hy, s.z_inverts_X1 w hw]
    rw [he]
    exact s.markedNine.mul_mem
      ((show cubicInG h ≤ s.markedNine from le_sup_left) hy)
      ((show s.X1 ≤ s.markedNine from le_sup_right) (s.X1.inv_mem hw))
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hc x
  · intro hx
    simpa only [hzi, mul_assoc, ← mul_assoc z z, hz, one_mul, mul_one] using hc _ hx

/-- The source's central involution candidate inverts the whole nine-group. -/
theorem uz_inverts_markedNine (x : G) (hx : x ∈ s.markedNine) :
    (s.u * z) * x * (s.u * z)⁻¹ = x⁻¹ := by
  obtain ⟨y, hy, w, hw, rfl⟩ := s.markedNine_factor x hx
  have hcy : (s.u * z) * y * (s.u * z)⁻¹ = y⁻¹ := by
    calc
      (s.u * z) * y * (s.u * z)⁻¹ = s.u * (z * y * z⁻¹) * s.u⁻¹ := by group
      _ = y⁻¹ := by rw [z_conj_cubic y hy, s.u_inverts_cubicInG y hy]
  have hcw : (s.u * z) * w * (s.u * z)⁻¹ = w⁻¹ := by
    calc
      (s.u * z) * w * (s.u * z)⁻¹ = s.u * (z * w * z⁻¹) * s.u⁻¹ := by group
      _ = s.u * w⁻¹ * s.u⁻¹ := by rw [s.z_inverts_X1 w hw]
      _ = w⁻¹ := by rw [s.u_centralizes_X1 _ (s.X1.inv_mem hw), mul_inv_cancel_right]
  have hcomm : Commute y w := ((s.X1_centralizes_X hw) y hy)
  calc
    (s.u * z) * (y * w) * (s.u * z)⁻¹ =
        ((s.u * z) * y * (s.u * z)⁻¹) * ((s.u * z) * w * (s.u * z)⁻¹) := by group
    _ = y⁻¹ * w⁻¹ := by rw [hcy, hcw]
    _ = (y * w)⁻¹ := by rw [mul_inv_rev, hcomm.inv_inv.eq]

/-- The nine-group in the specified six-letter coordinates. -/
def m10NineCoordinates : Subgroup (Equiv.Perm (Fin 6)) :=
  (s.markedNine.subgroupOf s.S).map s.equiv.toMonoidHom

theorem card_m10NineCoordinates : Nat.card s.m10NineCoordinates = 9 := by
  rw [m10NineCoordinates, card_map_of_injective s.equiv.injective,
    Nat.card_congr (subgroupOfEquivOfLe s.markedNine_le).toEquiv, s.card_markedNine]

/-- The original markings, with no complement or M₁₀ geometry assumed. -/
noncomputable def m10Marking : AlternatingSix.M10.Marking where
  D := s.m10NineCoordinates
  card_D := s.card_m10NineCoordinates
  z := s.equiv ⟨z, s.z_mem⟩
  u := s.equiv ⟨s.u, s.u_mem⟩
  z_swap := s.z_swap
  u_swap := s.u_swap
  commute := by
    have hc : Commute (⟨s.u, s.u_mem⟩ : s.S) ⟨z, s.z_mem⟩ :=
      Subtype.ext s.u_commutes_z.eq
    exact hc.map s.equiv.toMonoidHom
  z_normalizes := by
    apply (s.markedNine.subgroupOf s.S).le_normalizer_map s.equiv.toMonoidHom
    apply mem_map.mpr
    refine ⟨⟨z, s.z_mem⟩, ?_, rfl⟩
    rw [← subgroupOf_normalizer_eq s.markedNine_le]
    exact s.z_normalizes_markedNine
  b_inverts := by
    rintro x ⟨y, hy, rfl⟩
    have he : (⟨s.u, s.u_mem⟩ * ⟨z, s.z_mem⟩) * y *
        (⟨s.u, s.u_mem⟩ * ⟨z, s.z_mem⟩)⁻¹ = y⁻¹ :=
      Subtype.ext (s.uz_inverts_markedNine y hy)
    simpa only [map_mul, map_inv, MulEquiv.coe_toMonoidHom] using congrArg s.equiv he

end SymmetricSixData

namespace SymmetricNormalizerData

open AlternatingSix.ShadowLocal

variable {s : SymmetricSixData h a} (n : SymmetricNormalizerData s)

/-- Embed the concrete automorphism group using the inverse of the supplied,
compatible normalizer isomorphism. -/
noncomputable def modelEmbedding : AutA6 →* G :=
  (normalizer (s.S : Set G)).subtype.comp n.equiv.symm.toMonoidHom

theorem modelEmbedding_injective : Function.Injective n.modelEmbedding :=
  Subtype.val_injective.comp n.equiv.symm.injective

theorem modelEmbedding_range : n.modelEmbedding.range = normalizer (s.S : Set G) := by
  rw [modelEmbedding, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr n.equiv.symm.surjective, ← MonoidHom.range_eq_map, range_subtype]

/-- Compatibility holds on the entire original symmetric subgroup. -/
theorem modelEmbedding_on_s (x : s.S) :
    n.modelEmbedding (permutationAction (s.equiv x)) = x := by
  rw [← n.on_s x]
  change ((n.equiv.symm (n.equiv ⟨x, s.S.le_normalizer x.property⟩)) : G) = x
  rw [n.equiv.symm_apply_apply]

theorem modelEmbedding_z : n.modelEmbedding (permutationAction s.m10Marking.z) = z :=
  n.modelEmbedding_on_s ⟨z, s.z_mem⟩

theorem modelEmbedding_b :
    n.modelEmbedding (permutationAction (s.m10Marking.u * s.m10Marking.z)) = s.u * z := by
  rw [map_mul, map_mul, modelEmbedding_z]
  exact congrArg (· * z) (n.modelEmbedding_on_s ⟨s.u, s.u_mem⟩)

/-- The model nine-group has exactly the required ambient image. -/
theorem modelEmbedding_nine :
    (AlternatingSix.M10.nine s.m10Marking.D).map n.modelEmbedding = s.markedNine := by
  apply le_antisymm
  · rintro x ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    change (y : G) ∈ s.markedNine at hy
    simpa only [MulEquiv.coe_toMonoidHom, n.modelEmbedding_on_s] using hy
  · intro x hx
    refine ⟨permutationAction (s.equiv ⟨x, s.markedNine_le hx⟩), ?_,
      n.modelEmbedding_on_s ⟨x, s.markedNine_le hx⟩⟩
    exact ⟨s.equiv ⟨x, s.markedNine_le hx⟩,
      ⟨⟨x, s.markedNine_le hx⟩, hx, rfl⟩, rfl⟩

open AlternatingSix.M10

/-- Normalizers transport relative to the actual image N_G(S), not to G. -/
theorem modelEmbedding_normalizer (E : Subgroup AutA6) :
    (normalizer (E : Set AutA6)).map n.modelEmbedding =
      normalizer (s.S : Set G) ⊓ normalizer (E.map n.modelEmbedding : Set G) := by
  have he : (normalizer (E.map n.modelEmbedding : Set G)).comap n.modelEmbedding =
      normalizer (E : Set AutA6) := by
    rw [comap_normalizer_eq_of_le_range (E.map_le_range n.modelEmbedding),
      comap_map_eq_self_of_injective n.modelEmbedding_injective]
  rw [← he, map_comap_eq, n.modelEmbedding_range]

/-- The ambient image of the fixed concrete extension. -/
noncomputable def modelL : Subgroup G := extension.map n.modelEmbedding

theorem modelL_le : n.modelL ≤ normalizer (s.S : Set G) := by
  rw [← n.modelEmbedding_range]
  exact extension.map_le_range n.modelEmbedding

noncomputable def modelLEquiv : extension ≃* n.modelL :=
  extension.equivMapOfInjective n.modelEmbedding n.modelEmbedding_injective

/-- This equality preserves the literal intersection in the source contract. -/
theorem modelEmbedding_stabilizer :
    (stabilizer s.m10Marking.D).map n.modelEmbedding = s.markedK n.modelL := by
  rw [stabilizer, map_inf _ _ _ n.modelEmbedding_injective,
    n.modelEmbedding_normalizer, n.modelEmbedding_nine]
  change n.modelL ⊓ (normalizer (s.S : Set G) ⊓ normalizer (s.markedNine : Set G)) =
    n.modelL ⊓ normalizer (s.markedNine : Set G)
  rw [← inf_assoc, inf_eq_left.mpr n.modelL_le]

private noncomputable def modelCosetMap :
    (extension ⧸ (stabilizer s.m10Marking.D).subgroupOf extension) →ₑ[n.modelLEquiv.toMonoidHom]
      (n.modelL ⧸ (s.markedK n.modelL).subgroupOf n.modelL) where
  toFun q := Quotient.liftOn' q
    (fun x => (n.modelLEquiv x : n.modelL ⧸ (s.markedK n.modelL).subgroupOf n.modelL)) (by
      intro x y hxy
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      change (n.modelEmbedding (x : AutA6))⁻¹ * n.modelEmbedding (y : AutA6) ∈
        s.markedK n.modelL
      rw [← map_inv, ← map_mul, ← n.modelEmbedding_stabilizer]
      exact mem_map_of_mem _ hxy)
  map_smul' x q := by
    induction q using Quotient.inductionOn' with | h y =>
      change (n.modelLEquiv (x * y) : n.modelL ⧸ (s.markedK n.modelL).subgroupOf n.modelL) =
        (n.modelLEquiv x * n.modelLEquiv y : n.modelL)
      rw [map_mul]

private theorem modelCosetMap_surjective : Function.Surjective n.modelCosetMap := by
  intro q
  induction q using Quotient.inductionOn' with | h x =>
    obtain ⟨y, rfl⟩ := n.modelLEquiv.surjective x
    exact ⟨(y : extension ⧸ (stabilizer s.m10Marking.D).subgroupOf extension), rfl⟩

/-- Three-transitivity is transported to precisely L/(K.subgroupOf L). -/
theorem modelL_transitive (af : ActionFacts s.m10Marking.D) :
    MulAction.IsMultiplyPretransitive n.modelL
      (n.modelL ⧸ (s.markedK n.modelL).subgroupOf n.modelL) 3 := by
  let := af.transitive
  exact MulAction.IsPretransitive.of_embedding n.modelCosetMap_surjective

/-- The marked semidihedral presentation is preserved by the model embedding. -/
theorem modelEmbedding_semidihedral (P : Subgroup AutA6)
    (hp : ∃ p q : P, orderOf p = 8 ∧ orderOf q = 2 ∧
      q * p * q⁻¹ = p ^ 3 ∧ zpowers p ⊔ zpowers q = ⊤) :
    ∃ p q : P.map n.modelEmbedding, orderOf p = 8 ∧ orderOf q = 2 ∧
      q * p * q⁻¹ = p ^ 3 ∧ zpowers p ⊔ zpowers q = ⊤ := by
  let e := P.equivMapOfInjective n.modelEmbedding n.modelEmbedding_injective
  obtain ⟨p, q, hp, hq, hrel, hgen⟩ := hp
  refine ⟨e p, e q, (e.orderOf_eq p).trans hp, (e.orderOf_eq q).trans hq, ?_, ?_⟩
  · simpa only [map_mul, map_inv, map_pow] using congrArg e hrel
  · have hh := congrArg (Subgroup.map e.toMonoidHom) hgen
    simpa only [Subgroup.map_sup, MonoidHom.map_zpowers,
      map_top_of_surjective e.toMonoidHom e.surjective, MulEquiv.coe_toMonoidHom] using hh

/-- Complete transport of the two independent concrete model calculations.
The existence of `af` and `lf` remains the mathematical model obligation;
neither the ambient geometry nor any of its fields is assumed here. -/
noncomputable def m10GeometryOfModelFacts (af : ActionFacts s.m10Marking.D)
    (lf : LocalFacts s.m10Marking) : M10NormalizerGeometry s where
  L := n.modelL
  L_le := n.modelL_le
  D_le := by
    rw [← n.modelEmbedding_nine]
    exact map_mono af.nine_le
  card_L := by
    rw [modelL, card_map_of_injective n.modelEmbedding_injective]
    exact af.card
  card_K := by
    rw [← n.modelEmbedding_stabilizer, card_map_of_injective n.modelEmbedding_injective]
    exact af.card_stabilizer
  transitive := n.modelL_transitive af
  z_normalizes := by
    have hz : permutationAction s.m10Marking.z ∈ normalizer (extension : Set AutA6) := by
      rw [normalizer_eq_top_iff.mpr af.normal]
      trivial
    have hm := extension.le_normalizer_map n.modelEmbedding (mem_map_of_mem _ hz)
    simpa only [modelL, n.modelEmbedding_z] using hm
  z_not_mem := by
    intro hz
    have hz' : n.modelEmbedding (permutationAction s.m10Marking.z) ∈ n.modelL := by
      simpa only [n.modelEmbedding_z] using hz
    exact af.swap_not_mem _ s.m10Marking.z_swap
      ((mem_map_iff_mem n.modelEmbedding_injective).mp hz')
  P := lf.P.map n.modelEmbedding
  card_P := by rw [card_map_of_injective n.modelEmbedding_injective, lf.card_P]
  semidihedral := n.modelEmbedding_semidihedral lf.P lf.semidihedral
  intersection := by
    rw [← n.modelEmbedding_nine, ← n.modelEmbedding_normalizer, lf.normalizer_eq,
      Subgroup.map_sup]
  disjoint := by
    rw [← n.modelEmbedding_nine]
    exact disjoint_map n.modelEmbedding_injective lf.disjoint
  z_mem_P := by
    simpa only [n.modelEmbedding_z] using mem_map_of_mem n.modelEmbedding lf.z_mem
  center_P := by
    rw [map_center_image_of_injective lf.P n.modelEmbedding n.modelEmbedding_injective,
      ← map_map, lf.center_P, MonoidHom.map_zpowers, n.modelEmbedding_b]
  quaternion := by
    obtain ⟨q⟩ := lf.quaternion
    exact ⟨(MulEquiv.subgroupCongr
      (map_inf lf.P extension n.modelEmbedding n.modelEmbedding_injective).symm).trans
        (((lf.P ⊓ extension).equivMapOfInjective n.modelEmbedding
          n.modelEmbedding_injective).symm.trans q)⟩
  b_mem_K := by
    rw [← n.modelEmbedding_b, ← n.modelEmbedding_stabilizer]
    exact mem_map_of_mem _ lf.b_mem
  r := n.modelEmbedding lf.r
  r_mem := mem_map_of_mem _ lf.r_mem
  r_sq := by rw [← map_mul, lf.r_sq, map_one]
  r_not_mem_P := fun hr => lf.r_not_mem_P ((mem_map_iff_mem n.modelEmbedding_injective).mp hr)
  r_normalizes_P := lf.P.le_normalizer_map n.modelEmbedding (mem_map_of_mem _ lf.r_normalizes_P)
  cover := by
    rintro _ ⟨l, hl, rfl⟩
    rcases af.cover lf.r lf.r_mem lf.r_not_mem_stabilizer l hl with hk | hk
    · left
      rw [← n.modelEmbedding_stabilizer]
      exact mem_map_of_mem _ hk
    · right
      obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hk
      apply DoubleCoset.mem_doubleCoset.mpr
      rw [← n.modelEmbedding_stabilizer]
      exact ⟨n.modelEmbedding x, mem_map_of_mem _ hx,
        n.modelEmbedding y, mem_map_of_mem _ hy, by simp only [map_mul]⟩

/-- Construct the marked M₁₀ subgroup, its quotient action, and its complete
semidihedral geometry from the compatible full-normalizer isomorphism.
Both concrete model calculations are discharged here, including the
normality premise used to align the complement with the source markings. -/
theorem nonempty_m10NormalizerGeometry (n : SymmetricNormalizerData s) :
    Nonempty (M10NormalizerGeometry s) := by
  have af := actionFacts s.m10Marking.D s.m10Marking.card_D
  obtain ⟨lf⟩ := LocalGeometry.nonempty_localFacts s.m10Marking af.normal
  exact ⟨n.m10GeometryOfModelFacts af lf⟩

end SymmetricNormalizerData

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
