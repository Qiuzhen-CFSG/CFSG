module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear.G2Four

/-!
# Nonbinary exceptional critical actions

The genuine ambient offender theorem gives rank and fixed codimension 3n,
so reciprocal index bounds force both critical images to be offenders for
every n > 1. The vertex record retains the original quotient, natural cover
and its kernel, with the original degree n rather than degree two.
These are the inputs for the point-pair exclusion in G2Exclusion.

The argument extends LineAction/G2/MSReciprocal and MSCriticalActors without
changing their public field-four interfaces. Source: MS93 (3.2), pp.865--866;
Aschbacher--Smith 11.1.5, p.765. Octonion attribution: LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Representation.OneCohomology
open scoped IsMulCommutative Pointwise commutatorElement
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear.Exceptional
variable {n : ℕ}
private def binaryLinearEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module (ZMod 2) A] [Module (ZMod 2) B] (e : A ≃+ B) : A ≃ₗ[ZMod 2] B :=
  { e with map_smul' := ZMod.map_smul e }

private theorem ambient_offender_le_additive
    {J W F : Type*} [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    [Field F] [Finite F] [CharP F 2]
    (ρ : Representation (ZMod 2) J W) (B : Subgroup J) [B.Normal]
    (e : B ≃* Atlas.G2.Model F) (E : W ≃+ Atlas.G2.Natural.Space F)
    (he : ∀ (b : B) v, E (ρ (b : J) v) = Atlas.G2.Natural.action F (e b) (E v))
    (hf : Function.Injective ρ) {n : ℕ} (hn : 1 < n) (hc : Nat.card F = 2^n)
    (A : Subgroup J) (hA : IsOffender ρ A) : A ≤ B := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  apply Atlas.G2.Natural.Normalizer.ambient_offender_le F ρ B e
    (binaryLinearEquiv E) he hf hn hc hA

/-- An offender in a faithful ambient nonbinary G₂ natural action is inner;
its binary rank and fixed codimension are both three times the field degree. -/
theorem ambient_offender_rank
    {J : Type*} [Group J] [Finite J] (F : BinaryField) (hF : 1 < F.degree)
    (ρ : Representation (ZMod 2) J (Atlas.G2.Natural.Space F.Carrier))
    (B : Subgroup J) [B.Normal] (e : B ≃* Atlas.G2.Model F.Carrier)
    (he : ∀ (b : B) v, ρ (b : J) v = Atlas.G2.Natural.action F.Carrier (e b) v)
    (hf : Function.Injective ρ) (A : Subgroup J) (hA : IsOffender ρ A) :
    A ≤ B ∧ rank A = 3 * F.degree ∧ fixedCodim ρ A = 3 * F.degree := by
  have hc : Nat.card F.Carrier = 2^F.degree := F.card_eq
  have hAB := ambient_offender_le_additive ρ B e (AddEquiv.refl _) he hf hF hc A hA
  have ho := (hA.subgroupOf ρ hAB).map_equivariant (ρ.comp B.subtype)
    (Atlas.G2.NaturalOffenders.binaryNatural (F := F.Carrier))
    e.toMonoidHom e.injective (@binaryLinearEquiv _ _ _ _ _ _ (AddEquiv.refl _)) (fun b v => he b v)
  have hr := Atlas.G2.NaturalOffenders.natural_offender_rank hc (by omega : 0 < F.degree) _ ho
  have hd := Atlas.G2.NaturalOffenders.natural_offender_fixedCodim hc (by omega : 0 < F.degree) _ ho
  rw [rank_map_injective _ e.injective,rank_subgroupOf hAB] at hr
  have hde := fixedCodim_map_equivariant (ρ.comp B.subtype)
    (Atlas.G2.NaturalOffenders.binaryNatural (F := F.Carrier)) e.toMonoidHom
    (@binaryLinearEquiv _ _ _ _ _ _ (AddEquiv.refl _)) (fun b v => he b v) (A.subgroupOf B)
  rw [fixedCodim_subgroupOf ρ hAB,hd] at hde
  exact ⟨hAB,hr,hde⟩

/-- Reciprocal index bounds force both actual images to be offenders. -/
theorem reciprocal_natural_offenders
    {J₁ J₂ : Type*} [Group J₁] [Group J₂] [Finite J₁] [Finite J₂]
    (F₁ F₂ : BinaryField) (hF₁ : 1 < F₁.degree) (hF₂ : 1 < F₂.degree)
    (ρ₁ : Representation (ZMod 2) J₁ (Atlas.G2.Natural.Space F₁.Carrier))
    (ρ₂ : Representation (ZMod 2) J₂ (Atlas.G2.Natural.Space F₂.Carrier))
    (B₁ : Subgroup J₁) [B₁.Normal] (B₂ : Subgroup J₂) [B₂.Normal]
    (e₁ : B₁ ≃* Atlas.G2.Model F₁.Carrier) (e₂ : B₂ ≃* Atlas.G2.Model F₂.Carrier)
    (he₁ : ∀ (b : B₁) v, ρ₁ (b : J₁) v = Atlas.G2.Natural.action F₁.Carrier (e₁ b) v)
    (he₂ : ∀ (b : B₂) v, ρ₂ (b : J₂) v = Atlas.G2.Natural.action F₂.Carrier (e₂ b) v)
    (hf₁ : Function.Injective ρ₁) (hf₂ : Function.Injective ρ₂)
    (A₁ : Subgroup J₁) (A₂ : Subgroup J₂)
    (hA₁ : IsElementaryTwo A₁) (hA₂ : IsElementaryTwo A₂)
    (h₁₂ : 2 ^ fixedCodim ρ₁ A₁ ≤ Nat.card A₂)
    (h₂₁ : 2 ^ fixedCodim ρ₂ A₂ ≤ Nat.card A₁) :
    IsOffender ρ₁ A₁ ∧ IsOffender ρ₂ A₂ := by
  rw [hA₂.card_eq_two_pow_rank,Nat.pow_le_pow_iff_right (by decide : 1 < 2)] at h₁₂
  rw [hA₁.card_eq_two_pow_rank,Nat.pow_le_pow_iff_right (by decide : 1 < 2)] at h₂₁
  by_cases hle : rank A₂ ≤ rank A₁
  · have ha : IsOffender ρ₁ A₁ := ⟨hA₁,h₁₂.trans hle⟩
    obtain ⟨_,hr,hd⟩ := ambient_offender_rank F₁ hF₁ ρ₁ B₁ e₁ he₁ hf₁ A₁ ha
    exact ⟨ha,hA₂,by omega⟩
  · have hb : IsOffender ρ₂ A₂ := ⟨hA₂,h₂₁.trans (by omega)⟩
    obtain ⟨_,hr,hd⟩ := ambient_offender_rank F₂ hF₂ ρ₂ B₂ e₂ he₂ hf₂ A₂ hb
    exact ⟨⟨hA₁,by omega⟩,hb⟩

/-- Natural coordinates for the literal full vertex quotient. Every map is
anchored to the original stabilizer and moving subgroup. -/
structure VertexAction {M J : Type*} [Group M] [Group J]
    (n : ℕ) (R₀ : Subgroup M) (a : Vertex R₀) (B : Subgroup J) where
  field : BinaryField
  degree : field.degree = n
  nonbinary : 1 < field.degree
  component_normal : B.Normal
  componentEquiv : B ≃* Atlas.G2.Model field.Carrier
  action : Representation (ZMod 2) J (Atlas.G2.Natural.Space field.Carrier)
  component_apply : ∀ (b : B) v,
    action (b : J) v = Atlas.G2.Natural.action field.Carrier (componentEquiv b) v
  faithful : Function.Injective action
  quotient : stabilizer R₀ a →* J
  quotient_surjective : Function.Surjective quotient
  kernel_core : quotient.ker.map (stabilizer R₀ a).subtype = Q R₀ a
  kernel_centralizer : quotient.ker.map (stabilizer R₀ a).subtype = C R₀ a
  component_image : ((Ltilde R₀ a).subgroupOf (stabilizer R₀ a)).map quotient = B
  projection : U R₀ a →* Multiplicative (Atlas.G2.Natural.Space field.Carrier)
  projection_surjective : Function.Surjective projection
  projection_kernel : projection.ker.map (U R₀ a).subtype =
    U R₀ a ⊓ centralizer (Ltilde R₀ a : Set (FreeAmalgam R₀))
  conjugate : ∀ (g : stabilizer R₀ a) (u : U R₀ a),
    projection ⟨g.val*u.val*g.val⁻¹,
      (mem_normalizer_iff.mp (U_normalized a g.property) u.val).mp u.property⟩ =
        Multiplicative.ofAdd (action (quotient g) (projection u).toAdd)

variable {M J : Type*} [Group M] [Finite M] [Group J]
  {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R} {B : Subgroup J}

/-- The original critical image is elementary and nontrivial, has the exact
centralizer index, and satisfies the reciprocal fixed-space bound. -/
theorem critical_actor_bounds (path : CriticalPath R geometry a z)
    (hb : 0 < geometry.b R) (hcomm : ⁅Z R a,Z R z⁆ ≠ ⊥)
    (E : VertexAction n R z B) :
    IsElementaryTwo (criticalActor path E.quotient).range ∧
      Nat.card (criticalActor path E.quotient).range =
        (centralizer (Z R z : Set (FreeAmalgam R))).relIndex (Z R a) ∧
      2 ^ fixedCodim E.action (criticalActor path E.quotient).range ≤
        (centralizer (Z R a : Set (FreeAmalgam R))).relIndex (Z R z) := by
  let := finite_Z R a
  let := finite_Z R z
  let : Finite (U R z) := Finite.of_injective (inclusion (U_le_Z z)) (inclusion_injective _)
  let : IsElementaryAbelian 2 (Z R a) := geometry.Z_elementary hb a path.start_color
  let δ := criticalActor path E.quotient
  have hδ : δ.ker = (centralizer (Z R z : Set (FreeAmalgam R))).subgroupOf (Z R a) :=
    ChapterC.RankTwo.Sp4Four.SourceComparison.restricted_kernel_of_mapped_centralizer
      _ _ _ _ E.quotient E.kernel_centralizer
  have hc : Nat.card δ.range =
      (centralizer (Z R z : Set (FreeAmalgam R))).relIndex (Z R a) := by
    change Nat.card δ.range = ((centralizer (Z R z : Set (FreeAmalgam R))).subgroupOf (Z R a)).index
    rw [←hδ,index_ker]
  have he : IsElementaryTwo δ.range := by
    refine ⟨?_,IsElementaryAbelian.of_surjective δ.rangeRestrict δ.rangeRestrict_surjective⟩
    intro hz
    have hi : (centralizer (Z R z : Set (FreeAmalgam R))).relIndex (Z R a) = 1 := by
      rw [←hc,hz,card_bot]
    exact hcomm (commutator_eq_bot_iff_le_centralizer.mpr (relIndex_eq_one.mp hi))
  have hn : Z R a ≤ normalizer (U R z : Set (FreeAmalgam R)) :=
    (Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color)
      path.critical.1.le).trans (U_normalized z)
  refine ⟨he,hc,?_⟩
  exact (natural_fixed_index_le E.action _ _ hn E.projection E.projection_surjective
    δ (fun x u => E.conjugate
      (inclusion (Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color)
        path.critical.1.le) x) u)).trans
      (relIndex_le_of_le_right (U_le_Z z) index_ne_zero_of_finite)


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear.Exceptional
