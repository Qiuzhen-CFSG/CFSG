module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2.MSMovingKernel

/-!
# Intrinsic kernels in embedded G₂ moving covers

Transport the natural-cover criterion through an injective conjugation
embedding. The entire central kernel lies in the original subgroup commutator;
its nonidentity elements are precisely the elements that are not single
commutators of the original actor and moving subgroup. Applying this criterion
in both directions identifies two embedded kernels, using inversion to reverse
the order of a commutator.

MSVertexKernel applies these facts to the actual critical vertices arising from
Sylow-normalizer escape. Source: Meierfrankenfeld--Stellmacher (1993), (1.5)(iv)
and the G₂ argument in (3.2), printed pp.843 and865--866. This is the kernel
comparison preceding the field comparison, retained by the line-action owner;
final 11.2.3 assembly belongs to qt-d-1222-natural-normalizer-source.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.OneCohomology
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS

private theorem embedded_displacement
    {G J W : Type*} [Group G] [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    (A : Subgroup G) (σ : Representation (ZMod 2) J W)
    (j : Multiplicative W →* G) (δ : A →* J)
    (hc : ∀ (a : A) w, j (Multiplicative.ofAdd (σ (δ a) w)) =
      a.val * j (Multiplicative.ofAdd w) * a.val⁻¹)
    (a : A) (w : W) :
    j (Multiplicative.ofAdd (σ (δ a) w - w)) =
      ⁅a.val,j (Multiplicative.ofAdd w)⁆ := by
  rw [ofAdd_sub,map_div,div_eq_mul_inv,hc]
  rfl

private theorem embedded_moved_group
    {G J W : Type*} [Group G] [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    (A U : Subgroup G) (σ : Representation (ZMod 2) J W)
    (j : Multiplicative W →* G) (hjr : j.range = U) (δ : A →* J)
    (hc : ∀ (a : A) w, j (Multiplicative.ofAdd (σ (δ a) w)) =
      a.val * j (Multiplicative.ofAdd w) * a.val⁻¹) :
    (Coinvariants.ker (σ.comp δ.range.subtype)).toAddSubgroup.toSubgroup.map j = ⁅A,U⁆ := by
  let P := AddSubgroup.toZModSubmodule 2 ((⁅A,U⁆).comap j).toAddSubgroup'
  have hle : Coinvariants.ker (σ.comp δ.range.subtype) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨⟨a,ha⟩,w⟩,rfl⟩
    obtain ⟨b,rfl⟩ := ha
    change j (Multiplicative.ofAdd (σ (δ b) w - w)) ∈ ⁅A,U⁆
    rw [embedded_displacement A σ j δ hc]
    exact commutator_mem_commutator b.property (hjr ▸ ⟨_,rfl⟩)
  apply le_antisymm
  · rintro _ ⟨w,hw,rfl⟩
    exact hle hw
  · apply commutator_le.mpr
    intro a ha u hu
    obtain ⟨w,rfl⟩ := show u ∈ j.range from hjr.symm ▸ hu
    refine ⟨Multiplicative.ofAdd (σ (δ ⟨a,ha⟩) w.toAdd - w.toAdd),?_,?_⟩
    · exact Coinvariants.sub_mem_ker (ρ := σ.comp δ.range.subtype) ⟨δ ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩⟩ w.toAdd
    · exact embedded_displacement A σ j δ hc ⟨a,ha⟩ w.toAdd

/-- Transport the central-kernel criterion through an original conjugation
embedding, with the original actor and subgroup commutator retained. -/
theorem embedded_offender_kernel
    {G J V : Type*} [Group G] [Group J] [Finite J]
    [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
    (F : BinaryField) (hF : F.degree = 2)
    (s : MovedSection ρ B) (e : ActionEquiv (s.action.comp B.subtype) (binaryG2 F))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hf : Function.Injective (MovedSection.ambientAction s e))
    (A U K : Subgroup G) (j : Multiplicative s.space.toSubmodule →* G)
    (hj : Function.Injective j) (hjr : j.range = U) (δ : A →* J)
    (hconj : ∀ (a : A) w, j (Multiplicative.ofAdd (s.space.toRepresentation (δ a) w)) =
      a.val * j (Multiplicative.ofAdd w) * a.val⁻¹)
    (hK : (MovedSection.coverProjection s e).toLinearMap.ker.toAddSubgroup.toSubgroup.map j = K)
    (hA : BinaryOffender.IsOffender (MovedSection.ambientAction s e) δ.range) :
    K ≤ ⁅A,U⁆ ∧ ∀ x ∈ ⁅A,U⁆, x ≠ 1 →
      (x ∈ K ↔ ¬ ∃ a ∈ A, ∃ u ∈ U, ⁅a,u⁆ = x) := by
  obtain ⟨hle,hcrit⟩ := moved_cover_offender_kernel F hF s e hp hf δ.range hA
  have hm := embedded_moved_group A U s.space.toRepresentation j hjr δ hconj
  refine ⟨?_,?_⟩
  · rw [←hK,←hm]
    exact map_mono hle
  · intro x hx hne
    obtain ⟨w,hw,rfl⟩ := hm.symm ▸ hx
    have hwne : w.toAdd ≠ 0 := by
      intro hz
      apply hne
      have he : w = 1 := congrArg Multiplicative.ofAdd hz
      rw [he,map_one]
    have hmem : j w ∈ K ↔ MovedSection.coverProjection s e w.toAdd = 0 := by
      rw [←hK]
      constructor
      · rintro ⟨v,hv,he⟩
        exact hj he ▸ hv
      · intro hv
        exact ⟨w,hv,rfl⟩
    rw [hmem,hcrit w.toAdd hw hwne]
    apply not_congr
    constructor
    · rintro ⟨d,⟨a,rfl⟩,v,hv⟩
      refine ⟨a,a.property,j (Multiplicative.ofAdd v),hjr ▸ ⟨_,rfl⟩,?_⟩
      rw [←embedded_displacement A s.space.toRepresentation j δ hconj,hv]
      rfl
    · rintro ⟨a,ha,u,hu,he⟩
      obtain ⟨v,rfl⟩ := show u ∈ j.range from hjr.symm ▸ hu
      refine ⟨δ ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩,v.toAdd,?_⟩
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [embedded_displacement A s.space.toRepresentation j δ hconj]
      exact he

/-- Two central kernels with the intrinsic non-single-commutator criterion
agree as subgroups of the original group. -/
theorem embedded_kernels_eq
    {G : Type*} [Group G] (A U K L : Subgroup G)
    (hK : K ≤ ⁅A,U⁆)
    (hk : ∀ x ∈ ⁅A,U⁆, x ≠ 1 → (x ∈ K ↔ ¬ ∃ a ∈ A, ∃ u ∈ U, ⁅a,u⁆ = x))
    (hL : L ≤ ⁅U,A⁆)
    (hl : ∀ x ∈ ⁅U,A⁆, x ≠ 1 → (x ∈ L ↔ ¬ ∃ u ∈ U, ∃ a ∈ A, ⁅u,a⁆ = x)) :
    K = L := by
  have half (A U K L : Subgroup G)
      (hK : K ≤ ⁅A,U⁆)
      (hk : ∀ x ∈ ⁅A,U⁆, x ≠ 1 → (x ∈ K ↔ ¬ ∃ a ∈ A, ∃ u ∈ U, ⁅a,u⁆ = x))
      (hl : ∀ x ∈ ⁅U,A⁆, x ≠ 1 → (x ∈ L ↔ ¬ ∃ u ∈ U, ∃ a ∈ A, ⁅u,a⁆ = x)) :
      K ≤ L := by
    intro x hx
    by_cases he : x = 1
    · simp [he]
    have hi : x⁻¹ ∈ ⁅U,A⁆ := by
      rw [commutator_comm]
      exact (⁅A,U⁆).inv_mem (hK hx)
    apply L.inv_mem_iff.mp
    apply (hl x⁻¹ hi (inv_ne_one.mpr he)).mpr
    rintro ⟨u,hu,a,ha,heq⟩
    apply (hk x (hK hx) he).mp hx
    refine ⟨a,ha,u,hu,?_⟩
    rw [←commutatorElement_inv u a,heq,inv_inv]
  exact le_antisymm (half A U K L hK hk hl) (half U A L K hL hl hk)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
