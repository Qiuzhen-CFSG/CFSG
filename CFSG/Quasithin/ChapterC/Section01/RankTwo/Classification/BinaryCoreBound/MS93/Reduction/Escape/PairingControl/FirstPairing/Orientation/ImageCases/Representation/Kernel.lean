module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.NaturalGeneration.Section
public import Theory.ThreeSubgroups

/-!
# Commutator kernels on a single natural section

Write B for the residual-fixed preimage in H/N. The bounds [H,[Q,L]] ≤ D
and [B,Q] ≤ D make the kernel of any commutator row invariant under LQ.
The genuine natural coordinates on H/B force this kernel to be B or H.
For abelian H, evaluation at an element is a homomorphism to the actual
commutator quotient. A nonzero row therefore preserves the index of every
subgroup modulo B. Neither the actor order nor a dimension label replaces
the order of this commutator image.

All normality is in the supplied finite group A. The target uses relative
index, so no containment of D in the commutator subgroup is assumed.
Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(2), printed p.884.
The reused natural-section coordinates are earlier (4.3.1)(iii) mathematics.
-/

public section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.ImageCases
open QuotientApplication.NaturalGeneration
variable {A : Type*} [Group A] [Finite A]
  {π : A →* SL} {Q L H N D : Subgroup A}

/-- The three-subgroups lemma makes the commutator kernel invariant under L.
The radical bound makes it invariant under Q; natural irreducibility then
gives the two possible kernels, retaining the literal fixed preimage. -/
theorem natural_commutator_kernel_dichotomy
    (s : SingleNaturalSection π Q L H N)
    (hL : IsPPerfect 2 L) (hH : IsPGroup 2 H) (hgen : L ⊔ Q = ⊤)
    [D.Normal] (htriple : ⁅H, ⁅Q, L⁆⁆ ≤ D)
    (hfixed : letI := s.normal_kernel; ⁅centralizerModulo H L N, Q⁆ ≤ D)
    (W : Subgroup A) (hW : W ≤ Q) :
    letI := s.normal_kernel
    commutatorPreimage H W D = centralizerModulo H L N ∨
      commutatorPreimage H W D = H := by
  let := s.normal_kernel
  let := s.normal_group
  let B := centralizerModulo H L N
  let C := commutatorPreimage H W D
  have hCH : C ≤ H := commutatorPreimage_le _ _ _
  have hCW : ⁅C, W⁆ ≤ D := commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal
  have hBC : B ≤ C := le_commutatorPreimage (centralizerModulo_le _ _ _)
    ((commutator_mono le_rfl hW).trans hfixed)
  have hHQB : ⁅H, Q⁆ ≤ B := by
    intro x hx
    refine mem_centralizerModulo_iff.mpr ⟨(commutator_le_left H Q) hx, ?_⟩
    intro l hl
    apply s.triple_le
    rw [commutator_comm]
    exact commutator_mem_commutator hl hx
  have hQC : Q ≤ normalizer C := le_normalizer_iff_commutator_le_left.mpr
    ((commutator_mono hCH le_rfl).trans (hHQB.trans hBC))
  have hLC : L ≤ normalizer C := by
    apply le_normalizer_iff_commutator_le_left.mpr
    apply le_commutatorPreimage
    · exact (commutator_mono hCH le_rfl).trans (commutator_le_left _ _)
    · apply commutator_commutator_le_of_rotate (H₁ := C) (H₂ := L) (H₃ := W)
      · rw [commutator_comm L W, commutator_comm _ C]
        exact (commutator_mono hCH (commutator_mono hW le_rfl)).trans htriple
      · rw [commutator_comm W C]
        exact (commutator_mono hCW le_rfl).trans (commutator_le_left D L)
  have htop : (⊤ : Subgroup A) ≤ normalizer C := hgen ▸ sup_le hLC hQC
  let : C.Normal := ⟨fun x hx g => le_normalizer_iff.mp htop g (mem_top _) x hx⟩
  exact Initial.Natural.naturalFactor_dichotomy (sectionCoordinates s hL hH hgen)
    s.projection_surjective C hBC hCH

omit [Finite A] in
/-- The quotient centralizer of one element is the kernel of its commutator row. -/
theorem mem_row_kernel [D.Normal] (r x : A) :
    x ∈ commutatorPreimage H (zpowers r) D ↔ x ∈ H ∧ ⁅r, x⁆ ∈ D := by
  rw [commutatorPreimage_eq_inf_comap_centralizer, mem_inf, mem_comap,
    MonoidHom.map_zpowers, zpowers_eq_closure, centralizer_closure,
    mem_centralizer_singleton_iff]
  apply and_congr_right
  intro _
  rw [eq_comm (a := (QuotientGroup.mk' D) x * (QuotientGroup.mk' D) r),
    ← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
  exact QuotientGroup.eq_one_iff _

/-- A nonzero commutator row on the natural section has precisely its fixed
preimage as kernel, so restriction to any subgroup loses no further index. -/
theorem natural_commutator_image_index
    (s : SingleNaturalSection π Q L H N)
    (hL : IsPPerfect 2 L) (hH : IsPGroup 2 H) (hgen : L ⊔ Q = ⊤)
    [D.Normal] [IsMulCommutative H]
    (htriple : ⁅H, ⁅Q, L⁆⁆ ≤ D)
    (hfixed : letI := s.normal_kernel; ⁅centralizerModulo H L N, Q⁆ ≤ D)
    (S W : Subgroup A) (hS : S ≤ Q) (hW : W ≤ H)
    (hne : ¬ ⁅S, H⁆ ≤ D) :
    letI := s.normal_kernel
    (centralizerModulo H L N).relIndex W ≤ D.relIndex ⁅S, W⁆ := by
  let := s.normal_kernel
  let := s.normal_group
  obtain ⟨r, hr, x, hx, hcomm⟩ : ∃ r ∈ S, ∃ x ∈ H, ⁅r, x⁆ ∉ D := by
    classical
    by_contra! h
    exact hne (commutator_le.mpr h)
  have hkernel : commutatorPreimage H (zpowers r) D = centralizerModulo H L N := by
    rcases natural_commutator_kernel_dichotomy s hL hH hgen htriple hfixed
      (zpowers r) (zpowers_le.mpr (hS hr)) with he | he
    · exact he
    · exact (hcomm ((mem_row_kernel r x).mp (he.symm ▸ hx)).2).elim
  let K := ⁅S, W⁆
  have hKH : K ≤ H := (commutator_mono le_rfl hW).trans (commutator_le_right S H)
  have hcentral : K ≤ centralizer (W : Set A) := by
    intro k hk w hw
    exact congrArg Subtype.val (mul_comm (⟨w, hW hw⟩ : H) ⟨k, hKH hk⟩)
  let row : W →* K := centralCommutatorHom W K hcentral r
    (fun w hw => commutator_mem_commutator hr hw)
  let f := (QuotientGroup.mk' (D.subgroupOf K)).comp row
  have hker : f.ker = (centralizerModulo H L N).subgroupOf W := by
    ext w
    change ((row w : K) : K ⧸ D.subgroupOf K) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    change ⁅r, (w : A)⁆ ∈ D ↔ (w : A) ∈ centralizerModulo H L N
    rw [← hkernel, mem_row_kernel]
    exact ⟨fun h => ⟨hW w.property, h⟩, And.right⟩
  change ((centralizerModulo H L N).subgroupOf W).index ≤ Nat.card (K ⧸ D.subgroupOf K)
  rw [← hker, index_ker]
  exact Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective

/-- A subspace outside the fixed preimage that centralizes W modulo D forces
all of the natural section to centralize W modulo D. -/
theorem natural_commutator_le_of_nonfixed
    (s : SingleNaturalSection π Q L H N)
    (hL : IsPPerfect 2 L) (hH : IsPGroup 2 H) (hgen : L ⊔ Q = ⊤)
    [D.Normal] (htriple : ⁅H, ⁅Q, L⁆⁆ ≤ D)
    (hfixed : letI := s.normal_kernel; ⁅centralizerModulo H L N, Q⁆ ≤ D)
    (W E : Subgroup A) (hW : W ≤ Q) (hE : E ≤ H)
    (hne : letI := s.normal_kernel; ¬ E ≤ centralizerModulo H L N)
    (hcomm : ⁅E, W⁆ ≤ D) : ⁅H, W⁆ ≤ D := by
  let := s.normal_kernel
  have hEC : E ≤ commutatorPreimage H W D := le_commutatorPreimage hE hcomm
  rcases natural_commutator_kernel_dichotomy s hL hH hgen htriple hfixed W hW with he | he
  · exact (hne (hEC.trans_eq he)).elim
  · rw [← he]
    exact commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal

omit [Finite A] in
/-- Faithfulness is checked against the literal matrix action: an actor whose
commutators vanish in natural coordinates belongs to the marked kernel. -/
theorem natural_actor_le_kernel
    (n : RankOnePairing.NaturalFactor π ⊤ H N)
    (S : Subgroup A) (hcomm : ⁅S, H⁆ ≤ N) : S ≤ π.ker := by
  intro r hr
  have hfix (x : H) :
      (n.marking (π r)).val.mulVec (n.coordinates x).toAdd = (n.coordinates x).toAdd := by
    let y : H := ⟨r * (x : A) * r⁻¹,
      le_normalizer_iff.mp n.normalized r (mem_top _) x x.property⟩
    have hk : y * x⁻¹ ∈ n.coordinates.ker := by
      rw [n.kernel]
      exact hcomm (commutator_mem_commutator hr x.property)
    have he : n.coordinates y = n.coordinates x := by
      change n.coordinates (y * x⁻¹) = 1 at hk
      rwa [map_mul, map_inv, mul_inv_eq_one] at hk
    rw [← n.action r (mem_top _) x y rfl, he]
  have hm : (n.marking (π r)).val = (1 : SL).val := by
    apply Matrix.mulVec_injective
    funext v
    obtain ⟨x, hx⟩ := n.surjective (Multiplicative.ofAdd v)
    simpa only [hx, toAdd_ofAdd, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_mulVec] using hfix x
  exact n.marking.injective ((Subtype.ext hm).trans n.marking.map_one.symm)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.ImageCases
