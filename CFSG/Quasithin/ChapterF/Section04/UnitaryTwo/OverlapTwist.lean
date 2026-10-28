module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.AffinePlane
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.PointCentralTwist
public import Theory.Representation.BinaryAlternatingFiveExtension.BorelEmbedding
public import Theory.GroupTheory.Amalgam.TwistTransport
/-!
# Matching the affine and unitary point twists on the literal overlap

Restrict one marked affine-plane equivalence to the centralizer of its
marked root. This constructs an equivalence from the affine Borel model
to the actual unitary flag overlap, with its literal plane commuting square.
Its point embedding pulls the point residual back to the affine height
kernel: the order-96 affine residual lies in the pullback, and the marked
point involution proves that pullback proper in the order-192 overlap.

Both twists fix this kernel and multiply its other coset by the same
marked long root. They therefore agree on every element. In particular
the induced automorphism of the actual overlap extends across the point
inclusion. The final theorem supplies the marked plane equivalence from
AffinePlane, retaining its core marking. The general parameterized result
allows the assembly to reuse exactly the same chosen endpoint maps.

This proves the point-extension input to the overlap adjustment in
Aschbacher--Smith 13.5.17, printed p.922. The complete factorization of
arbitrary overlap discrepancies remains with the final amalgam assembly.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.OverlapTwist
open GreenBook.LieModels.UnitaryFour
open BinaryPermutation BinaryPermutation.AlternatingFiveExtension
open PointInvolution ShortRootFixedFour
local notation "hn" => Nat.le_refl 1
local notation "P" => pointParabolic 1 hn
local notation "R" => planeParabolic 1 hn
local notation "B" => overlap 1 hn
local notation "M" => ProjectiveGroup 1 hn
local notation "A" => AlternatingModel
local notation "Z" => SemidirectProduct.inl (Multiplicative.ofAdd FiveCentralizerGeometry.z)

/-- Restrict the same marked plane equivalence to its literal common Borel. -/
def overlapEquiv (E : A ≃* R)
    (hB : borelEmbedding.range.map E.toMonoidHom = (B).subgroupOf R) : BorelModel ≃* B :=
  (MonoidHom.ofInjective borelEmbedding_injective).trans
    ((E.subgroupMap borelEmbedding.range).trans
      ((MulEquiv.subgroupCongr hB).trans (subgroupOfEquivOfLe (show B≤R by rw [←exact_overlap]; exact inf_le_right))))

theorem overlapEquiv_val (E : A ≃* R)
    (hB : borelEmbedding.range.map E.toMonoidHom = (B).subgroupOf R) (x : BorelModel) :
    (overlapEquiv E hB x : M) = (E (borelEmbedding x) : M) := by rfl

/-- The same restriction satisfies the literal plane commuting square. -/
theorem plane_compatible (E : A ≃* R)
    (hB : borelEmbedding.range.map E.toMonoidHom = (B).subgroupOf R) (x : BorelModel) :
    (amalgam 1 hn).right (overlapEquiv E hB x) = E (borelEmbedding x) :=
  Subtype.ext (overlapEquiv_val E hB x)

/-- The actual point inclusion, pulled back by the same marked plane map. -/
def pointEmbedding (E : A ≃* R)
    (hB : borelEmbedding.range.map E.toMonoidHom = (B).subgroupOf R) : BorelModel →* P :=
  (amalgam 1 hn).left.comp (overlapEquiv E hB).toMonoidHom

theorem pointEmbedding_injective (E : A ≃* R)
    (hB : borelEmbedding.range.map E.toMonoidHom = (B).subgroupOf R) :
    Function.Injective (pointEmbedding E hB) :=
  (left_injective 1 hn).comp (overlapEquiv E hB).injective

theorem pointEmbedding_val (E : A ≃* R)
    (hB : borelEmbedding.range.map E.toMonoidHom = (B).subgroupOf R) (x : BorelModel) :
    (pointEmbedding E hB x : M) = (E (borelEmbedding x) : M) := by rfl

theorem pointEmbedding_range (E : A ≃* R)
    (hB : borelEmbedding.range.map E.toMonoidHom = (B).subgroupOf R) :
    (pointEmbedding E hB).range = (B).subgroupOf P := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact (overlapEquiv E hB x).property
  · intro hy
    obtain ⟨x,hx⟩ := (overlapEquiv E hB).surjective ⟨y,hy⟩
    refine ⟨x,Subtype.ext ?_⟩
    exact congrArg (fun t : B => (t:M)) hx

theorem pointEmbedding_root (E : A ≃* R)
    (hz : E (Z : A)=ModelClasses.longRight)
    (hB : borelEmbedding.range.map E.toMonoidHom = (B).subgroupOf R) :
    pointEmbedding E hB (Z : BorelModel)=longPoint := by
  apply Subtype.ext
  rw [pointEmbedding_val,borelEmbedding_inl,hz]
  rfl

/-- On the literal overlap, the affine height kernel is exactly the
preimage of the point residual. -/
theorem pointEmbedding_residual_preimage (E : A ≃* R)
    (hB : borelEmbedding.range.map E.toMonoidHom = (B).subgroupOf R) :
    (pResidual 2 P).comap (pointEmbedding E hB) = pResidual 2 BorelModel := by
  let : Finite BorelModel := Finite.of_injective (overlapEquiv E hB) (overlapEquiv E hB).injective
  let f := pointEmbedding E hB
  have hcard : Nat.card BorelModel=192 :=
    (Nat.card_congr (overlapEquiv E hB).toEquiv).trans BinaryCompletion.middle_card
  have hRcard : Nat.card (pResidual 2 BorelModel)=96 := by
    rw [residualModel_eq,card_residualModel]
  have hinc : pResidual 2 BorelModel ≤ (pResidual 2 P).comap f :=
    map_le_iff_le_comap.mp (map_pResidual_le 2 f)
  have hvR : involution∉pResidual 2 P := by
    intro hv
    have hh := involution_complement.disjoint.le_bot ⟨hv,mem_zpowers involution⟩
    exact involution_not_mem_core ((mem_bot.mp hh) ▸ (pCore 2 P).one_mem)
  have hvB : involution∈f.range := by
    rw [pointEmbedding_range,←pointModule_normalizer]
    exact pointModule.le_normalizer involution_mem_module
  have hproper : (pResidual 2 P).comap f ≠ ⊤ := by
    intro htop
    obtain ⟨x,hx⟩ := hvB
    have hxR : x∈(pResidual 2 P).comap f := by rw [htop]; trivial
    exact hvR (hx ▸ hxR)
  have hi := one_lt_index_of_ne_top hproper
  have hm := ((pResidual 2 P).comap f).card_mul_index
  rw [hcard] at hm
  have hupper : Nat.card ((pResidual 2 P).comap f)≤96 := by nlinarith
  exact (eq_of_le_of_card_ge hinc (by rw [hRcard]; exact hupper)).symm

/-- Under the marked plane identification, the literal point twist is
exactly the affine Borel twist, with equality on each element. -/
theorem point_twist_compatible (E : A ≃* R)
    (hz : E (Z : A)=ModelClasses.longRight)
    (hB : borelEmbedding.range.map E.toMonoidHom = (B).subgroupOf R) (x : BorelModel) :
    PointCentralTwist.centralTwist (pointEmbedding E hB x) =
      pointEmbedding E hB (Overlap.borelTwist x) := by
  have hmem : pointEmbedding E hB x∈pResidual 2 P ↔ x∈pResidual 2 BorelModel := by
    change x∈(pResidual 2 P).comap (pointEmbedding E hB) ↔ _
    rw [pointEmbedding_residual_preimage]
  by_cases hx : x∈pResidual 2 BorelModel
  · rw [PointCentralTwist.centralTwist_residual _ (hmem.mpr hx),
      Overlap.borelTwist_fixed_residual x hx]
  · rw [PointCentralTwist.centralTwist_outside _ (fun h => hx (hmem.mp h)),
      Overlap.borelTwist_outside_residual x hx,map_mul,pointEmbedding_root E hz hB]

/-- The affine twist extends across the literal point embedding. -/
theorem borelTwist_extends_point (E : A ≃* R)
    (hz : E (Z : A)=ModelClasses.longRight)
    (hB : borelEmbedding.range.map E.toMonoidHom = (B).subgroupOf R) :
    Theory.GroupTheory.RankTwoAmalgam.ExtendsAcross (pointEmbedding E hB) Overlap.borelTwist :=
  ⟨PointCentralTwist.centralTwist,point_twist_compatible E hz hB⟩

/-- The induced twist of the actual middle group extends across its
original inclusion in the point endpoint. -/
theorem induced_borelTwist_extends (E : A ≃* R)
    (hz : E (Z : A)=ModelClasses.longRight)
    (hB : borelEmbedding.range.map E.toMonoidHom = (B).subgroupOf R) :
    Theory.GroupTheory.RankTwoAmalgam.ExtendsAcross (amalgam 1 hn).left
      (MulAut.congr (overlapEquiv E hB) Overlap.borelTwist) := by
  refine ⟨PointCentralTwist.centralTwist,?_⟩
  intro b
  obtain ⟨x,rfl⟩ := (overlapEquiv E hB).surjective b
  change PointCentralTwist.centralTwist (pointEmbedding E hB x) =
    pointEmbedding E hB (Overlap.borelTwist ((overlapEquiv E hB).symm ((overlapEquiv E hB) x)))
  rw [MulEquiv.symm_apply_apply]
  exact point_twist_compatible E hz hB x

/-- A single marked affine-plane choice supplies the actual point extension
of the overlap twist, with all concrete model premises discharged. -/
theorem exists_marked_plane_equiv_with_twist :
    ∃ E : A ≃* R, E (Z : A)=ModelClasses.longRight ∧
      (SemidirectProduct.inl : V →* A).range.map E.toMonoidHom=pCore 2 R ∧
      ∃ hB : borelEmbedding.range.map E.toMonoidHom=(B).subgroupOf R,
        Theory.GroupTheory.RankTwoAmalgam.ExtendsAcross (amalgam 1 hn).left
          (MulAut.congr (overlapEquiv E hB) Overlap.borelTwist) := by
  obtain ⟨E,hz,hV,hC⟩ := AffinePlane.exists_marked_plane_equiv
  have hB : borelEmbedding.range.map E.toMonoidHom=(B).subgroupOf R := by
    rw [borelEmbedding_range]
    exact hC
  exact ⟨E,hz,hV,hB,induced_borelTwist_extends E hz hB⟩
end CFSG.Quasithin.ChapterF.UnitaryTwo.OverlapTwist
