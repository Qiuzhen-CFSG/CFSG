module

public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PGroup.BinaryPowerSeries
public import Theory.GroupTheory.PCoreImage
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# An abelian-square obstruction to elementary core commutators

Let R be a normal abelian two-subgroup of a finite group K whose square
subgroup has a two-group centralizer. A subnormal two-perfect subgroup B
with elementary core commutator must be trivial: subnormal core action puts
[R,B] in [O₂(B),B], so its elements have square one. Abelianity of R then
makes B centralize R², and two-perfection kills that two-group image.

The argument works coordinate by coordinate in a finite direct power of K.
It also survives a two-group kernel and a normal section with two-group
upper quotient. Both kernels are retained; neither extension is assumed
to split. `NormalPowerCover` records the actual surjective map to the full
local factors, not just their quotients by their two-cores.

Source application: Aschbacher–Smith, 2.3.9(7), printed p.526, using the
(4 × 4).D₁₂ local subgroup of M₁₂ in GLS3, Table 5.3b. The concrete radical
and local-overgroup construction are separate from this group-theoretic
obstruction.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- An actual normal abelian two-subgroup detected by its squares. -/
structure AbelianSquareControl (K : Type*) [Group K] where
  radical : Subgroup K
  normal : radical.Normal
  abelian : IsMulCommutative radical
  two_group : IsPGroup 2 radical
  centralizer_two_group : IsPGroup 2 (centralizer (radical.squareClosure : Set K))

/-- The same square control implies characteristic two for the local group. -/
theorem AbelianSquareControl.selfCentralizingCore {K : Type*} [Group K]
    (d : AbelianSquareControl K) :
    centralizer (pCore 2 K : Set K) ≤ pCore 2 K := by
  have hR : d.radical ≤ pCore 2 K := le_sSup ⟨d.normal, d.two_group⟩
  have hc : IsPGroup 2 (centralizer (pCore 2 K : Set K)) :=
    d.centralizer_two_group.to_le (centralizer_le (d.radical.squareClosure_le.trans hR))
  exact le_sSup ⟨inferInstance, hc⟩

/-- Exponent two in the intrinsic core commutator forces centralization of R². -/
theorem centralizes_squares_of_subnormal_twoPerfect
    (R B : Subgroup G) [R.Normal] [IsMulCommutative R]
    (hR : IsPGroup 2 R) (hB : B.IsSubnormal) (hp : IsPPerfect 2 B)
    (hu : ∀ u ∈ (⁅pCore 2 B, (⊤ : Subgroup B)⁆).map B.subtype, u ^ 2 = 1) :
    B ≤ centralizer (R.squareClosure : Set G) := by
  have hcomm := commutator_le_core_commutator_of_isSubnormal B R hB hp hR
    (by rw [normalizer_eq_top]; exact le_top)
  intro b hb
  rw [squareClosure, centralizer_closure]
  rintro _ ⟨r, rfl⟩
  have hbr : b * (r : G) * b⁻¹ ∈ R := (inferInstance : R.Normal).conj_mem r r.property b
  have hc : Commute (b * (r : G) * b⁻¹) (r : G)⁻¹ :=
    setLike_mul_comm hbr (R.inv_mem r.property)
  have hs : (b * (r : G) * b⁻¹ * (r : G)⁻¹) ^ 2 = 1 := by
    apply hu
    apply hcomm
    rw [commutator_comm]
    exact commutator_mem_commutator hb r.property
  rw [hc.mul_pow, inv_pow, mul_inv_eq_one] at hs
  rw [conj_pow] at hs
  exact (mul_inv_eq_iff_eq_mul.mp hs).symm

variable {K I : Type*} [Group K] [Finite K] [Finite I]

/-- The square obstruction applies independently in each coordinate. -/
theorem eq_bot_of_square_control_power (d : AbelianSquareControl K)
    (B : Subgroup (I → K)) (hB : B.IsSubnormal) (hp : IsPPerfect 2 B)
    (hu : ∀ u ∈ (⁅pCore 2 B, (⊤ : Subgroup B)⁆).map B.subtype, u ^ 2 = 1) :
    B = ⊥ := by
  classical
  let R := d.radical
  let : R.Normal := d.normal
  let : IsMulCommutative R := d.abelian
  have hcoord (i : I) (b : B) : (b : I → K) i ∈ centralizer (R.squareClosure : Set K) := by
    let f := MonoidHom.mulSingle (fun _ : I => K) i
    let Q := R.map f
    let : Q.Normal := ⟨by
      rintro x ⟨r, hr, rfl⟩ g
      refine ⟨g i * r * (g i)⁻¹, (inferInstance : R.Normal).conj_mem r hr (g i), ?_⟩
      ext j
      by_cases hj : j = i
      · subst j
        simp [f]
      · simp [f, Pi.mulSingle_eq_of_ne hj]⟩
    let : IsMulCommutative Q := R.map_isMulCommutative f
    have h := centralizes_squares_of_subnormal_twoPerfect Q B (d.two_group.map f) hB hp hu b.property
    rw [squareClosure, centralizer_closure]
    rintro _ ⟨r, rfl⟩
    have he := h ((f r) ^ 2) (square_mem_squareClosure (mem_map_of_mem f r.property))
    simpa [f] using congrFun he i
  apply eq_bot_iff.mpr
  intro b hb
  apply mem_bot.mpr
  funext i
  let f : B →* centralizer (R.squareClosure : Set K) :=
    ((Pi.evalMonoidHom (fun _ : I => K) i).comp B.subtype).codRestrict _ (hcoord i)
  exact congrArg Subtype.val
    (DFunLike.congr_fun (hp.hom_eq_one_of_isPGroup d.centralizer_two_group f) ⟨b, hb⟩)

/-- The full core commutator maps onto the target core commutator through a two-kernel. -/
theorem eq_bot_of_square_control_cover (d : AbelianSquareControl K)
    (f : G →* (I → K)) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (B : Subgroup G) (hB : B.IsSubnormal) (hp : IsPPerfect 2 B)
    (hu : ∀ u ∈ (⁅pCore 2 B, (⊤ : Subgroup B)⁆).map B.subtype, u ^ 2 = 1) :
    B = ⊥ := by
  have hm : ((⁅pCore 2 B, (⊤ : Subgroup B)⁆).map B.subtype).map f =
      (⁅pCore 2 (B.map f), (⊤ : Subgroup (B.map f))⁆).map (B.map f).subtype := by
    simp only [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    change ⁅(B.pCoreIn 2).map f, B.map f⁆ = ⁅(B.map f).pCoreIn 2, B.map f⁆
    rw [map_pCoreIn_of_ker_isPGroup f hk B]
  have hu' : ∀ u ∈ (⁅pCore 2 (B.map f), (⊤ : Subgroup (B.map f))⁆).map
      (B.map f).subtype, u ^ 2 = 1 := by
    rw [← hm]
    rintro _ ⟨u, humem, rfl⟩
    rw [← map_pow, hu u humem, map_one]
  have hz := eq_bot_of_square_control_power d (B.map f) (hB.map hf)
    (hp.of_surjective (f.subgroupMap B) (f.subgroupMap_surjective B)) hu'
  have hle : B ≤ f.ker := (B.map_eq_bot_iff).mp hz
  have hi := hp.hom_eq_one_of_isPGroup (hk.to_le hle) (MonoidHom.id B)
  apply eq_bot_iff.mpr
  intro b hb
  exact congrArg Subtype.val (DFunLike.congr_fun hi ⟨b, hb⟩)

/-- A normal section mapping onto full local factors, with p-group kernels below and above. -/
structure NormalPowerCover (p : ℕ) (E A : Type*) [Group E] [Group A] where
  base : Subgroup E
  normal : base.Normal
  quotient_isPGroup : @IsPGroup p (E ⧸ base) (@QuotientGroup.Quotient.group E _ base normal)
  copies : ℕ
  projection : base →* (Fin copies → A)
  surjective : Function.Surjective projection
  kernel_isPGroup : IsPGroup p projection.ker

/-- Two-perfection restricts to the normal base before applying the square obstruction. -/
theorem eq_bot_of_square_control_normal_cover (d : AbelianSquareControl K)
    (c : NormalPowerCover 2 G K) (B : Subgroup G) (hB : B.IsSubnormal)
    (hp : IsPPerfect 2 B)
    (hu : ∀ u ∈ (⁅pCore 2 B, (⊤ : Subgroup B)⁆).map B.subtype, u ^ 2 = 1) :
    B = ⊥ := by
  have hBN : B ≤ c.base := (le_pResidual_of_isPPerfect B hp).trans
    (sInf_le ⟨c.normal, c.quotient_isPGroup⟩)
  let D := B.subgroupOf c.base
  let e : D ≃* B := subgroupOfEquivOfLe hBN
  have hpD := hp.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hmap : (⁅pCore 2 D, (⊤ : Subgroup D)⁆).map e.toMonoidHom =
      ⁅pCore 2 B, (⊤ : Subgroup B)⁆ := by
    rw [map_commutator, pCore_map_iso 2 e, map_top_of_surjective _ e.surjective]
  have huD : ∀ u ∈ (⁅pCore 2 D, (⊤ : Subgroup D)⁆).map D.subtype, u ^ 2 = 1 := by
    rintro _ ⟨u, humem, rfl⟩
    apply Subtype.ext
    have he : e u ∈ ⁅pCore 2 B, (⊤ : Subgroup B)⁆ := hmap ▸ mem_map_of_mem e.toMonoidHom humem
    exact hu _ ⟨e u, he, rfl⟩
  have hD := eq_bot_of_square_control_cover d c.projection c.surjective c.kernel_isPGroup
    D hB.subgroupOf hpD huD
  have he := congrArg (Subgroup.map c.base.subtype) hD
  simpa only [D, map_subgroupOf_eq_of_le hBN, Subgroup.map_bot] using he
end Theory.GroupTheory

end
