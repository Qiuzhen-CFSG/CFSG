module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.OverlapCores
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.MovingCubicCore
public import Theory.GroupTheory.PrimeOrderLift

/-!
# The cubic decomposition of the actual HS core intersection

An overlap cubic fixes no nonidentity element of the Klein four image of
the normalizer core in S₄. Consequently its cyclic-four fixed core lies
in the involution-centralizer core. Together with the moved plane of V,
it gives the actual order-sixteen intersection by ambient multiplication.

This is local geometry derived from HS1--HS2 preceding Aschbacher--Smith
I.4.8, printed p.418.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims

private theorem cubic_fixed_four : ∀ x y : Equiv.Perm (Fin 4),
    x ^ 3 = 1 → x ≠ 1 → y ∈ Theory.SpecificGroups.SymmetricSix.DuadCalculation.core →
      x * y = y * x → y = 1 := by
  decide +kernel

variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The original cubic's cyclic-four fixed core lies in both local two-cores. -/
theorem TypeAt.cubic_fixed_core_le (h : TypeAt z V) (x : G)
    (hx : x ∈ involutionCentralizer z ⊓ normalizer (V : Set G))
    (hx3 : orderOf x = 3) :
    (normalizer (V : Set G)).pCoreIn 2 ⊓ centralizer ({x} : Set G) ≤
      (involutionCentralizer z).pCoreIn 2 := by
  let H := involutionCentralizer z
  let M := normalizer (V : Set G)
  let I := H ⊓ M
  let jH : I →* H := inclusion inf_le_left
  let jM : I →* M := inclusion inf_le_right
  let R := (pCore 2 M).comap jM
  let : R.Normal := inferInstanceAs ((pCore 2 M).comap jM).Normal
  have hRp : IsPGroup 2 R :=
    pCore_isPGroup.comap_of_injective jM (inclusion_injective inf_le_right)
  obtain ⟨f, hf, hk⟩ := h.exists_overlap_four_quotient
  have hkp : IsPGroup 2 f.ker := by
    rw [hk]
    exact pCore_isPGroup.comap_of_injective jH (inclusion_injective inf_le_left)
  let : (R.map f).Normal := (inferInstance : R.Normal).map f hf
  have hmap : R.map f ≤ pCore 2 (Equiv.Perm (Fin 4)) :=
    le_sSup ⟨inferInstance, hRp.map f⟩
  let xI : I := ⟨x, hx⟩
  have hxI : orderOf xI = 3 := (orderOf_coe xI).symm.trans hx3
  have hfx : orderOf (f xI) = 3 :=
    (f.orderOf_map_eq_of_coprime_of_isPGroup_ker hkp xI
      (by rw [hxI]; decide)).trans hxI
  intro y hy
  let yI : I := ⟨y, h.local_cores_le_intersection.2 hy.1⟩
  have hyR : yI ∈ R :=
    (mem_map_iff_mem M.subtype_injective (K := pCore 2 M) (x := jM yI)).mp hy.1
  have hyimage : f yI ∈ Theory.SpecificGroups.SymmetricSix.DuadCalculation.core := by
    rw [Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq]
    exact hmap ⟨yI, hyR, rfl⟩
  have hcomm : f xI * f yI = f yI * f xI := by
    rw [← map_mul, ← map_mul]
    apply congrArg f
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hy.2).symm
  have hyker : yI ∈ f.ker := cubic_fixed_four (f xI) (f yI)
    (orderOf_eq_prime_iff.mp hfx).1 (orderOf_eq_prime_iff.mp hfx).2 hyimage hcomm
  rw [hk] at hyker
  exact ⟨jH yI, hyker, rfl⟩

/-- Ambient multiplication decomposes the actual core intersection into the
cyclic-four fixed core and the moved plane of the original seed. -/
theorem TypeAt.cubic_overlap_product (h : TypeAt z V) (x : G)
    (hx : x ∈ involutionCentralizer z ⊓ normalizer (V : Set G))
    (hx3 : orderOf x = 3) :
    let Q := (involutionCentralizer z).pCoreIn 2
    let P := (normalizer (V : Set G)).pCoreIn 2
    let C := P ⊓ centralizer ({x} : Set G)
    let E := ⁅V, zpowers x⁆
    C ⊔ E = Q ⊓ P ∧ Disjoint C E ∧
      ∃ e : C × E ≃* (Q ⊓ P : Subgroup G),
        ∀ c a, (e (c, a) : G) = (c : G) * (a : G) := by
  let Q := (involutionCentralizer z).pCoreIn 2
  let P := (normalizer (V : Set G)).pCoreIn 2
  let C := P ⊓ centralizer ({x} : Set G)
  let E := ⁅V, zpowers x⁆
  let D := ⁅P, zpowers x⁆
  have hVQ : V ≤ Q := by
    change V ≤ (pCore 2 (involutionCentralizer z)).map (involutionCentralizer z).subtype
    rw [← h.centralizer_fitting]
    exact h.seed_le_core
  have hVP : V ≤ P := by
    change V ≤ (pCore 2 (normalizer (V : Set G))).map (normalizer (V : Set G)).subtype
    rw [← h.normalizer_fitting]
    exact h.seed_le_normalizer_core
  have hEV : E ≤ V :=
    le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hx.2)
  have hED : E ≤ D := commutator_mono hVP le_rfl
  have hCQ : C ≤ Q := h.cubic_fixed_core_le x hx hx3
  have hCP : C ≤ P := inf_le_left
  have hc : C ≤ centralizer (E : Set G) :=
    hCP.trans (h.seed_centralizer.ge.trans (centralizer_le hEV))
  have hd : Disjoint C E :=
    (h.cubic_core_product x hx hx3).2.2.1.symm.mono_right hED
  have hCc : Nat.card C = 4 := by
    obtain ⟨c, _, _, hc4, he⟩ := h.cubic_normalizer_core x hx hx3
    rw [show C = zpowers c from he, Nat.card_zpowers, hc4]
  have hEc : Nat.card E = 4 := (h.cubic_moving_omega x hx hx3).2
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting C E hd hc
  have hcard : Nat.card (C ⊔ E : Subgroup G) = 16 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, hCc, hEc]
  have hj : C ⊔ E = Q ⊓ P := eq_of_le_of_card_ge
    (sup_le (le_inf hCQ hCP) (le_inf (hEV.trans hVQ) (hEV.trans hVP)))
    (by rw [hcard, show Nat.card (Q ⊓ P : Subgroup G) = 16 from h.local_cores_structure.1])
  exact ⟨hj, hd, e.trans (MulEquiv.subgroupCongr hj), he⟩

end CFSG.Quasithin.HigmanSims
