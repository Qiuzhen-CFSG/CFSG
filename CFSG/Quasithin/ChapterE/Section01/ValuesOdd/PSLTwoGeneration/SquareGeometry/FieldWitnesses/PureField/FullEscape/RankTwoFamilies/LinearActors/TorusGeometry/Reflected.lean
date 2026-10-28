module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.Geometry
public import GorensteinWalter.ReflectedCyclicCharacteristic
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Characteristic odd subgroups of reflected involution centralizers

In a normal embedded layer, the ambient centralizer of an actor normalizes
its involution centralizers. The cyclic rotation subgroup of a reflected
centralizer is characteristic, and so is its odd prime core. A reflector
in the four-group actor inverts this core. An element of prime order has a
square of the same order, so a prime absent from the relative centralizer
forces the actor commutator to escape the prescribed overgroup.

The result retains the entire ambient centralizer, including semilinear
actors. The prime and reflected-torus hypotheses are supplied by the
PSL₂ and PGL₂ model branches in this directory.

Source: Aschbacher–Smith E.1.2 and E.1.14(6), pp.209–210, 214;
Aschbacher (1982), Lemma 4.10; the reflected torus characteristicity is
proved in `GorensteinWalter.ReflectedCyclicCharacteristic`.
-/

public section
open Subgroup GorensteinWalter
open scoped commutatorElement

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.TorusGeometry

variable {K G : Type*} [Group K] [Finite K] [Group G]

omit [Finite K] in
/-- Centralizing an element normalizes its centralizer inside a normal layer. -/
theorem centralizer_normalizes_image (f : K →* G) (hf : Function.Injective f)
    [f.range.Normal] (z : K) :
    centralizer ({f z} : Set G) ≤ normalizer ((centralizer ({z} : Set K)).map f : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb⟩ := (inferInstance : f.range.Normal).conj_mem (f a) ⟨a, rfl⟩ g
  refine mem_map.mpr ⟨b, ?_, hb⟩
  apply mem_centralizer_singleton_iff.mpr
  apply hf
  rw [map_mul, map_mul, hb]
  have hg := mem_centralizer_singleton_iff.mp hg
  have ha := congrArg f (mem_centralizer_singleton_iff.mp ha)
  simp only [map_mul] at ha
  calc
    g * f a * g⁻¹ * f z = g * f a * f z * g⁻¹ := by
      have hh : g⁻¹ * f z = f z * g⁻¹ := (Commute.symm hg).inv_right.symm
      rw [mul_assoc, hh]; group
    _ = f z * (g * f a * g⁻¹) := by rw [mul_assoc g (f a) (f z), ha]; rw [← mul_assoc g (f z) (f a), hg]; group

/-- A missing odd torus prime gives an escaping commutator normalized by the
full ambient centralizer of the original mapped actor. -/
theorem reflected_prime_escape (f : K →* G) (hf : Function.Injective f)
    [f.range.Normal] (A U : Subgroup K) (hA : IsKleinFour A) (hU : IsCyclic U)
    (z w : K) (hzA : z ∈ A) (hwU : w ∉ U) (hw2 : w * w = 1)
    (hinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹)
    (hC : centralizer ({z} : Set K) = U ⊔ zpowers w)
    {r : ℕ} (hr : r.Prime) (hro : Odd r) (hrU : r ∣ Nat.card U)
    (M : Subgroup G)
    (hrM : ¬ r ∣ Nat.card ((centralizer ({z} : Set K)).subgroupOf (M.comap f))) :
    ∃ X : Subgroup G, IsPGroup r X ∧
      centralizer (A.map f : Set G) ≤ normalizer (X : Set G) ∧
      ¬ ⁅X, A.map f⁆ ≤ M := by
  classical
  let : Fact r.Prime := ⟨hr⟩
  let : IsKleinFour A := hA
  let : IsCyclic U := hU
  have hr3 : 3 ≤ r := by have := hr.two_le; have := hro.not_two_dvd_nat; omega
  have hU3 : 3 ≤ Nat.card U := hr3.trans (Nat.le_of_dvd Nat.card_pos hrU)
  let C := centralizer ({z} : Set K)
  have hUC : U ≤ C := by change U ≤ centralizer ({z} : Set K); rw [hC]; exact le_sup_left
  have hchar (D : Subgroup K) (he : D = U ⊔ zpowers w) :
      (U.subgroupOf D).Characteristic := by
    subst D
    exact reflectedCyclic_characteristic_in_join U w hU hU3 hwU hw2 hinv
  let : (U.subgroupOf C).Characteristic := hchar C hC
  let X₀ := (pCore r U).map U.subtype
  let X := X₀.map f
  have hnU : normalizer (C.map f : Set G) ≤ normalizer (U.map f : Set G) := by
    have hh := normalizer_le_normalizer_characteristic_map f hf C (U.subgroupOf C)
    rwa [map_subgroupOf_eq_of_le hUC] at hh
  have hnX : normalizer (U.map f : Set G) ≤ normalizer (X : Set G) :=
    normalizer_le_normalizer_characteristic_map f hf U (pCore r U)
  have hn : centralizer (A.map f : Set G) ≤ normalizer (X : Set G) := by
    apply le_trans ?_ ((centralizer_normalizes_image f hf z).trans (hnU.trans hnX))
    intro g hg
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hg (f z) (mem_map_of_mem f hzA)).symm
  refine ⟨X, (pCore_isPGroup (p := r) (G := U)).map U.subtype |>.map f, hn, ?_⟩
  have hAU : ¬ A ≤ U := fun h => hA.not_isCyclic (Subgroup.isCyclic_of_le h)
  obtain ⟨t, htA, htU⟩ := SetLike.not_le_iff_exists.mp hAU
  have htC : t ∈ C := mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (IsKleinFour.isMulCommutative.is_comm.comm
      (⟨t, htA⟩ : A) ⟨z, hzA⟩))
  obtain ⟨v, hv, htv | htv⟩ :=
    (mem_sup_zpowers_of_involution_inverts hwU hw2 hinv).mp (show t ∈ U ⊔ zpowers w by rw [← hC]; exact htC)
  · exact (htU (htv ▸ hv)).elim
  have htinv (x : K) (hx : x ∈ U) : t * x * t⁻¹ = x⁻¹ := by
    have hvx : v * x⁻¹ = x⁻¹ * v := congrArg Subtype.val
      (IsCyclic.isMulCommutative.is_comm.comm (⟨v, hv⟩ : U) (⟨x, hx⟩ : U)⁻¹)
    calc
      t * x * t⁻¹ = v * (w * x * w⁻¹) * v⁻¹ := by rw [htv]; group
      _ = v * x⁻¹ * v⁻¹ := by rw [hinv x hx]
      _ = x⁻¹ := by rw [hvx]; group
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := U) r hrU
  have huP : u ∈ pCore r U := by
    have hp : IsPGroup r (zpowers u) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
    exact (le_sSup (show zpowers u ∈ normalPSubgroups r U from ⟨inferInstance, hp⟩)) (mem_zpowers u)
  have huX : f (u : K) ∈ X := mem_map_of_mem f (mem_map_of_mem U.subtype huP)
  have he : ⁅f (u : K), f t⁆ = f ((u : K) ^ 2) := by
    rw [← map_commutatorElement]
    congr 1
    rw [commutatorElement_def]
    have hh := htinv (u : K)⁻¹ (U.inv_mem u.property)
    calc
      (u : K) * t * (u : K)⁻¹ * t⁻¹ = (u : K) * (t * (u : K)⁻¹ * t⁻¹) := by group
      _ = (u : K) ^ 2 := by rw [hh, inv_inv, pow_two]
  intro hXM
  have hum : (u : K) ^ 2 ∈ M.comap f := by
    change f ((u : K) ^ 2) ∈ M
    rw [← he]
    exact hXM (commutator_mem_commutator huX (mem_map_of_mem f htA))
  let b : C.subgroupOf (M.comap f) := ⟨⟨(u : K) ^ 2, hum⟩, hUC (U.pow_mem u.property 2)⟩
  have hb : orderOf b = r := by
    have hbK : orderOf b = orderOf ((u : K) ^ 2) :=
      (orderOf_injective ((M.comap f).subtype.comp (C.subgroupOf (M.comap f)).subtype)
        ((M.comap f).subtype_injective.comp (C.subgroupOf (M.comap f)).subtype_injective) b).symm
    rw [hbK]
    have huK : orderOf (u : K) = r := by simpa using hu
    rw [(show (orderOf (u : K)).Coprime 2 by rw [huK]; exact hro.coprime_two_right).orderOf_pow, huK]
  exact hrM (hb ▸ orderOf_dvd_natCard b)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.TorusGeometry
