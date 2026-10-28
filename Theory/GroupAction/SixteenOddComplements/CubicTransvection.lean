module
public import Theory.GroupTheory.CyclicThreeNormalizer
public import Theory.GroupAction.NormalizingFixedPoints
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupAction.AutomorphismFixedSubgroup
/-!
# A transvection excludes a fixed-free normal cubic

On an elementary binary group of order16, a cubic subgroup normalized by an
automorphism with eight fixed points has a nontrivial fixed subgroup. If the
automorphism centralizes a cubic generator, orbit counting on its fixed
hyperplane gives a contradiction modulo3. If it inverts the generator, the
hyperplane and its cubic image intersect trivially and would have product
order64. This distinguishes the direct-sum action in Aschbacher--Smith F.5.7.
-/
open Subgroup
open scoped IsMulCommutative
namespace SixteenOddComplements
private theorem mem_fixed_zpowers_iff {E : Type*} [Group E]
    (a : MulAut E) (x : E) :
    x ∈ FixedPoints.subgroup (zpowers a) E ↔ a x = x := by
  constructor
  · intro hx
    exact hx ⟨a, mem_zpowers a⟩
  · intro hx c
    obtain ⟨n, hn⟩ := c.property
    change (c : MulAut E) x = x
    rw [← hn]
    exact MulAction.mem_fixedBy_zpow (show x ∈ MulAction.fixedBy E a from hx) n

public theorem cubic_fixed_ne_bot_of_transvection_normalizer
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 16) (K : Subgroup (MulAut E)) (hK : Nat.card K = 3)
    (t : MulAut E) (ht : Nat.card t.fixedSubgroup = 8)
    (hn : t ∈ normalizer (K : Set (MulAut E))) :
    FixedPoints.subgroup K E ≠ ⊥ := by
  intro hbot
  obtain ⟨aa, haane⟩ := (ne_bot_iff_exists_ne_one (H := K)).mp
    (fun hh => by rw [hh, card_bot] at hK; omega)
  let a : MulAut E := aa
  have ha : a ∈ K := aa.property
  have haneG : a ≠ 1 := fun hh => haane (Subtype.ext hh)
  obtain ⟨hgen, ha3⟩ := cyclicThree_generator K hK a ha haneG
  have hfree (x : E) (hx : a x = x) : x = 1 := by
    exact hbot.le (hgen ▸ (mem_fixed_zpowers_iff a x).mpr hx)
  rcases cyclicThree_normalizer_conjugates K hK a ha haneG t hn with hc | hi
  · have hcomm : t*a = a*t := mul_inv_eq_iff_eq_mul.mp hc
    let F := t.fixedSubgroup
    have hstable (k : K) (x : E) (hx : x∈F) : k • x ∈ F := by
      have hk : (k : MulAut E) ∈ zpowers a := by rw [hgen];exact k.property
      obtain ⟨n, hn⟩ := hk
      apply (MulAut.mem_fixedSubgroup t _).mpr
      change t ((k : MulAut E) x) = (k : MulAut E) x
      rw [← hn]
      have hca : Commute t a := hcomm
      have hh := congrArg (fun f : MulAut E => f x) (hca.zpow_right n).eq
      change t ((a ^ n) x) = (a ^ n) (t x) at hh
      exact hh.trans (congrArg (a ^ n) ((MulAut.mem_fixedSubgroup t x).mp hx))
    let : IsInvariant K E F := ⟨fun k x => ⟨hstable k x, fun hx => by
      have hh := hstable k⁻¹ (k • x) hx
      simpa only [inv_smul_smul] using hh⟩⟩
    have hf : FixedPoints.subgroup K F = ⊥ := by
      apply bot_unique
      intro x hx
      apply Subtype.ext
      exact hfree x (congrArg Subtype.val (hx ⟨a,ha⟩))
    have hm := (IsPGroup.of_card (n:=1) (by simpa using hK)).card_modEq_card_fixedPoints F
    change Nat.ModEq 3 (Nat.card F) (Nat.card (FixedPoints.subgroup K F)) at hm
    rw [ht,hf,card_bot] at hm
    norm_num [Nat.ModEq] at hm
  · let F := t.fixedSubgroup
    have hd : Disjoint F (F.map a.toMonoidHom) := by
      apply disjoint_iff.mpr
      apply bot_unique
      intro x hx
      obtain ⟨u,hu,rfl⟩ := hx.2
      have htu : t u = u := (MulAut.mem_fixedSubgroup t u).mp hu
      have htau : t (a u) = a u := (MulAut.mem_fixedSubgroup t _).mp hx.1
      have hta : t*a = a⁻¹*t := mul_inv_eq_iff_eq_mul.mp hi
      have hinv : a⁻¹ u = a u := by
        have hh := congrArg (fun f : MulAut E => f u) hta
        change t (a u) = a⁻¹ (t u) at hh
        rw [htu,htau] at hh
        exact hh.symm
      have ha2 : a (a u) = u := by
        have hh := congrArg a hinv
        simpa using hh.symm
      have ha3u : a (a (a u)) = u :=
        congrArg (fun f : MulAut E => f u) ha3
      have hau : a u = u := by rwa [ha2] at ha3u
      have huone := hfree u hau
      exact mem_bot.mpr (by simp [huone])
    have hc := card_sup_eq_mul_of_normalizes_of_disjoint F (F.map a.toMonoidHom)
      (by rw [normalizer_eq_top];exact le_top) hd
    rw [card_map_of_injective a.injective,ht] at hc
    have hbound := card_le_card_group (F ⊔ F.map a.toMonoidHom)
    rw [hc,hE] at hbound
    omega
end SixteenOddComplements
