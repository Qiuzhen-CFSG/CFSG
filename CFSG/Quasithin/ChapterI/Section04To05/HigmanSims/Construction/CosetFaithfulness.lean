module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.AmbientControl
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Normal-subgroup detection and faithful Mathieu coset actions in type HS

Every nontrivial ambient normal subgroup has even order, since the odd core
is trivial. Conjugating an involution into the common Sylow and then meeting
its center places the unique central involution z in that normal subgroup.
Full seed fusion puts V in it. Its centralizer is therefore a normal two-group
inside C_G(V), and the trivial ambient two-core makes it trivial.

If an M₂₂ subgroup were normal, conjugation would embed G in Aut(M₂₂).
The actual automorphism group has order 887040, which is not divisible by
512, the order of the ambient Sylow two-subgroup. Thus an M₂₂ subgroup is
not normal. Simplicity of the concrete Mathieu group kills its normal core,
proving faithfulness of its literal left-coset action.

This discharges the kernel premise in the type-HS degree-100 construction.
The existence, index and subdegrees of the M₂₂ subgroup are separate
obligations; none is asserted or assumed as part of TypeAt.
Source: HS1–HS2 and I.4.8, Aschbacher–Smith, printed p.418.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The marked involution is the unique central involution of an ambient Sylow inside its centralizer. -/
theorem TypeAt.ambient_center_unique (h : TypeAt z V) (S : Sylow 2 G)
    (hSH : (S : Subgroup G) ≤ involutionCentralizer z)
    (x : center S) (hx : orderOf x = 2) : (x.val : G) = z := by
  let P := S.subtype hSH
  let e : (P : Subgroup (involutionCentralizer z)) ≃* S := subgroupOfEquivOfLe hSH
  let y := (centerCongr e).symm x
  have hy : orderOf y = 2 := ((centerCongr e).symm.orderOf_eq x).trans hx
  exact h.local_center_involution_unique P y hy

/-- Every even ambient normal subgroup contains the marked involution. -/
theorem TypeAt.involution_mem_even_normal (h : TypeAt z V) (N : Subgroup G) [N.Normal]
    (hN : 2 ∣ Nat.card N) : z ∈ N := by
  obtain ⟨S, hS, _⟩ := h.exists_common_ambient_sylow
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 hN
  have hxG : orderOf (x : G) = 2^1 := by simpa using hx
  obtain ⟨y, hxy⟩ := S.exists_isConj_of_orderOf_eq_prime_pow hxG
  have hyN : (y : G) ∈ N := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hxy
    rw [← hg]
    exact (inferInstance : N.Normal).conj_mem x x.property g
  have hJ : N.subgroupOf (S : Subgroup G) ≠ ⊥ := by
    intro he
    have hyJ : y ∈ N.subgroupOf (S : Subgroup G) := hyN
    rw [he, mem_bot] at hyJ
    obtain ⟨g, hg⟩ := hxy
    have hh := hg.orderOf_eq (g : G)
    rw [hxG, hyJ] at hh
    norm_num at hh
  let : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
  obtain ⟨Z, _, hZN, hZcard, hZcenter⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2)
      (N.subgroupOf (S : Subgroup G)) ((nontrivial_iff_ne_bot _).mpr hJ)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (by rw [hZcard])
  let wZ : center S := ⟨w.val, hZcenter w.property⟩
  have he : (w.val : G) = z := TypeAt.ambient_center_unique h S (hS.trans inf_le_left) wZ
    (by simpa only [← orderOf_coe] using hw)
  exact he ▸ hZN w.property

/-- Every nontrivial ambient normal subgroup contains the original elementary seed. -/
theorem TypeAt.seed_le_nontrivial_normal (h : TypeAt z V) (N : Subgroup G) [N.Normal]
    (hn : N ≠ ⊥) : V ≤ N := by
  have hN : 2 ∣ Nat.card N := by
    by_contra hc
    exact hn ((pPrimeCore_eq_bot_iff.mp h.ambient_oddCore_eq_bot) N inferInstance
      (Nat.prime_two.coprime_iff_not_dvd.mpr hc))
  have hzN := TypeAt.involution_mem_even_normal h N hN
  have hz1 : (⟨z, h.involution_mem_seed⟩ : V) ≠ 1 := by
    intro he
    have hz : z = 1 := congrArg Subtype.val he
    have hh := h.involution
    simp [hz] at hh
  intro y hy
  by_cases hy1 : y = 1
  · exact hy1 ▸ N.one_mem
  obtain ⟨g, hg⟩ := h.seed_transitive ⟨z, h.involution_mem_seed⟩ ⟨y, hy⟩ hz1
    (fun he => hy1 (congrArg Subtype.val he))
  have hzy := congrArg Subtype.val hg
  change (g : G) * z * (g : G)⁻¹ = y at hzy
  exact hzy ▸ (inferInstance : N.Normal).conj_mem z hzN g

/-- Every nontrivial ambient normal subgroup has trivial ambient centralizer. -/
theorem TypeAt.normal_centralizer_eq_bot (h : TypeAt z V) (N : Subgroup G) [N.Normal]
    (hn : N ≠ ⊥) : centralizer (N : Set G) = ⊥ := by
  have hc : centralizer (N : Set G) ≤ (pCore 2 (normalizer (V : Set G))).map
      (normalizer (V : Set G)).subtype := by
    rw [← h.seed_centralizer]
    exact centralizer_le (TypeAt.seed_le_nontrivial_normal h N hn)
  have hp : IsPGroup 2 (centralizer (N : Set G)) :=
    ((pCore_isPGroup (p := 2) (G := normalizer (V : Set G))).map
      (normalizer (V : Set G)).subtype).of_injective (inclusion hc) (inclusion_injective hc)
  have hle : centralizer (N : Set G) ≤ pCore 2 G := le_sSup ⟨inferInstance, hp⟩
  exact bot_unique (h.ambient_twoCore_eq_bot ▸ hle)

/-- An actual M₂₂ subgroup cannot be ambient normal. -/
theorem TypeAt.m22_not_normal (h : TypeAt z V) (K : Subgroup G)
    (e : K ≃* Sporadic.Mathieu.M22) : ¬ K.Normal := by
  intro hK
  let := hK
  have hn : K ≠ ⊥ := by
    intro he
    have hc : Nat.card K = 443520 := (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m22_order
    rw [he, Nat.card_unique] at hc
    contradiction
  have hc := TypeAt.normal_centralizer_eq_bot h K hn
  have hi : Function.Injective K.normalizerMonoidHom := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [normalizerMonoidHom_ker, hc, bot_subgroupOf]
  let j : G →* normalizer (K : Set G) :=
    { toFun := fun g => ⟨g, le_normalizer_of_normal (mem_top g)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let f : G →* MulAut K := K.normalizerMonoidHom.comp j
  have hf : Function.Injective f := hi.comp (fun x y he => congrArg (fun t => (t.val : G)) he)
  let a : Sporadic.Mathieu.m22DesignAut ≃* MulAut Sporadic.Mathieu.M22 :=
    MulEquiv.ofBijective Sporadic.Mathieu.m22DesignAutToAut
      ⟨Sporadic.Mathieu.m22DesignAutToAut_injective, Sporadic.Mathieu.m22DesignAutToAut_surjective⟩
  have hcard : Nat.card (MulAut K) = 887040 :=
    (Nat.card_congr (MulAut.congr e).toEquiv).trans
      ((Nat.card_congr a.symm.toEquiv).trans Sporadic.Mathieu.m22DesignAut_order)
  obtain ⟨S, _, hs⟩ := h.exists_common_ambient_sylow
  have hd : 512 ∣ 887040 := by
    rw [← hs, ← hcard]
    exact (card_subgroup_dvd_card (S : Subgroup G)).trans (card_dvd_of_injective f hf)
  norm_num at hd

/-- Every actual M₂₂ subgroup has trivial ambient normal core. -/
theorem TypeAt.m22_core_free (h : TypeAt z V) (K : Subgroup G)
    (e : K ≃* Sporadic.Mathieu.M22) : K.normalCore = ⊥ := by
  let := Sporadic.Mathieu.m22_isSimpleGroup
  let : IsSimpleGroup K := e.isSimpleGroup
  let N := K.normalCore
  rcases (inferInstance : (N.subgroupOf K).Normal).eq_bot_or_eq_top with hn | hn
  · have hh := congrArg (Subgroup.map K.subtype) hn
    simpa only [subgroupOf_map_subtype, show N ⊓ K = N from inf_eq_left.mpr K.normalCore_le, Subgroup.map_bot] using hh
  · have hKN : K ≤ N := by
      intro x hx
      exact (show (⟨x, hx⟩ : K) ∈ N.subgroupOf K by rw [hn]; trivial)
    have he : K = N := le_antisymm hKN K.normalCore_le
    exact (TypeAt.m22_not_normal h K e (he.symm ▸ (inferInstance : N.Normal))).elim

/-- The literal left-coset action of every actual M₂₂ subgroup is faithful. -/
theorem TypeAt.m22_coset_faithful (h : TypeAt z V) (K : Subgroup G)
    (e : K ≃* Sporadic.Mathieu.M22) : Function.Injective (MulAction.toPermHom G (G ⧸ K)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [← normalCore_eq_ker, TypeAt.m22_core_free h K e]
end CFSG.Quasithin.HigmanSims
