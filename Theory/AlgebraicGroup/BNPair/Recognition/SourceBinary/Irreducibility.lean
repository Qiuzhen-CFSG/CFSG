module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.SplitCore
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.MarkedQuotient
public import Theory.AlgebraicGroup.BNPair.MaximalParabolic
public import Theory.GroupTheory.AmalgamLocalCores
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# Irreducibility of the marked characteristic-two quotient

For a finite split rank-two Tits system whose two marked parabolics have
self-centralizing two-cores, the marked simple reflections do not commute.
Thus the rank-two diagram is irreducible; no dihedral order is assumed.

First, a normal subgroup contained in a characteristic-two parabolic has
trivial two-core, since the ambient two-core vanishes. Self-centralization
then kills that subgroup. Both parabolics consequently have trivial normal
core. The standard-parabolic classification also makes them maximal, so
every nontrivial ambient normal subgroup supplements each parabolic.

If the two simple reflections commuted, the Weyl group would be the product
of their cyclic subgroups. Bruhat decomposition would give X = P₀P₁.
The embedded O₂(P₀) lies in the common Sylow U, hence in P₁. Normality in
P₀ and the product factorization then put O₂(P₀) in the normal core of P₁.
Its triviality contradicts self-centralization in the nontrivial P₀.

This is an elementary part of the minimal-configuration reduction left
implicit in DGS, Groups and Graphs, Part II, pp.80–81, for the split-quotient
invocation on p.224. It proves irreducibility, not the remaining minimality
or Fong–Seitz recognition. All maps and parabolics belong to the same
marked quotient; only that quotient is required to be finite.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary
variable {X : Type*} [Group X]

private theorem core_eq_bot_of_local_core (P : Subgroup X)
    (hX : pCore 2 X = ⊥)
    (hc : centralizer (pCore 2 P : Set P) ≤ pCore 2 P) :
    P.normalCore = ⊥ := by
  let K := P.normalCore
  let K' := K.subgroupOf P
  have hk : pCore 2 K = ⊥ := by
    rw [pCore_eq_comap_of_normal, hX, MonoidHom.comap_bot]
    exact P.normalCore.subtype.ker_eq_bot P.normalCore.subtype_injective
  have hk' : pCore 2 K' = ⊥ := by
    apply map_injective (f := (subgroupOfEquivOfLe P.normalCore_le).toMonoidHom)
      (subgroupOfEquivOfLe P.normalCore_le).injective
    rw [pCore_map_iso, hk, Subgroup.map_bot]
  have hzero : K' = ⊥ :=
    Theory.GroupTheory.AmalgamLocalCores.normal_eq_bot_of_core_eq_bot K' hc hk'
  have hm := congrArg (Subgroup.map P.subtype) hzero
  change (K.subgroupOf P).map P.subtype = (⊥ : Subgroup P).map P.subtype at hm
  rw [map_subgroupOf_eq_of_le (show K ≤ P from P.normalCore_le), Subgroup.map_bot] at hm
  exact hm

namespace MarkedQuotient
variable {P : Fin 2 → Subgroup X} (d : MarkedQuotient P)
/-- Each marked singleton parabolic is maximal proper. -/
theorem parabolic_isCoatom (i : Fin 2) :
    IsCoatom (d.tits.standardParabolic {d.simple i}) := by
  have hi : (1 - i : Fin 2) ≠ i := by fin_cases i <;> decide
  have he : d.tits.S \ {d.simple (1 - i)} = {d.simple i} := by
    rw [← d.simple_range]
    ext x
    simp only [Set.mem_sdiff, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨j, rfl⟩, hj⟩
      have hji : j = i := by
        have hn : j ≠ 1 - i := fun h => hj (congrArg d.simple h)
        fin_cases i <;> fin_cases j <;> simp_all
      exact congrArg d.simple hji
    · rintro rfl
      exact ⟨⟨i, rfl⟩, fun h => hi (d.simple_injective h).symm⟩
  simpa only [he] using d.tits.standardParabolic_isCoatom (d.simple_mem (1 - i))

/-- Local characteristic two eliminates the entire ambient normal core
of the parabolic, not only its two-core. -/
theorem parabolic_normalCore_eq_bot (split : SplitData d.tits) (i : Fin 2)
    (hc : centralizer (pCore 2 (d.tits.standardParabolic {d.simple i}) :
      Set (d.tits.standardParabolic {d.simple i})) ≤
      pCore 2 (d.tits.standardParabolic {d.simple i})) :
    (d.tits.standardParabolic {d.simple i}).normalCore = ⊥ :=
  core_eq_bot_of_local_core _ split.twoCore_eq_bot hc

/-- Every nontrivial ambient normal subgroup supplements either parabolic.
Equivalently it is transitive on that vertex type. -/
theorem normal_subgroup_sup_parabolic (split : SplitData d.tits) (i : Fin 2)
    (hc : centralizer (pCore 2 (d.tits.standardParabolic {d.simple i}) :
      Set (d.tits.standardParabolic {d.simple i})) ≤
      pCore 2 (d.tits.standardParabolic {d.simple i}))
    (V : Subgroup (X ⧸ d.D)) [V.Normal] (hne : V ≠ ⊥) :
    V ⊔ d.tits.standardParabolic {d.simple i} = ⊤ := by
  apply (d.parabolic_isCoatom i).lt_iff.mp
  apply lt_of_le_of_ne le_sup_right
  intro he
  have hv : V ≤ d.tits.standardParabolic {d.simple i} := he ▸ le_sup_left
  have hb := normal_le_normalCore.mpr hv
  rw [d.parabolic_normalCore_eq_bot split i hc] at hb
  exact hne (le_bot_iff.mp hb)

private theorem factor_of_commute (hcomm : Commute (d.simple 0) (d.simple 1))
    (x : X ⧸ d.D) :
    ∃ a ∈ d.tits.standardParabolic {d.simple 0},
      ∃ b ∈ d.tits.standardParabolic {d.simple 1}, a * b = x := by
  let W := d.tits.N ⧸ (d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N
  have hr : d.tits.S = {d.simple 0} ∪ {d.simple 1} := by
    rw [← d.simple_range]
    ext w
    simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hCS : ∀ a ∈ d.tits.S, ∀ b ∈ d.tits.S, a * b = b * a := by
    rw [hr]
    intro a ha b hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    all_goals simp only [Set.mem_singleton_iff] at ha hb
    all_goals subst a; subst b
    · rfl
    · exact hcomm.eq
    · exact hcomm.eq.symm
    · rfl
  have hc := isMulCommutative_closure hCS
  rw [d.tits.quotient_generate] at hc
  let := hc
  have hW : IsMulCommutative W := IsMulCommutative.of_comm fun a b =>
    congrArg Subtype.val (mul_comm' (⟨a, trivial⟩ : (⊤ : Subgroup W)) ⟨b, trivial⟩)
  let := hW
  let C₀ : Subgroup W := closure {d.simple 0}
  let C₁ : Subgroup W := closure {d.simple 1}
  let : C₁.Normal := ⟨fun a ha b => by
    rw [mul_comm' b a, mul_assoc, mul_inv_cancel, mul_one]
    exact ha⟩
  have hgen : C₀ ⊔ C₁ = ⊤ := by
    dsimp only [C₀, C₁]
    rw [← closure_union, ← hr, d.tits.quotient_generate]
  obtain ⟨w, hw⟩ := d.tits.exists_mem_doubleCoset x
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_normal_right.mp (hgen ▸ mem_top w)
  obtain ⟨y, hy, z, hz, rfl⟩ :=
    Set.mem_mul.mp (d.tits.bruhatCell_mul_subset_product a b hw)
  exact ⟨y, (d.tits.mem_standardParabolic_iff
    (Set.singleton_subset_iff.mpr (d.simple_mem 0)) y).mpr ⟨a, ha, hy⟩,
    z, (d.tits.mem_standardParabolic_iff
    (Set.singleton_subset_iff.mpr (d.simple_mem 1)) z).mpr ⟨b, hb, hz⟩, rfl⟩

/-- The two marked simple reflections do not commute: the rank-two
diagram is irreducible at the literal source markings. -/
theorem simple_not_commute (split : SplitData d.tits)
    (hc : ∀ i, centralizer (pCore 2 (d.tits.standardParabolic {d.simple i}) :
      Set (d.tits.standardParabolic {d.simple i})) ≤
      pCore 2 (d.tits.standardParabolic {d.simple i})) :
    ¬ Commute (d.simple 0) (d.simple 1) := by
  intro hcomm
  let P₀ := d.tits.standardParabolic {d.simple 0}
  let P₁ := d.tits.standardParabolic {d.simple 1}
  let V := (pCore 2 P₀).map P₀.subtype
  have hUP : split.U ≤ P₀ := split.U_le.trans (d.tits.B_le_standardParabolic _)
  have hVU : V ≤ split.U := by
    rintro v ⟨a, ha, rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal (split.sylow.subtype hUP) ha
  have hVP₁ : V ≤ P₁ := hVU.trans (split.U_le.trans (d.tits.B_le_standardParabolic _))
  have hN : P₀ ≤ normalizer (V : Set (X ⧸ d.D)) := by
    have hn := (pCore 2 P₀).le_normalizer_map P₀.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hn
  have hcore : V ≤ P₁.normalCore := by
    intro v hv g
    obtain ⟨a, ha, b, hb, he⟩ := d.factor_of_commute hcomm g⁻¹
    have hg : g = b⁻¹ * a⁻¹ := by rw [← mul_inv_rev, he, inv_inv]
    have hva : a⁻¹ * v * a ∈ V := by
      simpa only [inv_inv] using
        (mem_normalizer_iff.mp (hN (P₀.inv_mem ha)) v).mp hv
    have hh := P₁.mul_mem (P₁.mul_mem (P₁.inv_mem hb) (hVP₁ hva)) hb
    simpa only [hg, mul_inv_rev, inv_inv, mul_assoc] using hh
  have hV : V = ⊥ := by
    exact le_bot_iff.mp ((d.parabolic_normalCore_eq_bot split 1 (hc 1)) ▸ hcore)
  have hq : pCore 2 P₀ = ⊥ :=
    ((pCore 2 P₀).map_eq_bot_iff_of_injective P₀.subtype_injective).mp hV
  have htriv : (⊤ : Subgroup P₀) ≤ ⊥ := by
    have hh := hc 0
    change centralizer (pCore 2 P₀ : Set P₀) ≤ pCore 2 P₀ at hh
    rw [hq] at hh
    intro z _
    apply hh
    intro y hy
    rw [mem_bot.mp hy, one_mul, mul_one]
  obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective
    ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) (d.simple 0)
  have hnP : (n : X ⧸ d.D) ∈ P₀ :=
    (d.tits.mem_standardParabolic_iff
      (Set.singleton_subset_iff.mpr (d.simple_mem 0)) _).mpr
      ⟨d.simple 0, subset_closure (Set.mem_singleton _),
        d.tits.representative_mem_bruhatCell _ n hn⟩
  have hn1X : (n : X ⧸ d.D) = 1 :=
    congrArg (fun z : P₀ => (z : X ⧸ d.D))
      (mem_bot.mp (htriv (mem_top (⟨n, hnP⟩ : P₀))))
  have hn1 : n = 1 := Subtype.ext hn1X
  exact (d.tits.involutions _ (d.simple_mem 0)).1 (by rw [← hn, hn1, map_one])
end MarkedQuotient
end Theory.AlgebraicGroup.TitsSystem.SourceBinary
