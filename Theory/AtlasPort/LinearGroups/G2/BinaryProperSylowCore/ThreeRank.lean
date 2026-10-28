module

public import Theory.AtlasPort.LinearGroups.G2.BinaryProperSylowCore
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.ThreeObstruction
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedSylowCenter
public import Theory.AtlasPort.LinearGroups.G2.LieBinaryCompatibility
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.HexagonFixedPoint
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.PrimeRankCyclicSylow

/-!
# Three-rank of proper Sylow overgroups in the binary derived G₂ group

A proper Sylow-two overgroup has nontrivial two-core. The octonion hexagon
fixed-point theorem puts its normalizer in a conjugate of a standard
parabolic, whose order is not divisible by nine. Hence its Sylow-three
subgroups are cyclic. The rank bound lifts through the literal two-core
quotient map and supplies the G₂ branch of source 15.3.21.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.21,
printed p.1127; the hexagon argument is the same as in the source proof
of Proposition 1.3.4, printed p.511.
-/

@[expose] public section
namespace Atlas.G2.BinaryProperSylowCore
open Subgroup BinaryParabolicPair LieParabolicSetup EvenLocal.NormalizerCover

/-- A subgroup with nontrivial two-core lies in a conjugate of a binary
parabolic, and therefore its order is not divisible by nine. -/
theorem nine_not_dvd_of_twoCore_ne_bot
    (H : Subgroup DerivedModel) (hcore : pCore 2 H ≠ ⊥) : ¬ 9 ∣ Nat.card H := by
  let f : H →* Model (ZMod 2) := DerivedModel.subtype.comp H.subtype
  have hf : Function.Injective f := DerivedModel.subtype_injective.comp H.subtype_injective
  let Q : Subgroup (Model (ZMod 2)) := (pCore 2 H).map f
  have hQ : Q ≠ ⊥ := fun h => hcore
    (((pCore 2 H).map_eq_bot_iff_of_injective hf).mp h)
  have hpQ : IsPGroup 2 Q := pCore_isPGroup.map f
  obtain ⟨v, hv⟩ := normalizer_fixed_vertex_of_fixed_edge
    OctonionHexagon.hexagonData Q hQ hpQ (exists_fixed_edge Q hpQ)
  have hnorm (h : H) : f h ∈ normalizer (Q : Set (Model (ZMod 2))) := by
    apply (pCore 2 H).le_normalizer_map f
    apply mem_map.mpr
    exact ⟨h, by rw [normalizer_eq_top]; trivial, rfl⟩
  obtain ⟨g, hg⟩ := normalizer_conjugate_le_of_fixed_vertex Q v hv
  let j := (MulAut.conj g).toMonoidHom.comp f
  have hj : Function.Injective j := (MulAut.conj g).injective.comp hf
  have hcard : Nat.card j.range = Nat.card H :=
    (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm
  intro h9
  rcases hg with hfirst | hsecond
  · apply ThreeObstruction.first_nine_not_dvd
    have hle : j.range ≤ firstParabolic := by
      rw [← parabolic₁_binary]
      rintro _ ⟨h, rfl⟩
      exact hfirst (mem_map.mpr ⟨f h, hnorm h, rfl⟩)
    exact h9.trans (hcard ▸ card_dvd_of_le hle)
  · apply ThreeObstruction.second_nine_not_dvd
    have hle : j.range ≤ BinaryCore.secondParabolic := by
      rintro _ ⟨h, rfl⟩
      exact hsecond (mem_map.mpr ⟨f h, hnorm h, rfl⟩)
    exact h9.trans (hcard ▸ card_dvd_of_le hle)

/-- Every proper Sylow-two overgroup of G₂(2)′ has three-rank at most one. -/
theorem proper_sylow_overgroup_three_rank_le_one
    (P : Sylow 2 DerivedModel) (H : Subgroup DerivedModel)
    (hPH : (P : Subgroup DerivedModel) ≤ H) (hH : H ≠ ⊤) :
    primeRank 3 H ≤ 1 := by
  have h9 := nine_not_dvd_of_twoCore_ne_bot H (twoCore_ne_bot P H hH hPH)
  let Q : Sylow 3 H := default
  apply Q.primeRank_le_one_of_isCyclic
  obtain ⟨n, hn⟩ := Q.isPGroup'.exists_card_eq
  have hd : 3 ^ n ∣ Nat.card H := hn ▸ (Q : Subgroup H).card_subgroup_dvd_card
  have hsmall : n ≤ 1 := by
    by_contra! h
    exact h9 ((pow_dvd_pow 3 (by omega : 2 ≤ n)).trans hd)
  apply isCyclic_of_card_dvd_prime (p := 3)
  rw [hn]
  simpa using pow_dvd_pow 3 hsmall

/-- The same obstruction in an arbitrary finite extension of G₂(2)′ by its two-core. -/
theorem twoCoreQuotient_sylow_overgroup_three_rank_le_one
    {H : Type*} [Group H] [Finite H]
    (e : (H ⧸ pCore 2 H) ≃* DerivedModel)
    (P : Sylow 2 H) (M : Subgroup H)
    (hPM : (P : Subgroup H) ≤ M) (hM : M ≠ ⊤) :
    primeRank 3 M ≤ 1 := by
  let f : H →* DerivedModel := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hkerM : f.ker ≤ M := by
    rw [hker]
    exact (pCore_isPGroup.le_sylow_of_normal P).trans hPM
  have hproper : M.map f ≠ ⊤ := by
    intro hh
    have he := comap_map_eq_self hkerM
    rw [hh, comap_top] at he
    exact hM he.symm
  have hr : primeRank 3 (M.map f) ≤ 1 :=
    proper_sylow_overgroup_three_rank_le_one (P.mapSurjective hf) (M.map f)
      (map_mono hPM) hproper
  let g : M →* M.map f := f.subgroupMap M
  have hg : IsPGroup 2 g.ker := by
    have he : g.ker = f.ker.comap M.subtype := by
      ext x
      change (⟨f x, _⟩ : M.map f) = 1 ↔ f x = 1
      exact Subtype.ext_iff
    rw [he, hker]
    exact pCore_isPGroup.comap_of_injective M.subtype M.subtype_injective
  obtain ⟨n, hn⟩ := hg.exists_card_eq
  exact (primeRank_le_of_coprime_ker 3 g (by rw [hn]; exact (by decide : Nat.Coprime 3 2).pow_right n)).trans hr


end Atlas.G2.BinaryProperSylowCore
