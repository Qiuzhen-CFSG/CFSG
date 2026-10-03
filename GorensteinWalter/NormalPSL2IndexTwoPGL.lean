module
public import GorensteinWalter.NormalPSL2Semilinear
public import GorensteinWalter.PSL2OddCore
public import Mathlib.Algebra.Group.Shrink

/-!
# Prescribed PGL2 model of an index-two PSL2 extension

A finite group with dihedral Sylow two-subgroups and a specified normal
index-two PSL2(K) subgroup is isomorphic to PGL2(K). The equivalence extends
the supplied core identification through the canonical PSL2-to-PGL2 map.
Every odd finite field is retained, including orders three and nine.

The ambient odd core maps trivially to the index-two quotient and then
vanishes inside the PSL2 core. The prescribed semilinear embedding therefore
applies. Its coefficient image has odd order and order dividing two, so the
embedding lands in the linear layer. The canonical PSL2 range also has index
two in PGL2, giving equal source and target cardinalities and hence
surjectivity. The original core equation survives the restriction.
The public wrapper allows independent ambient and field universes by
transporting the finite ambient group through `Shrink` into the unchanged
field universe, using the actual comap equivalence on the specified core.

This is the projective model comparison used in Alperin--Brauer--Gorenstein,
Chapter II, Section 3, Proposition 3 (article page 25, PDF page 26, application of
reference [21], Lemma 9). Neither odd-core-freeness nor surjectivity of an
assumed projective action is an extra hypothesis.
-/

namespace GorensteinWalter
universe u v

private theorem ambient_odd_core {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hNi : N.index = 2)
    (K : Type u) [Field K] [Finite K] (eN : N ≃* PSL2 K)
    (hPSL : pPrimeCore 2 (PSL2 K) = ⊥) : pPrimeCore 2 G = ⊥ := by
  let O := pPrimeCore 2 G
  let q := QuotientGroup.mk' N
  have hD : O.map q = ⊥ := by
    apply Subgroup.card_eq_one.mp
    apply Nat.eq_one_of_dvd_coprimes (pPrimeCore_coprime_card (p := 2) (G := G))
    · have := (O.map q).card_subgroup_dvd_card
      rwa [← N.index_eq_card, hNi] at this
    · exact O.card_map_dvd q
  have hON : O ≤ N := by
    have := (Subgroup.map_eq_bot_iff O).mp hD
    simpa only [q, QuotientGroup.ker_mk'] using this
  have hNcore : pPrimeCore 2 N = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective (pPrimeCore 2 N)
      (f := eN.toMonoidHom) eN.injective).mp
    rw [pPrimeCore_map_iso, hPSL]
  have hcore := pPrimeCore_eq_bot_iff.mp hNcore (O.subgroupOf N)
    inferInstance (show Nat.Coprime 2 (Nat.card (O.subgroupOf N)) from by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hON).toEquiv]
      exact pPrimeCore_coprime_card)
  apply le_bot_iff.mp
  intro g hg
  have hg' : (⟨g, hON hg⟩ : N) ∈ O.subgroupOf N := hg
  rw [hcore] at hg'
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hg')

private theorem same_universe_extension
    {G : Type u} [Group G] [Finite G]
    (hGd : HasDihedralSylowTwo G)
    (N : Subgroup G) [N.Normal] (hNi : N.index = 2)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (eN : N ≃* PSL2 K) :
    ∃ e : G ≃* PGL2 K, ∀ n : N,
      e n = Matrix.ProjectiveSpecialLinearGroup.toPGL (eN n) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let : Finite (PGL2 K) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  have hO := ambient_odd_core N hNi K eN (psl2_pPrimeCore_two_eq_bot K hK)
  obtain ⟨f, hf, hfn, hodd⟩ :=
    exists_normal_psl2_semilinear_embedding hGd hO N K hK eN
  let c : G →* (K ≃+* K) := SemidirectProduct.rightHom.comp f
  have hcr : c.range = (pGammaL2FieldProjection K f.range).range := by
    ext σ
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨⟨f g, ⟨g, rfl⟩⟩, rfl⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨x, hx⟩ := g.property
      exact ⟨x, congrArg SemidirectProduct.right hx⟩
  have hNc : N ≤ c.ker := by
    intro n hn
    change (f n).right = 1
    rw [hfn ⟨n, hn⟩]
    rfl
  have hd : c.ker.index ∣ 2 := hNi ▸ Subgroup.index_dvd_of_le hNc
  have ho : Odd c.ker.index := by rw [Subgroup.index_ker, hcr]; exact hodd
  have hcindex : c.ker.index = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact h
    · rw [h] at ho
      norm_num at ho
  have hc : ∀ g, (f g).right = 1 := by
    intro g
    have hg : g ∈ c.ker := by rw [Subgroup.index_eq_one.mp hcindex]; trivial
    exact hg
  let fl : G →* pGammaL2PGLRange K := f.codRestrict _ (fun g => by
    refine ⟨(f g).left, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact (hc g).symm)
  let l : G →* PGL2 K := (pGammaL2PGLRangeEquiv K).symm.toMonoidHom.comp fl
  have hl : Function.Injective l :=
    (pGammaL2PGLRangeEquiv K).symm.injective.comp (fun a b h =>
      hf (congrArg Subtype.val h))
  have hcard : Nat.card G = Nat.card (PGL2 K) := by
    rw [← N.card_mul_index, hNi, Nat.card_congr eN.toEquiv]
    have hm := (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range.card_mul_index
    rw [pgl2_psl2Range_index_eq_two K hK,
      ← Nat.card_congr (psl2EquivToPGLRange K).toEquiv] at hm
    exact hm
  refine ⟨MulEquiv.ofBijective l
    ((Nat.bijective_iff_injective_and_card l).mpr ⟨hl, hcard⟩), ?_⟩
  intro n
  change l n = _
  apply (pGammaL2PGLRangeEquiv K).injective
  change (pGammaL2PGLRangeEquiv K)
    ((pGammaL2PGLRangeEquiv K).symm (fl n)) = _
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  exact hfn n

public theorem exists_mulEquiv_pgl2_of_normal_psl2_index_two
    {G : Type u} [Group G] [Finite G]
    (hGd : HasDihedralSylowTwo G)
    (N : Subgroup G) [N.Normal] (hNi : N.index = 2)
    (K : Type v) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (eN : N ≃* PSL2 K) :
    ∃ e : G ≃* PGL2 K, ∀ n : N,
      e n = Matrix.ProjectiveSpecialLinearGroup.toPGL (eN n) := by
  classical
  let eG : Shrink.{v} G ≃* G := Shrink.mulEquiv
  let : Finite (Shrink.{v} G) := Finite.of_injective eG eG.injective
  let M : Subgroup (Shrink.{v} G) := N.comap eG.toMonoidHom
  let eM : M ≃* N := MulEquiv.ofBijective (eG.toMonoidHom.subgroupComap N)
    ⟨fun _ _ h => Subtype.ext (eG.injective (congrArg Subtype.val h)),
      eG.toMonoidHom.subgroupComap_surjective_of_surjective N eG.surjective⟩
  have hMi : M.index = 2 := by
    rw [Subgroup.index_comap_of_surjective _ eG.surjective]
    exact hNi
  obtain ⟨e, he⟩ := same_universe_extension
    (hasDihedralSylowTwo_of_mulEquiv eG hGd) M hMi K hK (eM.trans eN)
  refine ⟨eG.symm.trans e, fun n => ?_⟩
  have hn : eG.symm n ∈ M := by
    change eG (eG.symm n) ∈ N
    simp
  have hh := he ⟨eG.symm n, hn⟩
  change e (eG.symm n) = _
  rw [hh]
  congr 2
  change eN (eM ⟨eG.symm n, hn⟩) = eN n
  apply congrArg eN
  apply Subtype.ext
  exact eG.apply_symm_apply n


end GorensteinWalter
