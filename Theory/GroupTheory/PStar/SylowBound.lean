module

public import Theory.GroupTheory.PStar.SylowBound.ChiefReduction
public import Theory.GroupTheory.PStar.SylowBound.ResidualReduction

/-!
# The Sylow-centralizer bound for the p-star p-core extension

The quotient by N = O_{p*p}(G) has trivial p-core. Frattini's argument makes
N C_G(P) normal, so failure of the bound yields a genuine chief subgroup Q
of G/N in its image. Its preimage M has p-star quotient M/N and p-star residual
O^p(N) = O_{p*}(G). The residual reduction supplies the hypotheses of the
extension criterion, proving that O^p(M) is p-star. Normality in G puts that
residual in O_{p*}(G), contradicting its surjection onto the nontrivial Q.

Source: GLS II, Chapter B, Theorem 5.9 (`refs/KGroup/GLS2/ChapterB.tex`).
The conclusion is O_{p*p}, as in the source proof, correcting O_{p'p} in the
transcript. The only explicit earlier-source inputs are normal-product closure
(GLS 5.6) and the extension criterion (GLS 5.3). Unconditional assembly must
supply both; no further structural premise is assumed here.
-/

public section

open Subgroup Theory.GroupTheory
universe u
namespace Subgroup
section Prime
variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [Finite G]

/-- The corrected GLS II 5.9 bound, conditional only on the universal
normal-product and extension implications from the earlier source. -/
theorem centralizer_sylow_pStarPCore_le_of_normal_sup_of_extension
    (hprod : ∀ (X : Type u) [Group X] [Finite X] (A B : Subgroup X),
      A.Normal → B.Normal → IsPStar p A → IsPStar p B → IsPStar p (A ⊔ B : Subgroup X))
    (hext : SylowBoundExtensionCriterion.{u} (p := p))
    (P : Sylow p (pStarPCore p G)) :
    centralizer ((P : Subgroup (pStarPCore p G)).map (pStarPCore p G).subtype : Set G) ≤
      pStarPCore p G := by
  classical
  let N := pStarPCore p G
  let C := centralizer ((P : Subgroup N).map N.subtype : Set G)
  let q := QuotientGroup.mk' N
  let _ : (N ⊔ C).Normal := normal_sup_centralizer_sylow N P
  let H := (N ⊔ C).map q
  let _ : H.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective N)
  by_contra hCN
  have hH : H ≠ ⊥ := by
    intro he
    apply hCN
    have h := (map_eq_bot_iff (N ⊔ C) (f := q)).mp he
    exact le_sup_right.trans (by simpa only [q, QuotientGroup.ker_mk'] using h)
  obtain ⟨Q, hQ, hQH⟩ := exists_chief_le_of_ne_bot H hH
  have hQstar : IsPStar p Q := isPStar_of_isChief_of_pCore_eq_bot
    pCore_quotient_pStarPCore_eq_bot Q hQ
  let _ := hQ.normal_upper
  let M := Q.comap q
  have hNM : N ≤ M := by simpa only [q, QuotientGroup.ker_mk'] using Q.ker_le_comap q
  have hMNC : M ≤ N ⊔ C := by
    have h := comap_mono (f := q) hQH
    simpa only [H, comap_map_eq, q, QuotientGroup.ker_mk', sup_of_le_left le_sup_left] using h
  let K := N.subgroupOf M
  let f : M →* Q :=
    { toFun := fun x => ⟨q x, x.property⟩
      map_one' := Subtype.ext (map_one q)
      map_mul' := fun x y => Subtype.ext (map_mul q (x : G) (y : G)) }
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N x.val
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    change q g ∈ Q
    rw [hg]
    exact x.property
  have hk : f.ker = K := by
    ext x
    change f x = 1 ↔ (x : G) ∈ N
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (x : G)
  have hquot : IsPStar p (M ⧸ K) := hQstar.of_equiv
    ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hk))
  have hRstar : IsPStar p (pStarCore p G) := isPStar_pStarCore_of_normal_sup (hprod G)
  have hNstar : IsPStar p (pResidual p N) := by
    let e := (pResidual p N).equivMapOfInjective N.subtype N.subtype_injective
    exact (hRstar.of_equiv (MulEquiv.subgroupCongr
      (map_pResidual_pStarPCore (p := p) (G := G))).symm).of_equiv e.symm
  let e : N ≃* K := (subgroupOfEquivOfLe hNM).symm
  let S : Sylow p K := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hKstar : IsPStar p (pResidual p K) :=
    (hNstar.of_equiv ((pResidual p N).equivMapOfInjective e.toMonoidHom e.injective)).of_equiv
      (MulEquiv.subgroupCongr (map_pResidual_of_surjective p e.toMonoidHom e.surjective))
  have hgen : K ⊔ centralizer ((S : Subgroup K).map K.subtype : Set M) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨n, hn, c, hc, he⟩ := mem_sup_of_normal_left.mp (hMNC x.property)
    have hcM : c ∈ M := by
      have h := M.mul_mem (M.inv_mem (hNM hn)) x.property
      simpa only [← he, inv_mul_cancel_left] using h
    have hcS : (⟨c, hcM⟩ : M) ∈ centralizer ((S : Subgroup K).map K.subtype : Set M) := by
      rintro z ⟨k, hk, rfl⟩
      change k ∈ (P : Subgroup N).map e.toMonoidHom at hk
      obtain ⟨a, ha, rfl⟩ := hk
      apply Subtype.ext
      exact hc a.val (mem_map.mpr ⟨a, ha, rfl⟩)
    apply mem_sup_of_normal_left.mpr
    exact ⟨⟨n, hNM hn⟩, hn, ⟨c, hcM⟩, hcS, Subtype.ext he⟩
  have hMstar := isPStar_pResidual_of_sylow_supplement hext K S hquot hKstar hgen
  have hle : (pResidual p M).map M.subtype ≤ N :=
    (le_pStarCore _ (hMstar.of_equiv
      ((pResidual p M).equivMapOfInjective M.subtype M.subtype_injective))).trans
      pStarCore_le_pStarPCore
  have hresker : pResidual p M ≤ f.ker := by
    rw [hk]
    intro x hx
    exact hle (mem_map.mpr ⟨x, hx, rfl⟩)
  have hbot : (⊤ : Subgroup Q) = ⊥ := by
    rw [← hQstar.1, ← map_pResidual_of_surjective p f hf]
    exact (map_eq_bot_iff _ (f := f)).mpr hresker
  have hQbot : Q = ⊥ := by
    apply bot_unique
    intro x hx
    have he : (⟨x, hx⟩ : Q) = 1 :=
      (mem_bot.mp (hbot ▸ (mem_top (⟨x, hx⟩ : Q))))
    exact congrArg Subtype.val he
  exact hQ.lt.ne' hQbot
end Prime

/-- The prime-two form consumed by the quasithin p-star structure assembly.
Both universal earlier-source implications remain explicit parameters. -/
theorem centralizer_sylow_twoStarPCore_le
    {G : Type u} [Group G] [Finite G]
    (hprod : ∀ (X : Type u) [Group X] [Finite X] (A B : Subgroup X),
      A.Normal → B.Normal → IsPStar 2 A → IsPStar 2 B → IsPStar 2 (A ⊔ B : Subgroup X))
    (hext : SylowBoundExtensionCriterion.{u} (p := 2))
    (P : Sylow 2 (pStarPCore 2 G)) :
    centralizer ((P : Subgroup (pStarPCore 2 G)).map (pStarPCore 2 G).subtype : Set G) ≤
      pStarPCore 2 G :=
  centralizer_sylow_pStarPCore_le_of_normal_sup_of_extension hprod hext P

end Subgroup
