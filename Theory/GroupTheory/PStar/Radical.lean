module

public import Theory.GroupTheory.PStar.Basic

/-!
# The p-star core and its p-core extension

Surjective maps preserve the normal join defining the p-star core, so it
is characteristic. Its generators also prove p-perfectness and containment
in O^p(G). Restricting the generators gives the overgroup property. The
p-core extension has residual exactly the embedded p-star core.

Finite normal-product closure makes the join itself p-star, by choosing a
maximal normal p-star subgroup. The final normal-subgroup and residual
invariance lemmas expose this remaining input through an explicit p-star
hypothesis on the intrinsic core; they do not assume that normality is
transitive.

Source: GLS II, Chapter B, Definition 5.7 and Lemma 5.8(i),(ii),(v).
-/

public section

open Subgroup Theory.GroupTheory
namespace Subgroup
variable {p : ℕ} {G H : Type*} [Group G] [Group H]

/-- Every normal p-star subgroup is contained in the p-star core. -/
theorem le_pStarCore (N : Subgroup G) [N.Normal] (hN : IsPStar p N) :
    N ≤ pStarCore p G := le_sSup ⟨inferInstance, hN⟩

/-- A p-star group is its own p-star core. -/
theorem pStarCore_eq_top [Finite G] [Fact p.Prime] (hG : IsPStar p G) :
    pStarCore p G = ⊤ := by
  exact top_unique (le_pStarCore ⊤ (hG.of_equiv Subgroup.topEquiv.symm))

/-- Surjections map the p-star core into the target p-star core. -/
theorem map_pStarCore_le_of_surjective [Finite G] [Fact p.Prime]
    (f : G →* H) (hf : Function.Surjective f) :
    (pStarCore p G).map f ≤ pStarCore p H := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  rintro N ⟨hN, hstar⟩
  let : N.Normal := hN
  let : (N.map f).Normal := hN.map f hf
  exact map_le_iff_le_comap.mp (le_pStarCore (N.map f)
    (hstar.of_surjective (f.subgroupMap N) (f.subgroupMap_surjective N)))

/-- Isomorphisms preserve the p-star core. -/
theorem map_pStarCore [Finite G] [Finite H] [Fact p.Prime] (e : G ≃* H) :
    (pStarCore p G).map e.toMonoidHom = pStarCore p H := by
  apply le_antisymm (map_pStarCore_le_of_surjective e.toMonoidHom e.surjective)
  have h := map_mono (f := e.toMonoidHom)
    (map_pStarCore_le_of_surjective e.symm.toMonoidHom e.symm.surjective (p := p))
  simpa [map_map] using h

/-- The p-star core is characteristic, GLS II 5.8(i). -/
instance pStarCore_characteristic [Finite G] [Fact p.Prime] :
    (pStarCore p G).Characteristic := by
  apply characteristic_iff_map_le.mpr
  intro e
  exact map_pStarCore_le_of_surjective e.toMonoidHom e.surjective

/-- The p-star core is contained in the p-residual. -/
theorem pStarCore_le_pResidual : pStarCore p G ≤ pResidual p G := by
  apply sSup_le
  rintro N ⟨_, hN⟩
  exact le_pResidual_of_isPPerfect N ((pResidual_eq_top_iff p N).mp hN.1)

/-- Restricting to an overgroup of the core preserves its containment,
with the intrinsic core embedded by the literal subtype map (GLS II 5.8(i)). -/
theorem pStarCore_le_map_of_le [Finite G] [Fact p.Prime]
    (Y : Subgroup G) (hY : pStarCore p G ≤ Y) :
    pStarCore p G ≤ (pStarCore p Y).map Y.subtype := by
  apply sSup_le
  rintro N ⟨hN, hstar⟩
  let : N.Normal := hN
  have hNY : N ≤ Y := (le_pStarCore N hstar).trans hY
  have hrel : IsPStar p (N.subgroupOf Y) :=
    hstar.of_equiv (subgroupOfEquivOfLe hNY).symm
  have hle := map_mono (f := Y.subtype) (le_pStarCore (N.subgroupOf Y) hrel)
  simpa only [map_subgroupOf_eq_of_le hNY] using hle

/-- Each core is p-perfect even before normal-product closure is used. -/
theorem isPPerfect_pStarCore [Finite G] [Fact p.Prime] :
    IsPPerfect p (pStarCore p G) := by
  let R := pStarCore p G
  have h : R ≤ (pResidual p R).map R.subtype := by
    apply sSup_le
    rintro N ⟨hN, hstar⟩
    let : N.Normal := hN
    have hNR : N ≤ R := le_pStarCore N hstar
    have hrel : IsPStar p (N.subgroupOf R) :=
      hstar.of_equiv (subgroupOfEquivOfLe hNR).symm
    have hle := map_mono (f := R.subtype)
      (le_pResidual_of_isPPerfect (N.subgroupOf R)
        ((pResidual_eq_top_iff p _).mp hrel.1))
    simpa only [map_subgroupOf_eq_of_le hNR] using hle
  apply (pResidual_eq_top_iff p R).mp
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := mem_map.mp (h x.property)
  exact (Subtype.ext he : y = x) ▸ hy

/-- The p-star core is contained in its p-core extension. -/
theorem pStarCore_le_pStarPCore : pStarCore p G ≤ pStarPCore p G := by
  intro x hx
  change QuotientGroup.mk' (pStarCore p G) x ∈ pCore p (G ⧸ pStarCore p G)
  have he : QuotientGroup.mk' (pStarCore p G) x = 1 :=
    (QuotientGroup.eq_one_iff x).mpr hx
  rw [he]
  exact one_mem _

/-- The p-residual of the p-core extension, embedded in the original group,
is exactly the p-star core. This uses only p-perfectness of the join. -/
theorem map_pResidual_pStarPCore [Finite G] [Fact p.Prime] :
    (pResidual p (pStarPCore p G)).map (pStarPCore p G).subtype = pStarCore p G := by
  let R := pStarCore p G
  let D := pStarPCore p G
  let N := R.subgroupOf D
  let q := QuotientGroup.mk' R
  let f : D →* pCore p (G ⧸ R) :=
    { toFun := fun x => ⟨q x, x.property⟩
      map_one' := Subtype.ext (map_one q)
      map_mul' := fun x y => Subtype.ext (map_mul q (x : G) (y : G)) }
  have hk : f.ker = N := by
    ext x
    change f x = 1 ↔ (x : G) ∈ R
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (x : G)
  have hquot : IsPGroup p (D ⧸ N) := by
    have h : IsPGroup p (D ⧸ f.ker) :=
      (pCore_isPGroup (p := p) (G := G ⧸ R)).to_subgroup f.range |>.of_equiv
        (QuotientGroup.quotientKerEquivRange f).symm
    exact h.of_equiv (QuotientGroup.quotientMulEquivOfEq hk)
  let e : R ≃* N := (subgroupOfEquivOfLe
    (pStarCore_le_pStarPCore (p := p) (G := G))).symm
  have hN : IsPPerfect p N :=
    (isPPerfect_pStarCore (p := p) (G := G)).of_surjective
      e.toMonoidHom e.surjective
  have he := pResidual_eq_of_isPPerfect N hN hquot
  change (pResidual p D).map D.subtype = R
  rw [he]
  exact map_subgroupOf_eq_of_le pStarCore_le_pStarPCore

/-- Finite normal-product closure makes the defining join itself p-star.
This is the precise lattice step from GLS II 5.6 to Definition 5.7; the
normal-product premise is discharged by the action theorem in source assembly. -/
theorem isPStar_pStarCore_of_normal_sup [Finite G] [Fact p.Prime]
    (hprod : ∀ A B : Subgroup G, A.Normal → B.Normal →
      IsPStar p A → IsPStar p B → IsPStar p (A ⊔ B : Subgroup G)) :
    IsPStar p (pStarCore p G) := by
  classical
  have hbot : IsPStar p (⊥ : Subgroup G) := isPStar_of_coprime_card (by simp)
  obtain ⟨M, hM, hmax⟩ := exists_maximal_of_wellFoundedGT
    (fun M : Subgroup G => M.Normal ∧ IsPStar p M) ⟨⊥, inferInstance, hbot⟩
  have he : pStarCore p G = M := by
    refine le_antisymm (sSup_le ?_) (le_sSup hM)
    rintro N ⟨hN, hstar⟩
    let : M.Normal := hM.1
    let : N.Normal := hN
    exact le_sup_right.trans (hmax
      ⟨inferInstance, hprod M N hM.1 hN hM.2 hstar⟩ le_sup_left)
  rw [he]
  exact hM.2

/-- Once the intrinsic core is p-star, characteristicity gives the normal-subgroup
containment in GLS II 5.8(i). The normality hypothesis refers to G. -/
theorem map_pStarCore_subtype_le_of_isPStar [Finite G] [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hstar : IsPStar p (pStarCore p N)) :
    (pStarCore p N).map N.subtype ≤ pStarCore p G := by
  let e := (pStarCore p N).equivMapOfInjective N.subtype N.subtype_injective
  exact le_pStarCore _ (hstar.of_equiv e)

/-- Residual invariance in GLS II 5.8(ii), with the sole remaining premise
that the core of O^p(G) is p-star. The residual and core are embedded in G. -/
theorem map_pStarCore_pResidual_eq_of_isPStar [Finite G] [Fact p.Prime]
    (hstar : IsPStar p (pStarCore p (pResidual p G))) :
    (pStarCore p (pResidual p G)).map (pResidual p G).subtype = pStarCore p G := by
  exact le_antisymm (map_pStarCore_subtype_le_of_isPStar _ hstar)
    (pStarCore_le_map_of_le _ pStarCore_le_pResidual)

/-- Normal-product closure for the residual supplies the remaining input to
the embedded residual-invariance statement. -/
theorem map_pStarCore_pResidual_eq_of_normal_sup [Finite G] [Fact p.Prime]
    (hprod : ∀ A B : Subgroup (pResidual p G), A.Normal → B.Normal →
      IsPStar p A → IsPStar p B → IsPStar p (A ⊔ B : Subgroup (pResidual p G))) :
    (pStarCore p (pResidual p G)).map (pResidual p G).subtype = pStarCore p G :=
  map_pStarCore_pResidual_eq_of_isPStar (isPStar_pStarCore_of_normal_sup hprod)

end Subgroup
