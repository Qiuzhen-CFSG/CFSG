module

public import Stellmacher.SectionFour.LemmaFourThree
public import Stellmacher.BaumannNormalizer

/-!
# A critical partner does not normalize the Baumann subgroup of `O₂(C)`

For a critical pair `(P,Pstar)` with `P ≤ C`, the partner `Pstar` cannot
normalize `B₀ = C_{O₂(C)}(Ω₁(Z(J(O₂(C)))))`. This proves the normalizer
assertion in the second paragraph of Stellmacher (4.6).

The nontrivial 2-group `O₂(C)` has nontrivial center, and that center lies
in `B₀`. On the other hand, `C` normalizes `B₀` by the imported Baumann
normalizer theorem. If `Pstar` normalized it too, `B₀` would be a normal
2-subgroup of `P ⋁ Pstar`: it lies in `O₂(C) ≤ S ≤ P`. The critical-pair
condition gives `O₂(P ⋁ Pstar)=1`, a contradiction.

Source: `refs/latex/stellmacher-n-group.tex`, proof of (4.6), using the
Section 4 definition of `Lambda` and nontriviality of `O₂(C)` from (4.3).
-/

namespace Stellmacher.SectionFour

universe u

private theorem baumann_ne_bot
    {G : Type u} [Group G] [Finite G] (Q : Subgroup G)
    (hQp : IsPGroup 2 Q) (hQne : Q ≠ ⊥) :
    Q ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G) ≠ ⊥ := by
  let _ : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
  have hZnontrivial : Nontrivial (Subgroup.center Q) := hQp.center_nontrivial
  have hZne : Subgroup.center Q ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).mp hZnontrivial
  have hJQ : elementaryAbelianMaxJ Q ≤ Q :=
    sSup_le fun _ hA ↦ hA.1
  have hWQ : omegaOneCenterAmbient (elementaryAbelianMaxJ Q) ≤ Q :=
    (Subgroup.map_subtype_le _).trans hJQ
  have hZB : (Subgroup.center Q).map Q.subtype ≤
      Q ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G) := by
    intro z hz
    obtain ⟨zQ, hzQ, rfl⟩ := hz
    refine ⟨zQ.property, ?_⟩
    change (zQ : G) ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzQ) ⟨w, hWQ hw⟩)
  intro hbot
  have hZmap : (Subgroup.center Q).map Q.subtype = ⊥ :=
    le_bot_iff.mp (hZB.trans_eq hbot)
  exact hZne ((Subgroup.map_eq_bot_iff_of_injective
    (Subgroup.center Q) Q.subtype_injective).mp hZmap)

private theorem le_normalizer_core
    {G : Type u} [Group G] (L : Subgroup G) :
    L ≤ Subgroup.normalizer (twoCoreAmbient L : Set G) := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_subtype_le (pCore 2 L))).mp
  rw [subgroupOf_map_subtype_eq]
  infer_instance

/-- The partner of a member contained in `C` does not normalize `B₀`. -/
public theorem baumann_not_normalized_by_partner
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G))
    (P Pstar : Subgroup G) (hpair : (P, Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S) :
    ¬ Pstar ≤ Subgroup.normalizer
      ((twoCoreAmbient (cSubgroup S) ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient (cSubgroup S))) :
          Set G) : Subgroup G) : Set G) := by
  let Q := twoCoreAmbient (cSubgroup S)
  let B := Q ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G)
  have hQp : IsPGroup 2 Q :=
    (pCore_isPGroup (p := 2) (G := cSubgroup S)).map (cSubgroup S).subtype
  have hBne : B ≠ ⊥ :=
    baumann_ne_bot Q hQp (twoCore_cSubgroup_ne_bot S heven)
  have hBp : IsPGroup 2 B := hQp.to_le inf_le_left
  have hPN : P ≤ Subgroup.normalizer (B : Set G) :=
    ((hPC.trans (le_normalizer_core _)).trans (normalizer_le_normalizer_baumann _))
  intro hPstarN
  have hjoinN : P ⊔ Pstar ≤ Subgroup.normalizer (B : Set G) := sup_le hPN hPstarN
  have hSP : (S : Subgroup G) ≤ P := by
    obtain ⟨T, hT⟩ := hpair.1.1.2.1
    rw [← hT]
    exact Subgroup.map_subtype_le _
  have hSC : (S : Subgroup G) ≤ cSubgroup S := hSP.trans hPC
  have hQS : Q ≤ (S : Subgroup G) := by
    let T : Sylow 2 (cSubgroup S) := S.subtype hSC
    have hTmap : (T : Subgroup (cSubgroup S)).map (cSubgroup S).subtype =
        (S : Subgroup G) := by
      rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSC]
    rw [← hTmap]
    exact Subgroup.map_mono
      ((pCore_isPGroup (p := 2) (G := cSubgroup S)).le_sylow_of_normal T)
  have hBJ : B ≤ P ⊔ Pstar :=
    inf_le_left.trans (hQS.trans (hSP.trans le_sup_left))
  have hBN : (B.subgroupOf (P ⊔ Pstar)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBJ).mpr hjoinN
  have hBpJ : IsPGroup 2 (B.subgroupOf (P ⊔ Pstar)) :=
    hBp.of_equiv (Subgroup.subgroupOfEquivOfLe hBJ).symm
  have hBcore : B ≤ twoCoreAmbient (P ⊔ Pstar) := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hBJ]
    exact Subgroup.map_mono (le_sSup ⟨hBN, hBpJ⟩)
  exact hBne (le_bot_iff.mp (hBcore.trans_eq hpair.2.2))

end Stellmacher.SectionFour
