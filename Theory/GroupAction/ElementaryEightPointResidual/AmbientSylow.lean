module
public import Theory.GroupAction.ElementaryEightPointResidual.PointCentralization
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Promoting the point-preimage Sylow normalizer to the ambient group

Use the actual commutator bound [R ∩ D,B] ≤ O₂(B), where D is a normal
cover of the full action on an elementary eight-group and B has A₄ image.
In the point stabilizer S₄, an element centralizing A₄ modulo any two-subgroup
of A₄ lies in A₄. This is checked by one small permutation calculation.
The literal images of R ∩ D and O₂(B) therefore put the former inside A₄.

If R were the selected Sylow subgroup of N_G(C), its intersection with
normal D would map onto a Sylow subgroup of GL₃(2), of order eight. That
cannot lie in A₄. Thus the selected Sylow strictly contains R. Since R
already has index two in an ambient Sylow subgroup, the enlargement itself
is Sylow in G. All subgroup maps and the full component-action kernel are
retained; the argument needs no identification of that kernel with O₂(D).

Source: Aschbacher–Smith 14.7.6, printed pp.1044–1045, refs/quasithin.pdf.
LocalReduction.LargePrimePointLiftSource applies this to the same original
compatible Sylow intersection whose second support was proved fixed.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupAction.ElementaryEightPointResidual

private theorem normal_cover_sylow_image_not_le_twelve
    {N E : Type*} [Group N] [Finite N] [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 8)
    (f : N →* MulAut E) (D : Subgroup N) [D.Normal] (hD : D.map f = ⊤)
    (P : Sylow 2 N) (B : Subgroup (MulAut E)) (hB : Nat.card B = 12) :
    ¬ (((P : Subgroup N).subgroupOf D).map (f.comp D.subtype)) ≤ B := by
  have hf : Function.Surjective (f.comp D.subtype) := by
    intro e
    obtain ⟨d,hd,hde⟩ := hD.ge (mem_top e)
    exact ⟨⟨d,hd⟩,hde⟩
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_normal D
  intro hle
  rw [←hQ,←Sylow.coe_mapSurjective hf] at hle
  have hd := card_dvd_of_le hle
  have hc : Nat.card (Q.mapSurjective hf) = 8 := by
    rw [Sylow.card_eq_multiplicity,card_mulAut_of_elementary_eight E hE]
    decide +kernel
  rw [hc,hB] at hd
  norm_num at hd

private theorem sylow_promotion_of_index_two
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (R A : Subgroup G) (hRS : R ≤ S)
    (hi : R.relIndex (S : Subgroup G) = 2)
    (hA : IsPGroup 2 A) (hRA : R ≤ A) (hne : R ≠ A) :
    ∃ T : Sylow 2 G, (T : Subgroup G) = A := by
  obtain ⟨P,hP⟩ := hA.exists_le_sylow
  have hrel : 2 ≤ R.relIndex A := by
    have hpos : R.relIndex A ≠ 0 := index_ne_zero_of_finite
    have h1 : R.relIndex A ≠ 1 := by
      intro he
      exact hne (le_antisymm hRA (relIndex_eq_one.mp he))
    omega
  have hcardR := relIndex_mul_relIndex (⊥ : Subgroup G) R A bot_le hRA
  rw [relIndex_bot_left,relIndex_bot_left] at hcardR
  have hcardS := relIndex_mul_relIndex (⊥ : Subgroup G) R (S : Subgroup G) bot_le hRS
  rw [relIndex_bot_left,relIndex_bot_left,hi] at hcardS
  have hcardP : Nat.card P = Nat.card S := by rw [P.card_eq_multiplicity,S.card_eq_multiplicity]
  have hPA : (P : Subgroup G) = A := (eq_of_le_of_card_ge hP (by
    rw [hcardP,←hcardS,←hcardR]
    exact Nat.mul_le_mul_left _ hrel)).symm
  exact ⟨P,hPA⟩


/-- The original component-intersection commutator bound promotes the
compatible Sylow normalizer to an actual ambient Sylow subgroup. -/
theorem point_preimage_ambient_sylow
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (R B C Z : Subgroup G) [IsElementaryAbelian 2 C]
    (hRS : R ≤ S) (hi : R.relIndex (S : Subgroup G) = 2)
    (hRC : R ≤ normalizer (C : Set G))
    (hBC : B ≤ normalizer (C : Set G))
    (hRB : R ≤ normalizer (B : Set G))
    (hc : Nat.card C = 8) (hz : Nat.card Z = 2)
    (hfixed : C ⊓ centralizer (B : Set G) = Z)
    (halt : Nat.card (conjugationImage B C) = 3 ∨
      (Nat.card (conjugationImage B C) = 12 ∧
        Nonempty (conjugationImage B C ≃* alternatingGroup (Fin 4))))
    (D : Subgroup (normalizer (C : Set G))) [D.Normal]
    (hD : D.map C.normalizerMonoidHom = ⊤)
    (hcomm : ⁅R ⊓ D.map (normalizer (C : Set G)).subtype,B⁆ ≤ B.pCoreIn 2) :
    Nat.card (conjugationImage B C) = 12 ∧
      Nonempty (conjugationImage B C ≃* alternatingGroup (Fin 4)) ∧
      let L0 := D ⊓ (conjugationImage B C).comap C.normalizerMonoidHom
      let L0G := L0.map (normalizer (C : Set G)).subtype
      conjugationImage L0G C = conjugationImage B C ∧
      (D ⊓ C.normalizerMonoidHom.ker).map (normalizer (C : Set G)).subtype ≤ L0G ∧
      ∃ P : Sylow 2 (normalizer (C : Set G)),
        R ≤ (P : Subgroup (normalizer (C : Set G))).map (normalizer (C : Set G)).subtype ∧
        (P : Subgroup (normalizer (C : Set G))).map (normalizer (C : Set G)).subtype ≤
          normalizer (L0G : Set G) ∧
        ∃ TA : Sylow 2 G, (TA : Subgroup G) =
          (P : Subgroup (normalizer (C : Set G))).map (normalizer (C : Set G)).subtype := by
  let N := normalizer (C : Set G)
  let DA := D.map N.subtype
  let A := R ⊓ DA
  have hAC : A ≤ N := inf_le_left.trans hRC
  obtain ⟨h12,he,hm,hk,P,hRP,hPN⟩ := point_preimage_sylow S R B C Z hRS hi hRC hBC hRB
    hc hz hfixed halt D hD
  have himage := conjugationImage_le_point_image A B C Z hAC hBC
    (inf_le_left.trans hRB) hc hz hfixed h12 hcomm
  have hne : R ≠ (P : Subgroup N).map N.subtype := by
    intro hsame
    have hmap : (((P : Subgroup N).subgroupOf D).map (C.normalizerMonoidHom.comp D.subtype)) =
        conjugationImage A C := by
      rw [conjugationImage_eq_map_of_le _ _ hAC,←map_map,subgroupOf_map_subtype]
      congr 1
      change _ = (R ⊓ D.map N.subtype).subgroupOf N
      rw [hsame,subgroupOf,comap_inf,
        comap_map_eq_self_of_injective N.subtype_injective,
        comap_map_eq_self_of_injective N.subtype_injective]
    exact normal_cover_sylow_image_not_le_twelve hc C.normalizerMonoidHom D hD P _ h12
      (hmap ▸ himage)
  obtain ⟨TA,hTA⟩ := sylow_promotion_of_index_two S R ((P : Subgroup N).map N.subtype)
    hRS hi (P.isPGroup'.map N.subtype) hRP hne
  exact ⟨h12,he,hm,hk,P,hRP,hPN,TA,hTA⟩

end Theory.GroupAction.ElementaryEightPointResidual
