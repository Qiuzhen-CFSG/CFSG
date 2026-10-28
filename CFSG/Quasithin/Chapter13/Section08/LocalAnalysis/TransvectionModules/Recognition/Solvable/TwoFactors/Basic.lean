module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.Factors
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.FaithfulClosure
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.Preimage
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.PPerfectHom


/-!
# Sylow transport and generation for the two-factor branch

The image of the standing Sylow two-subgroup in H/O₂(H) is Sylow, as is its
intersection with the normal transvection closure. A faithful transvection
can be conjugated into this image without changing its normal closure.

For the actual internal B.1.8 factors, a conjugation permutation fixing a
factor containing t would make that factor contain the whole normal closure.
Its order six contradicts the closure's order 36. A Sylow two-subgroup has
the full image on a set of two factors, so it already moves that factor.
Two-perfect subgroups, on the other hand, fix each factor.

`FactorAction` records the conjugation permutation still to be constructed;
none of these conditional lemmas asserts the source's final contradiction.
Source: Aschbacher–Smith, 13.8.5, printed p.947 (PDF p.964), combined
manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.TwoFactors
open ChapterB
variable {G A E : Type*} [Group G] [Finite G] [Group A] [Finite A]
  [AddCommGroup E] [Module (ZMod 2) E]

noncomputable def sourceSylow (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) : Sylow 2 (Source.Hstar H) :=
  (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))

theorem sourceSylow_eq (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) :
    (sourceSylow T H hTH : Subgroup (Source.Hstar H)) = Source.starImage H T := rfl

theorem sourceSylow_restrict_normalClosure (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (t : Source.Hstar H) :
    ∃ S : Sylow 2 (normalClosure ({t} : Set (Source.Hstar H))),
      (S : Subgroup _) = (Source.starImage H T).subgroupOf (normalClosure ({t} : Set _)) :=
  (sourceSylow T H hTH).exists_subgroupOf_eq_of_normal _

omit [Finite A] in
theorem conjugate_normalClosure (t a : A) :
    normalClosure ({a * t * a⁻¹} : Set A) = normalClosure ({t} : Set A) := by
  apply le_antisymm
  · apply normalClosure_le_normal
    rw [Set.singleton_subset_iff]
    exact (inferInstance : (normalClosure ({t} : Set A)).Normal).conj_mem t
      (subset_normalClosure (Set.mem_singleton t)) a
  · apply normalClosure_le_normal
    rw [Set.singleton_subset_iff]
    have h := (inferInstance : (normalClosure ({a * t * a⁻¹} : Set A)).Normal).conj_mem
      (a * t * a⁻¹) (subset_normalClosure (Set.mem_singleton _)) a⁻¹
    have he : a⁻¹ * (a * t * a⁻¹) * (a⁻¹)⁻¹ = t := by group
    rwa [he] at h

theorem exists_transvection_in_sylow (ρ : Representation (ZMod 2) A E)
    (hρ : Function.Injective ρ) (t : A) (ht : IsTransvection ρ t) (T : Sylow 2 A) :
    ∃ a : A, a * t * a⁻¹ ∈ T ∧ IsTransvection ρ (a * t * a⁻¹) ∧
      normalClosure ({a * t * a⁻¹} : Set A) = normalClosure ({t} : Set A) := by
  have hp : IsPGroup 2 (zpowers t) :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one (ht.square hρ)).isPGroup
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A S T
  have hle : (zpowers t).map (MulAut.conj a).toMonoidHom ≤ (T : Subgroup A) := by
    rw [← ha]
    exact map_mono hS
  exact ⟨a, hle (mem_map_of_mem _ (mem_zpowers t)), ht.conjugate a,
    conjugate_normalClosure t a⟩

/-- The source transvection can be conjugated into the literal image of T.
The membership H∈Hz supplies Sylow restriction, and the earlier centralizer
bound supplies faithfulness. -/
theorem source_transvection_in_sylow
    (T : Sylow 2 G) (H L₁ G₁ M V₃ V₁ : Subgroup G)
    (hH : H ∈ Source.Hz L₁ T G₁ M)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (σ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hσ : IsConjugation H V₃ V₁ σ)
    (hcentralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H)
    (t : Source.Hstar H) (ht : IsTransvection σ t) :
    ∃ a : Source.Hstar H, a * t * a⁻¹ ∈ Source.starImage H T ∧
      IsTransvection σ (a * t * a⁻¹) ∧
      normalClosure ({a * t * a⁻¹} : Set (Source.Hstar H)) = normalClosure ({t} : Set _) :=
  exists_transvection_in_sylow σ (faithful_of_centralizer_le_core σ hσ hcentralizer)
    t ht (sourceSylow T H (le_sup_right.trans hH.1.2))

variable {ρ : Representation (ZMod 2) A E}

noncomputable def ambientFactor (t : A)
    (d : SolvableFFFactors (ρ.comp (normalClosure ({t} : Set A)).subtype))
    (i : Fin d.count) : Subgroup A :=
  (d.factor i).map (normalClosure ({t} : Set A)).subtype

omit [Finite A] in
theorem closure_card (t : A)
    (d : SolvableFFFactors (ρ.comp (normalClosure ({t} : Set A)).subtype))
    (hJ : offenderSubgroup (ρ.comp (normalClosure ({t} : Set A)).subtype) = ⊤) :
    Nat.card (normalClosure ({t} : Set A)) = 6 ^ d.count := by
  have h := Nat.card_congr d.groupProduct.toEquiv
  rw [Nat.card_pi] at h
  simp only [d.factor_card, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [hJ, Nat.card_congr (Subgroup.topEquiv).toEquiv] at h
  exact h.symm

omit [Finite A] in
theorem ambientFactor_ne_closure (t : A)
    (d : SolvableFFFactors (ρ.comp (normalClosure ({t} : Set A)).subtype))
    (hJ : offenderSubgroup (ρ.comp (normalClosure ({t} : Set A)).subtype) = ⊤)
    (hc : d.count = 2) (i : Fin d.count) :
    ambientFactor t d i ≠ normalClosure ({t} : Set A) := by
  intro he
  have hcard := closure_card t d hJ
  have hmap : Nat.card (ambientFactor t d i) = 6 :=
    (Nat.card_congr ((d.factor i).equivMapOfInjective _ Subtype.val_injective).toEquiv).symm.trans
      (d.factor_card i)
  rw [he, hcard, hc] at hmap
  norm_num at hmap

/-- A permutation of the literal factors, with the ambient conjugation equation.
This is conclusion data to be constructed, not an extra source hypothesis. -/
structure FactorAction (t : A)
    (d : SolvableFFFactors (ρ.comp (normalClosure ({t} : Set A)).subtype)) where
  permutation : A →* Equiv.Perm (Fin d.count)
  map_factor : ∀ a i, (ambientFactor t d i).map (MulAut.conj a).toMonoidHom =
    ambientFactor t d (permutation a i)

private theorem factorPerm_isPGroup {n : ℕ} (hn : n = 2) :
    IsPGroup 2 (Equiv.Perm (Fin n)) := IsPGroup.of_card (n := 1) (by
  subst n
  simp [Nat.card_eq_fintype_card, Fintype.card_perm])

omit [Finite A] in
/-- Two-perfect local subgroups fix each of two permuted factors. -/
theorem twoPerfect_normalizes_factors (t : A)
    (d : SolvableFFFactors (ρ.comp (normalClosure ({t} : Set A)).subtype))
    (hc : d.count = 2) (α : FactorAction t d) (B : Subgroup A)
    (hB : IsPPerfect 2 B) (i : Fin d.count) :
    B ≤ normalizer (ambientFactor t d i : Set A) := by
  have he := hB.hom_eq_one_of_isPGroup (factorPerm_isPGroup hc)
    (α.permutation.comp B.subtype)
  intro b hb
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hbi : α.permutation b = 1 :=
    DFunLike.congr_fun he (⟨b, hb⟩ : B)
  exact (α.map_factor b i).trans (by rw [hbi]; rfl)

/-- A Sylow two-subgroup has the full image in a permutation group on two factors. -/
theorem sylow_factorAction_range {n : ℕ} (hn : n = 2)
    (α : A →* Equiv.Perm (Fin n)) (T : Sylow 2 A) :
    (T : Subgroup A).map α = α.range := by
  have hp := factorPerm_isPGroup hn
  let S := T.mapSurjective α.rangeRestrict_surjective
  have htop : (S : Subgroup α.range) = ⊤ :=
    (S.is_maximal' ((hp.to_subgroup α.range).to_subgroup ⊤) le_top).symm
  apply le_antisymm (map_le_range _ _)
  rintro x ⟨a, rfl⟩
  have hmem : (⟨α a, a, rfl⟩ : α.range) ∈ S := by
    change (⟨α a, a, rfl⟩ : α.range) ∈ (S : Subgroup α.range)
    rw [htop]
    trivial
  obtain ⟨b, hb, he⟩ := hmem
  exact ⟨b, hb, congrArg Subtype.val he⟩

/-- Once the actual factor permutation is constructed, normal generation forces
its Sylow action to move the factor containing the transvection. -/
theorem sylow_moves_factor (t : A)
    (d : SolvableFFFactors (ρ.comp (normalClosure ({t} : Set A)).subtype))
    (hJ : offenderSubgroup (ρ.comp (normalClosure ({t} : Set A)).subtype) = ⊤)
    (hc : d.count = 2) (α : FactorAction t d)
    (i : Fin d.count) (hi : t ∈ ambientFactor t d i) (T : Sylow 2 A) :
    ∃ a ∈ (T : Subgroup A), α.permutation a i ≠ i := by
  classical
  by_contra h
  push Not at h
  have hfix (a : A) : α.permutation a i = i := by
    have hm : α.permutation a ∈ (T : Subgroup A).map α.permutation := by
      rw [sylow_factorAction_range hc α.permutation T]
      exact ⟨a, rfl⟩
    obtain ⟨b, hb, he⟩ := hm
    rw [← he]
    exact h b hb
  have hn : (ambientFactor t d i).Normal := normal_iff_map_conj_eq.mpr (by
    intro a
    change (ambientFactor t d i).map (MulAut.conj a).toMonoidHom = _
    rw [α.map_factor, hfix])
  have hle : normalClosure ({t} : Set A) ≤ ambientFactor t d i :=
    normalClosure_le_normal (by simpa using hi)
  exact ambientFactor_ne_closure t d hJ hc i
    (le_antisymm (map_subtype_le _) hle)

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.TwoFactors

end
