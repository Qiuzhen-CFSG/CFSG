module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.OddSupplement.LinearComplement.Model
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.Freeness
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.TwoStructure.ModelConsequences

/-!
# The cyclic odd complement in the actual linear centralizer

The embedding constructed from the moved-point action carries the nontrivial
normal Sylow 2-subgroup of J into the concrete PSL₂ model. The intrinsic Borel
calculation and Schur–Zassenhaus give its cyclic odd complement, whose nontrivial
subgroups have no additional normalizers in J. Transport back along the actual
embedding gives both an internal complement in J and the literal ambient
subgroup product required by the Burnside argument in GLS IV, Chapter 2,
Lemma 15.5 (refs/KGroup/GLS4/Chapter2.tex).
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
local notation "L" => residualGenerated M z t
local notation "J" => centralizer (L : Set G)
local notation "U" => Subgroup.map (Subgroup.subtype J) (pCore 2 J)
include d

/-- The native complement in J, including all its nontrivial subgroup normalizers. -/
public theorem Context.exists_linear_centralizer_complement_native (hne : pCore 2 J ≠ ⊥) :
    ∃ Y : Subgroup J, (pCore 2 J).IsComplement' Y ∧
      Odd (Nat.card Y) ∧ IsCyclic Y ∧ Nat.card Y ∣ 2 ^ n - 1 ∧
      ∀ P : Subgroup J, P ≤ Y → P ≠ ⊥ → normalizer (P : Set J) = Y := by
  obtain ⟨hm⟩ := d.centralizerLocalModelData
  obtain ⟨S, hS⟩ := d.centralizer_twoCore_sylow hm hne
  let f := d.model.toMonoidHom.comp hm.embedding
  have hf : Function.Injective f := d.model.injective.comp hm.embedding_injective
  let e : J ≃* f.range := MonoidHom.ofInjective hf
  let P : Sylow 2 f.range := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP : (P : Subgroup f.range) = (pCore 2 J).map e.toMonoidHom := by
    exact (Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S).trans
      (congrArg (Subgroup.map e.toMonoidHom) hS)
  let : (P : Subgroup f.range).Normal := hP ▸
    (inferInstance : (pCore 2 J).Normal).map e.toMonoidHom e.surjective
  have hPne : (P : Subgroup f.range) ≠ ⊥ := by
    rw [hP]
    exact fun hb => hne (((pCore 2 J).map_eq_bot_iff_of_injective e.injective).mp hb)
  obtain ⟨C, hC, hcodd, hccyc, hcdiv, hcnorm⟩ :=
    LinearComplement.exists_complement_of_normal_sylow
      (GaloisField.card 2 n (by have := d.parameter; omega))
      (by have := d.parameter; omega) f.range P hPne
  let Y := C.map e.symm.toMonoidHom
  have hY : Y.map e.toMonoidHom = C := (map_symm_eq_iff_map_eq Y (e := e)).mp rfl
  have hback : (P : Subgroup f.range).map e.symm.toMonoidHom = pCore 2 J :=
    (map_symm_eq_iff_map_eq _ (e := e)).mpr hP.symm
  have hc : Nat.card Y = Nat.card C :=
    (Nat.card_congr (C.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).toEquiv).symm
  have hp : Nat.card (pCore 2 J) = Nat.card P := by
    rw [hP]
    exact Nat.card_congr ((pCore 2 J).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
  have hycomp : (pCore 2 J).IsComplement' Y := by
    apply isComplement'_of_card_mul_and_disjoint
    · rw [hc, hp, hC.card_mul_card]
      exact (Nat.card_congr e.toEquiv).symm
    · simpa only [hback] using (disjoint_map (f := e.symm.toMonoidHom) e.symm.injective hC.disjoint)
  let : IsCyclic C := hccyc
  let : IsCyclic Y := isCyclic_of_surjective
    (C.equivMapOfInjective e.symm.toMonoidHom e.symm.injective)
    (C.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).surjective
  refine ⟨Y, hycomp, hc ▸ hcodd, inferInstance, hc ▸ hcdiv, ?_⟩
  intro Q hQY hQne
  have hQC : Q.map e.toMonoidHom ≤ C := hY ▸ map_mono hQY
  have hQmapne : Q.map e.toMonoidHom ≠ ⊥ :=
    fun hb => hQne ((Q.map_eq_bot_iff_of_injective e.injective).mp hb)
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_equiv_normalizer_eq Q e, hY]
  exact hcnorm _ hQC hQmapne

/-- The literal ambient complement and normalizer formulas used in source 15.5. -/
public theorem Context.exists_linear_centralizer_complement (hne : pCore 2 J ≠ ⊥) :
    ∃ Y : Subgroup G, Y ≤ J ∧ Odd (Nat.card Y) ∧ IsCyclic Y ∧
      Nat.card Y ∣ 2 ^ n - 1 ∧ (pCore 2 J).IsComplement' (Y.subgroupOf J) ∧
      (J : Set G) = (U : Set G) * (Y : Set G) ∧
      ∀ P : Subgroup G, P ≤ Y → P ≠ ⊥ → J ⊓ normalizer (P : Set G) = Y := by
  obtain ⟨Y₀, hcomp, hodd, hcyc, hdiv, hnorm⟩ :=
    d.exists_linear_centralizer_complement_native hne
  let Y := Y₀.map (J).subtype
  have hYJ : Y ≤ J := map_subtype_le Y₀
  have hYsub : Y.subgroupOf J = Y₀ := by
    ext x
    exact mem_map_iff_mem (J).subtype_injective
  have hc : Nat.card Y = Nat.card Y₀ :=
    (Nat.card_congr (Y₀.equivMapOfInjective (J).subtype (J).subtype_injective).toEquiv).symm
  let : IsCyclic Y₀ := hcyc
  let : IsCyclic Y := isCyclic_of_surjective
    (Y₀.equivMapOfInjective (J).subtype (J).subtype_injective)
    (Y₀.equivMapOfInjective (J).subtype (J).subtype_injective).surjective
  refine ⟨Y, hYJ, hc ▸ hodd, inferInstance, hc ▸ hdiv, hYsub ▸ hcomp, ?_, ?_⟩
  · ext g
    constructor
    · intro hg
      obtain ⟨⟨a, b⟩, hab⟩ := hcomp.surjective ⟨g, hg⟩
      exact ⟨a.val, ⟨a.val, a.property, rfl⟩,
        b.val, ⟨b.val, b.property, rfl⟩, congrArg Subtype.val hab⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact (J).mul_mem (map_subtype_le _ ha) (hYJ hb)
  · intro P hPY hPne
    have hPJ : P ≤ J := hPY.trans hYJ
    have hPsub : P.subgroupOf J ≤ Y₀ := hYsub ▸ subgroupOf_mono (J) hPY
    have hPsubne : P.subgroupOf J ≠ ⊥ := by
      intro hb
      have hh := map_subgroupOf_eq_of_le hPJ
      rw [hb, Subgroup.map_bot] at hh
      exact hPne hh.symm
    have he := hnorm _ hPsub hPsubne
    rw [← subgroupOf_normalizer_eq hPJ] at he
    have hmap := congrArg (Subgroup.map (J).subtype) he
    rw [subgroupOf_map_subtype] at hmap
    exact inf_comm _ _ |>.trans hmap

end BenderSuzuki.ZD.LinearExclusion
