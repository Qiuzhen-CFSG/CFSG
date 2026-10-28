module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.SplitOrRee
public import Theory.SpecificGroups.PSL3.LinearThreeRadicalCubic
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Smaller two-cores in the linear-three component rows

A proper full-Sylow local component in PSL₃(q) is a point or line
parabolic residual, whose two-core has order q². The same assertion
holds in SL₃(q) after the literal central projection. Transport through
K/O₂(K) therefore shows that O₂(L₂) cannot lie in O₂(K).

Conversely, in a perfect group with quasisimple two-core quotient, a
proper normal kernel has central image in that quotient. Any two-subgroup
in that kernel maps trivially, since the quotient has trivial two-core.
Thus centralization of full V₂ by O₂(L₂), together with noncentrality of
L₂, gives the opposite containment. SecondLinear applies both arguments
to the actual second-normalizer action, without recognizing a new module
or dropping the fixed layer C_V(L).

Source: Aschbacher--Smith 11.1.2, printed pp.764--765, using the
parabolic embeddings of A.3.12. This is the local core argument for
qt-d-1222-natural-relative-components.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin CFSG.Quasithin.ChapterA.Section03
open CFSG.Quasithin.Chapter1.Section02
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.SecondLinear

private theorem projective_local_core_ne_bot
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (S : Sylow 2 PSL(3,F)) (B : Subgroup PSL(3,F))
    (hB : B ∈ localCComponents S) (hp : B ≠ ⊤) : pCore 2 B ≠ ⊥ := by
  obtain ⟨g,hg⟩ := SourceEmbeddings.FiveLocalFF.linear_three_local_placement hF hn S B hB hp
  let a := (MulAut.conj g).subgroupMap B
  have hc : Nat.card (pCore 2 B) = Nat.card F ^ 2 := by
    have hb (e : B ≃* Matrix.PSL3.LinearThree.pointLocalSL F) :
        Nat.card (pCore 2 B) = Nat.card F ^ 2 := by
      rw [Nat.card_congr ((e.subgroupMap (pCore 2 B)).trans
        (MulEquiv.subgroupCongr (pCore_map_iso 2 e))).toEquiv]
      exact Matrix.PSL3.LinearThree.card_pointLocalSL_twoCore F
    rcases hg with h | h
    · exact hb ((a.trans (MulEquiv.subgroupCongr h)).trans
        (Matrix.PSL3.LinearThree.pointLocalProjectEquiv F).symm)
    · exact hb (((a.trans (MulEquiv.subgroupCongr h)).trans
        (Matrix.PSL3.LinearThree.lineLocalProjectEquiv F).symm).trans
        (Matrix.PSL3.LinearThree.pointLineLocalEquiv F).symm)
  intro hz
  rw [hz,Subgroup.card_bot] at hc
  have hh : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega : 2 ≤ n)
  nlinarith

private theorem special_linear_local_core_ne_bot
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (S : Sylow 2 SL(3,F)) (B : Subgroup SL(3,F))
    (hB : B ∈ localCComponents S) (hp : B ≠ ⊤)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n)) : pCore 2 B ≠ ⊥ := by
  intro hz
  let f := Matrix.PSL3.projection F
  let : Group.IsPerfect B := by
    let := hB.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup SL(3,F)) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  have hp' : B.map f ≠ ⊤ := by
    intro ht
    apply hp
    apply top_unique
    apply le_of_map_le_of_perfect f (Matrix.PSL3.projection_ker F).le ⊤ B
    rw [ht]
    exact le_top
  have hk : IsPGroup 2 (f.subgroupMap B).ker := by
    apply pCore_isPGroup.to_le
    intro b hb
    have hc : (b : SL(3,F)) ∈ center SL(3,F) :=
      (Matrix.PSL3.projection_ker F).le (congrArg Subtype.val hb)
    have hbc : b ∈ center B := by
      apply mem_center_iff.mpr
      intro a
      exact Subtype.ext (mem_center_iff.mp hc a)
    let q := QuotientGroup.mk' (pCore 2 B)
    have hz' : q b ∈ center (B ⧸ pCore 2 B) := by
      apply mem_center_iff.mpr
      intro a
      obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) a
      rw [← map_mul,← map_mul,mem_center_iff.mp hbc a]
    rw [ChapterC.Section05.NormalizerControl.EmbeddingSelection.binary_center_eq_bot hm,mem_bot] at hz'
    exact (QuotientGroup.eq_one_iff b).mp hz'
  have he : pCore 2 (B.map f) = ⊥ := by
    have ht := (f.subgroupMap B).comap_pCore_of_ker_isPGroup (f.subgroupMap_surjective B) hk
    have ht' := congrArg (map (f.subgroupMap B)) ht
    simpa only [map_comap_eq_self (MonoidHom.range_eq_top_of_surjective _
      (f.subgroupMap_surjective B) ▸ le_top),hz,Subgroup.map_bot] using ht'
  exact projective_local_core_ne_bot hF hn (S.mapSurjective (Matrix.PSL3.projection_surjective F))
    (B.map f) (localCComponents_map_of_solvable_ker hB f) hp' he

private theorem image_core_eq_bot
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    (f : G →* A) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hcore : pCore 2 G ≤ f.ker) : pCore 2 A = ⊥ := by
  have hpre := f.comap_pCore_of_ker_isPGroup hf hk
  apply bot_unique
  calc
    pCore 2 A = ((pCore 2 A).comap f).map f :=
      (map_comap_eq_self (f.range_eq_top_of_surjective hf ▸ le_top)).symm
    _ ≤ f.ker.map f := map_mono (hpre ▸ hcore)
    _ = ⊥ := (Subgroup.map_eq_bot_iff _).mpr le_rfl

/-- A proper local component inside either linear-three quotient has a
nontrivial image of its own two-core in the containing quotient. -/
theorem core_not_le_of_linear
    {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents P) (hK : K.IsCComponent) (hBK : B < K)
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^n))
    (hmodel : Source.IsSL (K ⧸ pCore 2 K) 3 (2^n) ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 (2^n)) :
    ¬ B.pCoreIn 2 ≤ K.pCoreIn 2 := by
  intro hcore
  obtain ⟨R,_,hR⟩ := SourceEmbeddings.exists_local_sylow_restriction P hB hBK.le hK.subnormal
  let D := B.subgroupOf K
  let d := subgroupOfEquivOfLe hBK.le
  let dq := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  have hdcore : (pCore 2 D).map D.subtype ≤ pCore 2 K := by
    rintro _ ⟨b,hb,rfl⟩
    have hb' : d b ∈ pCore 2 B := pCore_map_iso 2 d ▸ mem_map_of_mem d.toMonoidHom hb
    have hc := hcore (mem_map_of_mem B.subtype hb')
    change b.val ∈ ((pCore 2 K).map K.subtype).comap K.subtype at hc
    rw [comap_map_eq_self_of_injective K.subtype_injective] at hc
    exact hc
  have hmodelcore {A : Type} [Group A] [Finite A] (e : (K ⧸ pCore 2 K) ≃* A) :
      ∃ (S : Sylow 2 A) (C : Subgroup A), C ∈ localCComponents S ∧ C ≠ ⊤ ∧
        ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 (2^n) ∧ pCore 2 C = ⊥ := by
    let q := QuotientGroup.mk' (pCore 2 K)
    let f := e.toMonoidHom.comp q
    have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hk : f.ker = pCore 2 K := by
      ext x
      change e (q x) = 1 ↔ x ∈ pCore 2 K
      rw [e.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff x
    let := pCore_isNilpotent (p := 2) (G := K)
    let : Group.IsSolvable f.ker := hk ▸ (inferInstance : Group.IsSolvable (pCore 2 K))
    let S := R.mapSurjective hf
    let C := D.map f
    have ht : (⊤ : Subgroup K).IsCComponent := by
      simpa only [subgroupOf_self] using hK.subgroupOf le_rfl
    have hp : C ≠ ⊤ := by
      intro he
      have heq : D.map q = (⊤ : Subgroup K).map q := by
        apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
        rw [map_map,map_map,map_top_of_surjective f hf]
        exact he
      have heD := MovedMaximality.eq_of_twoCore_images_eq R hR ht le_top heq
      exact hBK.ne (le_antisymm hBK.le (subgroupOf_eq_top.mp heD))
    have hker : IsPGroup 2 (f.subgroupMap D).ker := by
      rw [ker_subgroupMap,hk]
      exact pCore_isPGroup.comap_subtype
    let a := (f.subgroupMap D).quotientPCoreEquivOfSurjective (f.subgroupMap_surjective D) hker
    refine ⟨S,C,localCComponents_map_of_solvable_ker hR f,hp,
      hm.of_mulEquiv (a.symm.trans dq),?_⟩
    apply image_core_eq_bot (f.subgroupMap D) (f.subgroupMap_surjective D) hker
    intro b hb
    apply Subtype.ext
    exact (show (b : K) ∈ f.ker from hk ▸ hdcore (mem_map_of_mem D.subtype hb))
  rcases hmodel with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    obtain ⟨S,C,hC,hp,hm,hz⟩ := hmodelcore e
    exact special_linear_local_core_ne_bot hF hn S C hC hp hm hz
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    obtain ⟨S,C,hC,hp,_,hz⟩ := hmodelcore e
    exact projective_local_core_ne_bot hF hn S C hC hp hz

private theorem core_le_of_proper_normal
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    [IsQuasisimple (G ⧸ pCore 2 G)]
    (N B : Subgroup G) [N.Normal] (hN : N ≠ ⊤)
    (hB : B.pCoreIn 2 ≤ N) : B.pCoreIn 2 ≤ pCore 2 G := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let : (N.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hNc : N.map q ≤ center (G ⧸ pCore 2 G) := by
    rcases IsQuasisimple.normal_le_center_or_eq_top (N.map q) with h | h
    · exact h
    · have hs : N ⊔ pCore 2 G = ⊤ := by
        have he := congrArg (comap q) h
        simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using he
      let : Group.IsNilpotent (G ⧸ N) :=
        (isPGroup_quotient_of_sup_eq_top N (pCore 2 G) pCore_isPGroup hs).isNilpotent
      exact (hN (top_unique (by simpa only [solvableResidual_eq_top] using
        solvableResidual_le_of_solvable_quotient N))).elim
  let U := (B.pCoreIn 2).map q
  have hUc : U ≤ center (G ⧸ pCore 2 G) := (map_mono hB).trans hNc
  let : U.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hUc hx) g,mul_inv_cancel_right]
    exact hx⟩
  have hU : U ≤ pCore 2 (G ⧸ pCore 2 G) :=
    le_sSup ⟨inferInstance,(isPGroup_pCoreIn 2 B).map q⟩
  rw [pCore_quotient_pCore_eq_bot 2] at hU
  simpa only [q,MonoidHom.comap_bot,QuotientGroup.ker_mk'] using
    map_le_iff_le_comap.mp hU

/-- A noncentral component action with the smaller two-core in its kernel
forces that two-core into the containing component's own two-core. -/
theorem core_le_of_centralizing
    {G : Type*} [Group G] [Finite G] {B K U : Subgroup G}
    (hK : K ≤ normalizer (U : Set G)) (hBK : B ≤ K)
    [Group.IsPerfect K] [IsQuasisimple (K ⧸ pCore 2 K)]
    (hB : B.pCoreIn 2 ≤ centralizer (U : Set G))
    (hnon : ¬ B ≤ centralizer (U : Set G)) : B.pCoreIn 2 ≤ K.pCoreIn 2 := by
  let N := (centralizer (U : Set G)).subgroupOf K
  let : N.Normal := ⟨fun x hx k =>
    (normalizer_le_normalizer_centralizer _ (hK k.property) (x : G)).mp hx⟩
  have hn : N ≠ ⊤ := by
    intro h
    apply hnon
    intro b hb
    exact (show (⟨b,hBK hb⟩ : K) ∈ N from h.symm ▸ mem_top _)
  have hcore := core_le_of_proper_normal N (B.subgroupOf K) hn (by
    rw [pCoreIn_subgroupOf 2 B K hBK]
    exact comap_mono hB)
  have hh := map_mono (f := K.subtype) hcore
  rwa [pCoreIn_subgroupOf 2 B K hBK,
    map_subgroupOf_eq_of_le ((B.pCoreIn_le 2).trans hBK)] at hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.SecondLinear
