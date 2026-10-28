module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ChiZeroHalfSylow
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Solvable
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.SymplecticFour.Blocks
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.GroupTheory.SylowIndexTwoExtension
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.SylowKernelCore
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ResidualMarks

/-!
# Conditional marked recognition of the single symplectic component

Assume a literal component is isomorphic to Sp₄ over a nonbinary even field.
A natural L₂ block normalized by half an ambient Sylow lies in the normalizer
of its nontrivial two-core. Symplectic two-local coverage puts that normalizer
inside a parabolic. Half-Sylow χ₀ rigidity identifies the original block with
the parabolic's actual solvable residual. The intrinsic module cardinality
then identifies the source exponent with the field degree.

Sylow conjugacy inside the recognized residual aligns the original block
Sylow with the standard ambient Sylow without changing the residual mark.
The same equivalence transports every actor: diagram preservation is exactly
preservation of the literal block, and moving its actual two-core sends it
to the opposite local conjugacy class. No full ambient Sylow assumption on
the block Sylow is used.

This supplies the marked geometry in Aschbacher–Smith 2.4.23(5), printed
pp.537–538. Selection of the direct Sp₄ model from the full Theorem C
catalogue remains a separate premise; an isomorphism only modulo the center
is not substituted for the displayed component isomorphism.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single.SymplecticRecognition
variable {G : Type*} [Group G] [Finite G]

private theorem local_map_equiv {A S : Subgroup G}
    (hA : A ∈ ChapterA.Section03.localCComponents S)
    {H : Type*} [Group H] (e : G ≃* H) :
    A.map e.toMonoidHom ∈ ChapterA.Section03.localCComponents (S.map e.toMonoidHom) := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  exact Chapter1.Section02.localCComponents_map_of_solvable_ker hA e.toMonoidHom

omit [Finite G] in
private theorem local_perfect {L S : Subgroup G}
    (hL : L ∈ ChapterA.Section03.localCComponents S) : Group.IsPerfect L := by
  let := hL.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show L ≤ L ⊔ S from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show L ≤ L ⊔ S from le_sup_left)).surjective

private theorem natural_isCComponent {L : Subgroup G} {n : ℕ}
    (hL : L.IsSubnormal) (hn : ChapterC.IsL2EvenBlock L n) : L.IsCComponent := by
  rcases hn.2.1.quotient with hq | h3
  · let := hq
    exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient hL hn.2.1.twoPerfect
  · let : IsCyclic (L ⧸ pCore 2 L) := isCyclic_of_prime_card h3
    let : CommGroup (L ⧸ pCore 2 L) := IsMulCommutative.instCommGroup
    let : Group.IsNilpotent (pCore 2 L) := pCore_isPGroup.isNilpotent
    let : Group.IsSolvable L := (Group.isSolvable_iff_subgroup_quotient (pCore 2 L)).mpr
      ⟨inferInstance, inferInstance⟩
    exact hn.not_solvable.elim

private theorem exponent_eq {L : Type*} [Group L] {n m : ℕ}
    (hn : ChapterC.IsL2EvenBlock L n) (hm : ChapterC.IsL2EvenBlock L m) : n = m := by
  have hp := hn.module_card.symm.trans hm.module_card
  have he := (Nat.pow_right_injective (by decide : 1 < (2 : ℕ))) hp
  omega

omit [Finite G] in
private theorem residual_model {R D : Subgroup G} {m : ℕ}
    (hD : (solvableResidual R).map R.subtype = D)
    (hm : ChapterC.IsL2EvenBlock D m) :
    ChapterC.IsL2EvenBlock (solvableResidual R) m := by
  let e := ((solvableResidual R).equivMapOfInjective R.subtype R.subtype_injective).trans
    (MulEquiv.subgroupCongr hD)
  exact hm.of_mulEquiv e.symm


omit [Finite G] in
private theorem card_mul_relIndex {A B : Subgroup G} (h : A ≤ B) :
    Nat.card A * A.relIndex B = Nat.card B := by
  simpa only [relIndex_bot_left] using relIndex_mul_relIndex ⊥ A B bot_le h

private theorem half_sylow_restrict (P : Sylow 2 G) {S Q : Subgroup G}
    (hSP : S ≤ P) (hi : S.relIndex P ≤ 2) (hSQ : S ≤ Q) :
    ∃ T : Sylow 2 Q, S.subgroupOf Q ≤ T ∧ (S.subgroupOf Q).relIndex T ≤ 2 := by
  obtain ⟨T,hT⟩ := ((P.isPGroup'.to_le hSP).comap_subtype (K := Q)).exists_le_sylow
  refine ⟨T,hT,?_⟩
  have hcard := card_le_sylow_two (T.isPGroup'.map Q.subtype) P
  rw [card_map_of_injective Q.subtype_injective] at hcard
  have hS := Nat.card_congr (subgroupOfEquivOfLe hSQ).toEquiv
  have hp := card_mul_relIndex hSP
  have ht := card_mul_relIndex hT
  change Nat.card (S.subgroupOf Q) * (S.subgroupOf Q).relIndex T = Nat.card T at ht
  rw [hS] at ht
  have hpos : 0 < Nat.card S := Nat.card_pos
  nlinarith

/-- A half-Sylow local natural block inside a natural parabolic residual
is the whole residual. -/
theorem eq_residual_of_half_sylow (P : Sylow 2 G) {S L Q : Subgroup G} {m : ℕ}
    (hSP : S ≤ P) (hi : S.relIndex P ≤ 2) (hSQ : S ≤ Q) (hLQ : L ≤ Q)
    (hlocal : L ∈ ChapterA.Section03.localCComponents S)
    (hm : ChapterC.IsL2EvenBlock (solvableResidual Q) m) :
    L = (solvableResidual Q).map Q.subtype := by
  obtain ⟨T,hST,hindex⟩ := half_sylow_restrict P hSP hi hSQ
  have hc := ChapterA.Section03.SourceEmbeddings.local_restrict hlocal hLQ
  let := local_perfect hc
  have he := ChapterA.Section03.SourceEmbeddings.eq_of_chiZero_containing_component_half_sylow
    T hST hindex hc
    (natural_isCComponent (inferInstance : (solvableResidual Q).Normal).isSubnormal hm)
    (le_solvableResidual_of_isPerfect (L.subgroupOf Q)) (Or.inl ⟨m,hm⟩)
  simpa only [map_subgroupOf_eq_of_le hLQ] using congrArg (fun D => D.map Q.subtype) he

variable {F : Type} [Field F] [Finite F] [CharP F 2]

/-- A local natural block normalized by half a Sylow in Sp₄ is a conjugate
of an actual standard parabolic residual, with the same field exponent. -/
theorem model_residual_recognition {m n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (P : Sylow 2 (Sp F)) (S L : Subgroup (Sp F))
    (hSP : S ≤ P) (hi : S.relIndex P ≤ 2)
    (hlocal : L ∈ ChapterA.Section03.localCComponents S)
    (hSL : S ≤ normalizer (L : Set (Sp F))) (hm : ChapterC.IsL2EvenBlock L m) :
    m = n ∧ ∃ g : Sp F, L.map (MulAut.conj g).toMonoidHom = pointLocal ∨
      L.map (MulAut.conj g).toMonoidHom = planeLocal := by
  let U := (pCore 2 L).map L.subtype
  have hU : U ≠ ⊥ := fun h => hm.2.1.core_ne_bot
    (((pCore 2 L).map_eq_bot_iff_of_injective L.subtype_injective).mp h)
  have hLN : L ≤ normalizer (U : Set (Sp F)) :=
    L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hSN : S ≤ normalizer (U : Set (Sp F)) :=
    hSL.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  obtain ⟨g,hg⟩ := twoLocal_parabolic_cover_of_charTwo (normalizer (U : Set (Sp F)))
    ⟨U,hU,pCore_isPGroup.map L.subtype,rfl⟩
  let a := MulAut.conj g
  let P' := P.mapSurjective (f := a.toMonoidHom) a.surjective
  have hSP' : S.map a.toMonoidHom ≤ P' := map_mono hSP
  have hi' : (S.map a.toMonoidHom).relIndex P' ≤ 2 := by
    change (S.map a.toMonoidHom).relIndex ((P : Subgroup (Sp F)).map a.toMonoidHom) ≤ 2
    simpa only [relIndex_map_map_of_injective (f := a.toMonoidHom) _ _ a.injective] using hi
  have hc := local_map_equiv hlocal a
  have hm' := hm.of_mulEquiv (L.equivMapOfInjective a.toMonoidHom a.injective)
  have aux (Q D : Subgroup (Sp F))
      (hQ : (normalizer (U : Set (Sp F))).map a.toMonoidHom ≤ Q)
      (hr : (solvableResidual Q).map Q.subtype = D)
      (hd : ChapterC.IsL2EvenBlock D n) :
      L.map a.toMonoidHom = D ∧ m = n := by
    have he := eq_residual_of_half_sylow P' hSP' hi'
      ((map_mono hSN).trans hQ) ((map_mono hLN).trans hQ) hc (residual_model hr hd)
    rw [hr] at he
    refine ⟨he,?_⟩
    rw [he] at hm'
    exact exponent_eq hm' hd
  rcases hg with hp | hp
  · have hh := aux _ _ hp (pointParabolic_solvableResidual_eq hF hn)
      (ChapterF.GreenBook.LieModels.SymplecticFour.pointLocal_isL2EvenBlock hF hn)
    exact ⟨hh.2,g,Or.inl hh.1⟩
  · have hh := aux _ _ hp (planeParabolic_solvableResidual_eq hF hn)
      (ChapterF.GreenBook.LieModels.SymplecticFour.planeLocal_isL2EvenBlock hF hn)
    exact ⟨hh.2,g,Or.inr hh.1⟩

/-- Recognition through the supplied isomorphism keeps the literal block
image; only an inner adjustment of the model coordinates is used. -/
theorem residual_recognition {m n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (e : G ≃* Sp F) (P : Sylow 2 G) (S L : Subgroup G)
    (hSP : S ≤ P) (hi : S.relIndex P ≤ 2)
    (hlocal : L ∈ ChapterA.Section03.localCComponents S)
    (hSL : S ≤ normalizer (L : Set G)) (hm : ChapterC.IsL2EvenBlock L m) :
    m = n ∧ ∃ f : G ≃* Sp F,
      L.map f.toMonoidHom = pointLocal ∨ L.map f.toMonoidHom = planeLocal := by
  have hi' : (S.map e.toMonoidHom).relIndex ((P : Subgroup G).map e.toMonoidHom) ≤ 2 := by
    rwa [relIndex_map_map_of_injective _ _ e.injective]
  have hs' : S.map e.toMonoidHom ≤ normalizer (L.map e.toMonoidHom : Set (Sp F)) := by
    rw [← map_normalizer_eq_of_bijective L e.bijective]
    exact map_mono hSL
  obtain ⟨he,g,hg⟩ := model_residual_recognition hF hn (P.mapSurjective e.surjective)
    _ _ (map_mono hSP) hi' (local_map_equiv hlocal e) hs'
    (hm.of_mulEquiv (L.equivMapOfInjective e.toMonoidHom e.injective))
  refine ⟨he,e.trans (MulAut.conj g),?_⟩
  have hh : (e.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := rfl
  rw [hh, ← map_map]
  exact hg

private theorem align_sylow {H : Type*} [Group H] [Finite H]
    (e : G ≃* H) (L : Subgroup G) (D : Subgroup H)
    (hLD : L.map e.toMonoidHom = D) (R : Sylow 2 L) (V : Sylow 2 H) (hVD : (V : Subgroup H) ≤ D) :
    ∃ f : G ≃* H, L.map f.toMonoidHom = D ∧
      ((R : Subgroup L).map L.subtype).map f.toMonoidHom = V := by
  let eL := (L.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hLD)
  let R' := R.mapSurjective (f := eL.toMonoidHom) eL.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq D R' (V.subtype hVD)
  have hg' : (R' : Subgroup D).map (MulAut.conj g).toMonoidHom = (V : Subgroup H).subgroupOf D :=
    congrArg Sylow.toSubgroup hg
  refine ⟨e.trans (MulAut.conj (g : H)),?_,?_⟩
  · change L.map ((MulAut.conj (g : H)).toMonoidHom.comp e.toMonoidHom) = D
    rw [← map_map,hLD]
    exact mem_normalizer_iff_map_conj_eq.mp (D.le_normalizer g.property)
  · have hh := congrArg (fun W : Subgroup D => W.map D.subtype) hg'
    rw [map_subgroupOf_eq_of_le hVD] at hh
    change (((R : Subgroup L).map eL.toMonoidHom).map (MulAut.conj g).toMonoidHom).map D.subtype = _ at hh
    rw [map_map] at hh
    rw [map_map] at hh
    rw [map_map]
    convert hh using 1
    congr 1

/-- The actual Sylow of the recognized block can be aligned with the
standard ambient Sylow while retaining its point or plane residual mark. -/
theorem marked_residual_recognition {m n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (e : G ≃* Sp F) (P : Sylow 2 G) (S L : Subgroup G)
    (hSP : S ≤ P) (hi : S.relIndex P ≤ 2)
    (hlocal : L ∈ ChapterA.Section03.localCComponents S)
    (hSL : S ≤ normalizer (L : Set G)) (hm : ChapterC.IsL2EvenBlock L m)
    (R : Sylow 2 L) :
    m = n ∧ ∃ f : G ≃* Sp F,
      ((R : Subgroup L).map L.subtype).map f.toMonoidHom = unipotent ∧
      (L.map f.toMonoidHom = pointLocal ∨ L.map f.toMonoidHom = planeLocal) := by
  obtain ⟨he,f,hf⟩ := residual_recognition hF hn e P S L hSP hi hlocal hSL hm
  refine ⟨he,?_⟩
  rcases hf with hp | hp
  · obtain ⟨f',hf',hR⟩ := align_sylow f L pointLocal hp R (unipotentSylow hF hn.le)
      (show unipotent ≤ pointLocal from inf_le_left)
    exact ⟨f',hR,Or.inl hf'⟩
  · obtain ⟨f',hf',hR⟩ := align_sylow f L planeLocal hp R (unipotentSylow hF hn.le)
      (show unipotent ≤ planeLocal from inf_le_right)
    exact ⟨f',hR,Or.inr hf'⟩

open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms

omit [Finite G] [Finite F] [CharP F 2] in
private theorem map_congr_aut (f : G ≃* Sp F) (a : MulAut G) (D : Subgroup G) :
    (D.map f.toMonoidHom).map (MulAut.congr f a).toMonoidHom =
      (D.map a.toMonoidHom).map f.toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  ext g : 1
  change f (a (f.symm (f g))) = f (a g)
  rw [f.symm_apply_apply]

omit [Finite G] in
/-- Every actor preserving the marked Sylow preserves the diagram exactly
when it preserves the literal recognized local factor. -/
theorem preservesDiagram_iff_block_map {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (f : G ≃* Sp F) (L V : Subgroup G)
    (hL : L.map f.toMonoidHom = pointLocal ∨ L.map f.toMonoidHom = planeLocal)
    (hV : V.map f.toMonoidHom = unipotent)
    (a : MulAut G) (ha : V.map a.toMonoidHom = V) :
    PreservesDiagram (MulAut.congr f a) ↔ L.map a.toMonoidHom = L := by
  let b := MulAut.congr f a
  have hU : unipotent.map b.toMonoidHom = unipotent := by
    rw [← hV,map_congr_aut,ha]
  have hfix : L.map a.toMonoidHom = L ↔
      (L.map f.toMonoidHom).map b.toMonoidHom = L.map f.toMonoidHom := by
    rw [map_congr_aut]
    constructor
    · exact congrArg (fun D : Subgroup G => D.map f.toMonoidHom)
    · intro he
      exact map_injective f.injective he
  rw [hfix]
  exact preservesDiagram_iff_local_map hF hn b hU _ hL

omit [Finite G] in
/-- Moving the literal two-core of the local block detects diagram movement;
the actor need not be an involution. -/
theorem not_preservesDiagram_of_core_moved {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (f : G ≃* Sp F) (L V : Subgroup G)
    (hL : L.map f.toMonoidHom = pointLocal ∨ L.map f.toMonoidHom = planeLocal)
    (hV : V.map f.toMonoidHom = unipotent)
    (a : MulAut G) (ha : V.map a.toMonoidHom = V)
    (hmove : (L.pCoreIn 2).map a.toMonoidHom ≠ L.pCoreIn 2) :
    ¬ PreservesDiagram (MulAut.congr f a) := by
  intro hb
  have he := (preservesDiagram_iff_block_map hF hn f L V hL hV a ha).mp hb
  apply hmove
  rw [map_pCoreIn_of_injective 2 L a.toMonoidHom a.injective,he]

omit [Finite G] in
/-- The source actor moving the original local core sends the recognized
residual into the opposite diagram class, with the same component coordinates. -/
theorem core_moving_actor_opposite_class {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (f : G ≃* Sp F) (L V : Subgroup G)
    (hL : L.map f.toMonoidHom = pointLocal ∨ L.map f.toMonoidHom = planeLocal)
    (hV : V.map f.toMonoidHom = unipotent)
    (a : MulAut G) (ha : V.map a.toMonoidHom = V)
    (hmove : (L.pCoreIn 2).map a.toMonoidHom ≠ L.pCoreIn 2) :
    (L.map f.toMonoidHom = pointLocal ∧ ∃ g : Sp F,
      (L.map a.toMonoidHom).map f.toMonoidHom = planeLocal.map (MulAut.conj g).toMonoidHom) ∨
    (L.map f.toMonoidHom = planeLocal ∧ ∃ g : Sp F,
      (L.map a.toMonoidHom).map f.toMonoidHom = pointLocal.map (MulAut.conj g).toMonoidHom) := by
  have hb := not_preservesDiagram_of_core_moved hF hn f L V hL hV a ha hmove
  obtain ⟨hp,hl⟩ := moving_local_opposite_classes hF hn (MulAut.congr f a) hb
  rcases hL with hL | hL
  · refine Or.inl ⟨hL,?_⟩
    rw [← map_congr_aut,hL]
    exact hp
  · refine Or.inr ⟨hL,?_⟩
    rw [← map_congr_aut,hL]
    exact hl

/-- The source half-Sylow block has one uniform marked realization, valid
for every actor on the component preserving the original local Sylow. -/
theorem marked_recognition_with_actors {m n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (e : G ≃* Sp F) (P : Sylow 2 G) (S L : Subgroup G)
    (hSP : S ≤ P) (hi : S.relIndex P ≤ 2)
    (hlocal : L ∈ ChapterA.Section03.localCComponents S)
    (hSL : S ≤ normalizer (L : Set G)) (hm : ChapterC.IsL2EvenBlock L m)
    (R : Sylow 2 L) :
    m = n ∧ ∃ f : G ≃* Sp F,
      ((R : Subgroup L).map L.subtype).map f.toMonoidHom = unipotent ∧
      (L.map f.toMonoidHom = pointLocal ∨ L.map f.toMonoidHom = planeLocal) ∧
      ∀ a : MulAut G,
        ((R : Subgroup L).map L.subtype).map a.toMonoidHom = (R : Subgroup L).map L.subtype →
        (PreservesDiagram (MulAut.congr f a) ↔ L.map a.toMonoidHom = L) ∧
        ((L.pCoreIn 2).map a.toMonoidHom ≠ L.pCoreIn 2 →
          ¬ PreservesDiagram (MulAut.congr f a)) := by
  obtain ⟨he,f,hV,hL⟩ := marked_residual_recognition hF hn e P S L hSP hi hlocal hSL hm R
  refine ⟨he,f,hV,hL,fun a ha => ?_⟩
  exact ⟨preservesDiagram_iff_block_map hF hn f L _ hL hV a ha,
    not_preservesDiagram_of_core_moved hF hn f L _ hL hV a ha⟩

end CFSG.Quasithin.Chapter2.LinearShadows.Single.SymplecticRecognition