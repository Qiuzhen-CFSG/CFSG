module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SpecialLinearThreeLocalQuotient
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import Theory.SpecificGroups.SymplecticFour.Sylow.Normalizer
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Normalizers
public import Theory.GroupTheory.PResidual.NormalizedComparison
public import Theory.SpecificGroups.PSL3.BorelTwoParabolics
public import Theory.GroupTheory.NormalizedSylowTransitivity

/-!
# The two normalized proper locals in the binary classical rank-two groups

For PSL₃ and Sp₄, actual local placement gives the two parabolic residuals
up to conjugacy. Sylow conjugacy inside their normalizers removes that
conjugacy when the standard Sylow normalizes the local subgroup. Thus any
fixed Sylow normalizes at most two proper local components.

Perfectness reflects containment through the central projection SL₃ → PSL₃
and through a two-group kernel inside the fixed Sylow. The scalar kernel
is retained. An ambient actor preserving the same Sylow therefore has
normalizer index at most two on any such proper local component.

Source: Aschbacher–Smith A.3.12 and the classical common-component step of
5.2.2, printed pp.47–48 and 648, refs/quasithin.pdf. The imported matrix
models and local placement proofs retain their native/ATLAS attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ClassicalLocalPairs

private theorem normalized_conjugate_eq {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (C : Subgroup G)
    (hN : normalizer (S : Set G) ≤ normalizer (C : Set G))
    (g : G) (hg : (S : Subgroup G) ≤ normalizer (C.conjBy g : Set G)) : C.conjBy g = C := by
  have hSC : (S : Subgroup G) ≤ normalizer (C : Set G) :=
    (S : Subgroup G).le_normalizer.trans hN
  obtain ⟨n,hn,he⟩ := NormalizedSylowTransitivity.conjugator C S (S.subtype hSC)
    S.isPGroup' (fun a ha => by
      change (S : Subgroup G).conjBy a ≤ ((S : Subgroup G).subgroupOf _).map _ at ha
      rw [map_subgroupOf_eq_of_le hSC] at ha
      exact eq_of_le_of_card_ge ha (by rw [conjBy,card_map_of_injective (MulAut.conj a).injective])) g hg
  exact he.symm.trans (mem_normalizer_iff_map_conj_eq.mp (hN hn))

private theorem eq_of_normalized_conjugate {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {B C : Subgroup G}
    (hN : normalizer (S : Set G) ≤ normalizer (C : Set G))
    (hB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (g : G) (hg : B.map (MulAut.conj g).toMonoidHom = C) : B = C := by
  have he : C.conjBy g⁻¹ = B := by
    rw [←hg]
    change (B.conjBy g).conjBy g⁻¹ = B
    rw [conjBy_conjBy,inv_mul_cancel,conjBy_one]
  exact he.symm.trans (normalized_conjugate_eq S C hN g⁻¹ (he ▸ hB))

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
open Matrix.PSL3.LinearThree

private theorem linear_standard_pair {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2^f)
    (B : Subgroup PSL(3,F))
    (hl : B ∈ localCComponents (unipotent F))
    (hn : unipotent F ≤ normalizer (B : Set PSL(3,F))) (hp : B ≠ ⊤) :
    B = pointLocal F ∨ B = lineLocal F := by
  let S := unipotentSylow F (by omega : 0 < f) hF
  have hlarge : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ f)
  have hNp : normalizer (S : Set PSL(3,F)) ≤ normalizer (pointLocal F : Set PSL(3,F)) := by
    change normalizer (unipotent F : Set PSL(3,F)) ≤ _
    rw [normalizer_unipotent F (by omega) hF,←ParabolicResiduals.pointParabolic_residual F hlarge]
    exact ((projective_parabolics_inf F) ▸ inf_le_left).trans
      ((pointParabolic F).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (solvableResidual _)))
  have hNl : normalizer (S : Set PSL(3,F)) ≤ normalizer (lineLocal F : Set PSL(3,F)) := by
    change normalizer (unipotent F : Set PSL(3,F)) ≤ _
    rw [normalizer_unipotent F (by omega) hF,←ParabolicResiduals.lineParabolic_residual F hlarge]
    exact ((projective_parabolics_inf F) ▸ inf_le_right).trans
      ((lineParabolic F).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (solvableResidual _)))
  obtain ⟨g,hg | hg⟩ := FiveLocalFF.linear_three_local_placement hF hf S B hl hp
  · exact .inl (eq_of_normalized_conjugate S hNp hn g hg)
  · exact .inr (eq_of_normalized_conjugate S hNl hn g hg)


open Theory.SpecificGroups.SymplecticFour in
private theorem symplectic_standard_pair {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2^f)
    (B : Subgroup (Sp F))
    (hl : B ∈ localCComponents (Theory.SpecificGroups.SymplecticFour.unipotent (F := F)))
    (hn : Theory.SpecificGroups.SymplecticFour.unipotent ≤ normalizer (B : Set (Sp F))) (hp : B ≠ ⊤) :
    B = Theory.SpecificGroups.SymplecticFour.pointLocal ∨ B = Theory.SpecificGroups.SymplecticFour.planeLocal := by
  let S := Theory.SpecificGroups.SymplecticFour.unipotentSylow hF (by omega : 1 ≤ f)
  have hNp : normalizer (S : Set (Sp F)) ≤ normalizer (Theory.SpecificGroups.SymplecticFour.pointLocal (F := F) : Set (Sp F)) := by
    change normalizer (Theory.SpecificGroups.SymplecticFour.unipotent (F := F) : Set (Sp F)) ≤ _
    rw [←Theory.SpecificGroups.SymplecticFour.borel_eq_normalizer_unipotent]
    exact inf_le_left.trans ((normal_subgroupOf_iff_le_normalizer Theory.SpecificGroups.SymplecticFour.pointLocal_le).mp inferInstance)
  have hNl : normalizer (S : Set (Sp F)) ≤ normalizer (Theory.SpecificGroups.SymplecticFour.planeLocal (F := F) : Set (Sp F)) := by
    change normalizer (Theory.SpecificGroups.SymplecticFour.unipotent (F := F) : Set (Sp F)) ≤ _
    rw [←Theory.SpecificGroups.SymplecticFour.borel_eq_normalizer_unipotent]
    exact inf_le_right.trans ((normal_subgroupOf_iff_le_normalizer Theory.SpecificGroups.SymplecticFour.planeLocal_le).mp inferInstance)
  obtain ⟨g,hg | hg⟩ := FiveLocalFF.symplectic_local_placement hF hf S B hl hp
  · exact .inl (eq_of_normalized_conjugate S hNp hn g hg)
  · exact .inr (eq_of_normalized_conjugate S hNl hn g hg)

variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

abbrev NormalizedProperLocals (S : Subgroup G) :=
  {B : Subgroup G // B ∈ localCComponents S ∧ S ≤ normalizer (B : Set G) ∧ B ≠ ⊤}

omit [Finite G] in
private theorem local_perfect {S B : Subgroup G} (hl : B ∈ localCComponents S) :
    Group.IsPerfect B := by
  let := hl.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective

omit [Finite G] in
private theorem card_le_of_pair (S : Subgroup G) (C D : Subgroup G)
    (h : ∀ B : NormalizedProperLocals S, B.val = C ∨ B.val = D) :
    Nat.card (NormalizedProperLocals S) ≤ 2 := by
  classical
  let j : NormalizedProperLocals S → Bool := fun B => decide (B.val = C)
  have hj : Function.Injective j := by
    intro B E he
    apply Subtype.ext
    by_cases hb : B.val = C
    · have hE : E.val = C := of_decide_eq_true (by simpa [j,hb] using he.symm)
      exact hb.trans hE.symm
    · have hd := (h B).resolve_left hb
      have hE : E.val ≠ C := of_decide_eq_false (by simpa [j,hb] using he.symm)
      exact hd.trans ((h E).resolve_left hE).symm
  exact (Nat.card_le_card_of_injective j hj).trans_eq (by simp [Nat.card_eq_fintype_card])

theorem card_le_of_equiv (e : G ≃* Q) (S : Subgroup G) :
    Nat.card (NormalizedProperLocals S) ≤ Nat.card (NormalizedProperLocals (S.map e.toMonoidHom)) := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  let j : NormalizedProperLocals S → NormalizedProperLocals (S.map e.toMonoidHom) := fun B =>
    ⟨B.val.map e.toMonoidHom,
      Chapter1.Section02.localCComponents_map_of_solvable_ker B.property.1 e.toMonoidHom,
      (map_mono B.property.2.1).trans (B.val.le_normalizer_map e.toMonoidHom),
      fun ht => B.property.2.2 ((map_injective e.injective) (ht.trans (map_top_of_surjective _ e.surjective).symm))⟩
  exact Nat.card_le_card_of_injective j (fun B C he => Subtype.ext
    ((map_injective e.injective) (congrArg Subtype.val he)))

/-- A fixed Sylow normalizes at most two proper local components in binary PSL₃. -/
theorem linear_card {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2^f)
    (S : Sylow 2 PSL(3,F)) : Nat.card (NormalizedProperLocals (S : Subgroup PSL(3,F))) ≤ 2 := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) S (unipotentSylow F (by omega) hF)
  apply (card_le_of_equiv (MulAut.conj g) (S : Subgroup PSL(3,F))).trans
  have hS : (S : Subgroup PSL(3,F)).map (MulAut.conj g).toMonoidHom = unipotent F :=
    congrArg Sylow.toSubgroup hg
  rw [hS]
  exact card_le_of_pair _ _ _ (fun B => linear_standard_pair hf hF B.val
    B.property.1 B.property.2.1 B.property.2.2)

open Theory.SpecificGroups.SymplecticFour in
/-- A fixed Sylow normalizes at most two proper local components in binary Sp₄. -/
theorem symplectic_card {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2^f)
    (S : Sylow 2 (Sp F)) : Nat.card (NormalizedProperLocals (S : Subgroup (Sp F))) ≤ 2 := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp F) S (unipotentSylow hF (by omega))
  apply (card_le_of_equiv (MulAut.conj g) (S : Subgroup (Sp F))).trans
  have hS : (S : Subgroup (Sp F)).map (MulAut.conj g).toMonoidHom = Theory.SpecificGroups.SymplecticFour.unipotent :=
    congrArg Sylow.toSubgroup hg
  rw [hS]
  exact card_le_of_pair _ _ _ (fun B => symplectic_standard_pair hf hF B.val
    B.property.1 B.property.2.1 B.property.2.2)


private theorem perfect_twoPerfect (Y : Type*) [Group Y] [Finite Y] [Group.IsPerfect Y] :
    IsPPerfect 2 Y := by
  intro N hn hp
  let := hn
  by_contra he
  let : Nontrivial (Y ⧸ N) := QuotientGroup.nontrivial_iff.mpr he
  let : Group.IsPerfect (Y ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  exact Group.IsPerfect.not_isNilpotent (Y ⧸ N) hp.isNilpotent

/-- A two-group kernel inside the fixed Sylow retains the bound on normalized
proper local components. Perfectness prevents a proper local from covering. -/
theorem two_kernel_card [Group.IsPerfect G] (S : Sylow 2 G)
    (q : G →* Q) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker) :
    Nat.card (NormalizedProperLocals (S : Subgroup G)) ≤
      Nat.card (NormalizedProperLocals (S.mapSurjective hq : Subgroup Q)) := by
  let : Group.IsNilpotent q.ker := hk.isNilpotent
  let : Group.IsSolvable q.ker := inferInstance
  have hker := hk.le_sylow_of_normal S
  have hreflect (B C : NormalizedProperLocals (S : Subgroup G))
      (he : B.val.map q ≤ C.val.map q) : B.val ≤ C.val := by
    let := local_perfect B.property.1
    exact isPPerfect_le_of_map_le_of_kernel_normalizes q B.val C.val
      (perfect_twoPerfect B.val) hk (hker.trans C.property.2.1) he
  have hproper (B : NormalizedProperLocals (S : Subgroup G)) : B.val.map q ≠ ⊤ := by
    intro he
    apply B.property.2.2
    apply top_unique
    apply isPPerfect_le_of_map_le_of_kernel_normalizes q ⊤ B.val
      (perfect_twoPerfect (⊤ : Subgroup G)) hk (hker.trans B.property.2.1)
    rw [he]
    exact le_top
  let j : NormalizedProperLocals (S : Subgroup G) →
      NormalizedProperLocals (S.mapSurjective hq : Subgroup Q) := fun B =>
    ⟨B.val.map q,Chapter1.Section02.localCComponents_map_of_solvable_ker B.property.1 q,
      (map_mono B.property.2.1).trans (B.val.le_normalizer_map q),hproper B⟩
  exact Nat.card_le_card_of_injective j (fun B C he => Subtype.ext
    (le_antisymm (hreflect B C (congrArg Subtype.val he).le)
      (hreflect C B (congrArg Subtype.val he).ge)))

private theorem central_kernel_card [Group.IsPerfect G] (S : Sylow 2 G)
    (q : G →* Q) (hq : Function.Surjective q) (hk : q.ker ≤ center G)
    [Group.IsSolvable q.ker] :
    Nat.card (NormalizedProperLocals (S : Subgroup G)) ≤
      Nat.card (NormalizedProperLocals (S.mapSurjective hq : Subgroup Q)) := by
  have hreflect (B C : NormalizedProperLocals (S : Subgroup G))
      (he : B.val.map q ≤ C.val.map q) : B.val ≤ C.val := by
    let := local_perfect B.property.1
    exact le_of_map_le_of_perfect q hk B.val C.val he
  have hproper (B : NormalizedProperLocals (S : Subgroup G)) : B.val.map q ≠ ⊤ := by
    intro he
    apply B.property.2.2
    apply top_unique
    apply le_of_map_le_of_perfect q hk ⊤ B.val
    rw [he]
    exact le_top
  let j : NormalizedProperLocals (S : Subgroup G) →
      NormalizedProperLocals (S.mapSurjective hq : Subgroup Q) := fun B =>
    ⟨B.val.map q,Chapter1.Section02.localCComponents_map_of_solvable_ker B.property.1 q,
      (map_mono B.property.2.1).trans (B.val.le_normalizer_map q),hproper B⟩
  exact Nat.card_le_card_of_injective j (fun B C he => Subtype.ext
    (le_antisymm (hreflect B C (congrArg Subtype.val he).le)
      (hreflect C B (congrArg Subtype.val he).ge)))

/-- The same two-local bound holds for SL₃, retaining its scalar kernel. -/
theorem specialLinear_card {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2^f)
    (S : Sylow 2 SL(3,F)) : Nat.card (NormalizedProperLocals (S : Subgroup SL(3,F))) ≤ 2 := by
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  exact (central_kernel_card S (Matrix.PSL3.projection F) (Matrix.PSL3.projection_surjective F)
    (Matrix.PSL3.projection_ker F).le).trans
    (linear_card hf hF (S.mapSurjective (Matrix.PSL3.projection_surjective F)))


/-- An actor preserving the full Sylow of K has at most two conjugates of a
normalized proper local component whenever K has the two-local bound. -/
theorem normalizer_relIndex_le_two
    (K N R : Subgroup G) (S : Sylow 2 K)
    (hRK : R ≤ K) (hNK : N ≤ normalizer (K : Set G))
    (hNS : N ≤ normalizer (((S : Subgroup K).map K.subtype : Subgroup G) : Set G))
    (hl : R.subgroupOf K ∈ localCComponents (S : Subgroup K))
    (hn : (S : Subgroup K) ≤ normalizer (R.subgroupOf K : Set K))
    (hp : R.subgroupOf K ≠ ⊤)
    (hc : Nat.card (NormalizedProperLocals (S : Subgroup K)) ≤ 2) :
    (normalizer (R : Set G)).relIndex N ≤ 2 := by
  let a : N →* MulAut K := K.normalizerMonoidHom.comp (inclusion hNK)
  let _ : MulAction N (Subgroup K) := {
    smul := fun n B => B.map (a n).toMonoidHom
    one_smul := fun B => by
      change B.map (a 1).toMonoidHom = B
      rw [map_one]
      exact map_id B
    mul_smul := fun n m B => by
      change B.map (a (n*m)).toMonoidHom = (B.map (a m).toMonoidHom).map (a n).toMonoidHom
      rw [map_mul,map_map]
      rfl }
  have hformula (n : N) (B : Subgroup K) :
      (B.map (a n).toMonoidHom).map K.subtype =
        (B.map K.subtype).map (MulAut.conj (n : G)).toMonoidHom := by
    rw [map_map,map_map]
    rfl
  have hS (n : N) : (S : Subgroup K).map (a n).toMonoidHom = S := by
    apply map_injective K.subtype_injective
    rw [hformula]
    exact mem_normalizer_iff_map_conj_eq.mp (hNS n.property)
  let B := R.subgroupOf K
  have hBmap : B.map K.subtype = R := map_subgroupOf_eq_of_le hRK
  have hstab : MulAction.stabilizer N B = (normalizer (R : Set G)).subgroupOf N := by
    ext n
    change B.map (a n).toMonoidHom = B ↔ (n : G) ∈ normalizer (R : Set G)
    rw [mem_normalizer_iff_map_conj_eq]
    constructor
    · intro he
      have hh := congrArg (map K.subtype) he
      rwa [hformula,hBmap] at hh
    · intro he
      apply map_injective K.subtype_injective
      rwa [hformula,hBmap]
  have hmem (n : N) : n • B ∈ {C : Subgroup K |
      C ∈ localCComponents (S : Subgroup K) ∧
        (S : Subgroup K) ≤ normalizer (C : Set K) ∧ C ≠ ⊤} := by
    let : Group.IsSolvable (a n).toMonoidHom.ker := by
      rw [(a n).toMonoidHom.ker_eq_bot (a n).injective]
      infer_instance
    refine ⟨?_,?_,?_⟩
    · have hh := Chapter1.Section02.localCComponents_map_of_solvable_ker hl (a n).toMonoidHom
      rwa [hS] at hh
    · have hh := (map_mono (f := (a n).toMonoidHom) hn).trans (B.le_normalizer_map (a n).toMonoidHom)
      rwa [hS] at hh
    · intro he
      apply hp
      exact (map_injective (a n).injective) (he.trans (map_top_of_surjective _ (a n).surjective).symm)
  let j : MulAction.orbit N B → NormalizedProperLocals (S : Subgroup K) := fun C =>
    ⟨C.val,by obtain ⟨n,hn⟩ := C.property; exact hn ▸ hmem n⟩
  have hj : Function.Injective j := by
    intro C D he
    have hv : C.val = D.val := congrArg
      (fun V : NormalizedProperLocals (S : Subgroup K) => V.val) he
    exact Subtype.ext hv
  change ((normalizer (R : Set G)).subgroupOf N).index ≤ 2
  rw [←hstab,MulAction.index_stabilizer]
  exact (Nat.card_le_card_of_injective j hj).trans hc

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ClassicalLocalPairs
