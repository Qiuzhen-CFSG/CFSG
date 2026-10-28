module
public import CFSG.Quasithin.ChapterG.Section02.Binary.Recognition.Maps
public import Theory.GroupTheory.IrreducibleNormalizerCore

/-!
# Recognition of the binary star quotient by its natural action

The action of LT on V has kernel O₂(LT). Irreducibility makes the
core centralize V, while the faithful C₃ coordinates on L and the
two-group quotient LT/L make the entire action kernel a two-group.
The action on the three nonidentity vectors therefore embeds the actual
star quotient into S₃. Its L-image has order three, and its U-image is a
nontrivial two-group, so the embedding is onto.

Source: Aschbacher–Smith, G.2.3(1), printed p.333.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}

private theorem faithful_raw : ∀ a : Equiv.Perm (Fin 3),
    (∀ v : Fin 3 → ZMod 2, (∑ i, v i) = 0 → ∀ i, v (a⁻¹ i) = v i) → a = 1 := by
  decide +kernel

private theorem faithful_plane (a : alternatingGroup (Fin 3))
    (ha : ∀ v : BinaryPermutation.core (Fin 3),
      BinaryPermutation.coreRepresentation (Fin 3) a.val v = v) : a = 1 := by
  apply Subtype.ext
  apply faithful_raw
  intro v hv i
  exact congrArg (fun w : BinaryPermutation.core (Fin 3) => w.val i) (ha ⟨v, hv⟩)

theorem binary_LT_core_centralizes_V (h : D.BaseHypothesis) (b : D.BinaryNaturalData) :
    D.LT.pCoreIn 2 ≤ centralizer (D.V : Set G) := by
  exact pCoreIn_le_centralizer_of_irreducible D.V D.L D.LT
    (h.binary_T_isPGroup.to_le h.V_le_T) (h.V_le_T.trans le_sup_right)
    (b.binary_LT_normalizes_V h) le_sup_left b.irreducible

theorem binaryLStar_eq_one_of_conjugation_eq_one (h : D.BaseHypothesis) (b : D.BinaryNaturalData)
    (l : D.L) (hl : D.binaryConjugation h b (inclusion (show D.L ≤ D.LT from le_sup_left) l) = 1) :
    D.binaryLStar l = 1 := by
  apply b.quotientEquiv.injective
  rw [map_one]
  apply faithful_plane
  intro v
  obtain ⟨w, hw⟩ := b.coordinates.surjective (Multiplicative.ofAdd v)
  have he := b.equivariant l w
  have hwfix : D.V.normalizerMonoidHom ⟨l, b.L_normalizes_V l.property⟩ w = w := by
    exact congrArg (fun a : MulAut D.V => a w) hl
  rw [hwfix, hw] at he
  exact he.symm

theorem binaryConjugation_kernel_isPGroup (h : D.BaseHypothesis) (b : D.BinaryNaturalData) :
    IsPGroup 2 (D.binaryConjugation h b).ker := by
  let a := D.binaryConjugation h b
  let N := D.L.subgroupOf D.LT
  have hn : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le D.L.le_normalizer h.T_normalizes_L)
  let := hn
  have ht : N ⊔ D.T.subgroupOf D.LT = ⊤ := by
    rw [← subgroupOf_sup (show D.L ≤ D.LT from le_sup_left) le_sup_right]
    exact subgroupOf_self _
  have hp : IsPGroup 2 (D.LT ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N (D.T.subgroupOf D.LT)
      h.binary_T_isPGroup.comap_subtype ht
  let r : a.ker →* D.LT ⧸ N := (QuotientGroup.mk' N).comp a.ker.subtype
  have hr : IsPGroup 2 r.ker := by
    let j : r.ker →* pCore 2 D.LT :=
      { toFun := fun x => ⟨x.val.val, by
          have hxl : (x.val.val : G) ∈ D.L :=
            (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property
          have hx := binaryLStar_eq_one_of_conjugation_eq_one h b ⟨x.val.val, hxl⟩ x.val.property
          exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    apply pCore_isPGroup.of_injective j
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : pCore 2 D.LT => z.val) he))
  have hh := (hp.to_subgroup ⊤).comap_of_ker_isPGroup r hr
  rw [comap_top] at hh
  exact hh.of_equiv topEquiv

theorem binaryConjugation_kernel (h : D.BaseHypothesis) (b : D.BinaryNaturalData) :
    (D.binaryConjugation h b).ker = pCore 2 D.LT := by
  have hle : (D.binaryConjugation h b).ker ≤ pCore 2 D.LT :=
    le_sSup ⟨inferInstance, binaryConjugation_kernel_isPGroup h b⟩
  apply le_antisymm hle
  intro x hx
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  change (x : G) * (v : G) * (x : G)⁻¹ = v
  have hc := binary_LT_core_centralizes_V h b (mem_map_of_mem D.LT.subtype hx) v.val v.property
  change (v : G) * (x : G) = (x : G) * (v : G) at hc
  rw [← hc, mul_assoc, mul_inv_cancel, mul_one]

noncomputable def binaryNonzeroLabels (b : D.BinaryNaturalData) : {v : D.V // v ≠ 1} ≃ Fin 3 := by
  classical
  let := Fintype.ofFinite D.V
  apply Fintype.equivFinOfCardEq
  have hc : Fintype.card D.V = 4 := by simpa only [Nat.card_eq_fintype_card] using b.card_V
  simp only [Fintype.card_subtype_compl, Fintype.card_unique, hc]

noncomputable def binaryNonzeroAut : MulAut D.V →* Equiv.Perm {v : D.V // v ≠ 1} where
  toFun f := by
    classical
    exact Equiv.Perm.subtypePerm f.toEquiv (fun x => by simp)
  map_one' := by ext x; rfl
  map_mul' f g := by ext x; rfl

omit [Finite G] in
theorem binaryNonzeroAut_injective : Function.Injective (binaryNonzeroAut (D := D)) := by
  intro f g he
  apply MulEquiv.ext
  intro v
  by_cases hv : v = 1
  · simp only [hv, map_one]
  · exact congrArg Subtype.val (Equiv.congr_fun he ⟨v, hv⟩)

noncomputable def binaryPermutationAction (h : D.BaseHypothesis) (b : D.BinaryNaturalData) :
    D.LT →* Equiv.Perm (Fin 3) :=
  (binaryNonzeroLabels b).permCongrHom.toMonoidHom.comp
    (binaryNonzeroAut.comp (D.binaryConjugation h b))

theorem binaryPermutationAction_kernel (h : D.BaseHypothesis) (b : D.BinaryNaturalData) :
    (binaryPermutationAction h b).ker = pCore 2 D.LT := by
  rw [← binaryConjugation_kernel h b]
  ext x
  change (binaryNonzeroLabels b).permCongrHom (binaryNonzeroAut (D.binaryConjugation h b x)) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]
  exact (map_eq_one_iff _ binaryNonzeroAut_injective)

noncomputable def binaryStarEmbedding (h : D.BaseHypothesis) (b : D.BinaryNaturalData) :
    D.Star →* Equiv.Perm (Fin 3) :=
  QuotientGroup.lift (pCore 2 D.LT) (binaryPermutationAction h b) (binaryPermutationAction_kernel h b).ge

theorem binaryStarEmbedding_injective (h : D.BaseHypothesis) (b : D.BinaryNaturalData) :
    Function.Injective (binaryStarEmbedding h b) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 D.LT) x
  exact (QuotientGroup.eq_one_iff y).mpr ((binaryPermutationAction_kernel h b).le hx)

theorem binaryStarEmbedding_surjective (h : D.BaseHypothesis) (b : D.BinaryNaturalData) (hUT : D.U ≤ D.T) :
    Function.Surjective (binaryStarEmbedding h b) := by
  let j := binaryStarEmbedding h b
  have hj := binaryStarEmbedding_injective h b
  have hperm : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hd : Nat.card j.range ∣ 6 := hperm ▸ j.range.card_subgroup_dvd_card
  have hL : Nat.card (D.star D.L) = 3 := by
    rw [Nat.card_congr b.quotientEquiv.toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  have h3 : 3 ∣ Nat.card j.range := by
    have hdL := (D.star D.L).card_subgroup_dvd_card
    rw [hL, Nat.card_congr (MonoidHom.ofInjective hj).toEquiv] at hdL
    exact hdL
  have hp : IsPGroup 2 (D.star D.U) :=
    (h.binary_U_isPGroup hUT).comap_subtype.map (QuotientGroup.mk' (pCore 2 D.LT))
  have h2 : 2 ∣ Nat.card j.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv]
    exact ((hp.card_eq_or_dvd).resolve_left
      (fun he => b.image_nontrivial (Subgroup.card_eq_one.mp he))).trans
      (D.star D.U).card_subgroup_dvd_card
  have he : Nat.card j.range = 6 := Nat.dvd_antisymm hd
    ((by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3)
  apply MonoidHom.range_eq_top.mp
  apply eq_top_of_card_eq
  exact he.trans hperm.symm

noncomputable def binaryStarEquiv (h : D.BaseHypothesis) (b : D.BinaryNaturalData)
    (hUT : D.U ≤ D.T) : D.Star ≃* Equiv.Perm (Fin 3) :=
  MulEquiv.ofBijective (binaryStarEmbedding h b)
    ⟨binaryStarEmbedding_injective h b, binaryStarEmbedding_surjective h b hUT⟩

/-- The recognized star quotient induces the original action on the three nonzero vectors. -/
theorem binaryStarEquiv_apply (h : D.BaseHypothesis) (b : D.BinaryNaturalData)
    (hUT : D.U ≤ D.T) (x : D.LT) :
    binaryStarEquiv h b hUT (QuotientGroup.mk' (pCore 2 D.LT) x) =
      binaryPermutationAction h b x := rfl

end CFSG.Quasithin.ChapterG.Section02.Setup
