module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.AmbientControl
public import Theory.SpecificGroups.Alternating.FiveOrderTwentyFour
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Theory.GroupTheory.PCoreSurjective

/-!
# The two cores in the original HS overlap

The overlap of the marked involution centralizer and seed normalizer has an
S₄ quotient with kernel the first local two-core. The second local two-core
maps onto its Klein four subgroup. Thus the two actual cores intersect in
order sixteen and generate the overlap's two-core of order 256.

These are direct consequences of HS1--HS2 preceding Aschbacher--Smith I.4.8,
printed p.418; no recognition or ambient simplicity is used.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims

private theorem point_card (i : Fin 5) :
    Nat.card (MulAction.stabilizer (Equiv.Perm (Fin 5)) i) = 24 := by
  have hi : (MulAction.stabilizer (Equiv.Perm (Fin 5)) i).index = 5 := by
    rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ]
    simp
  have hh := (MulAction.stabilizer (Equiv.Perm (Fin 5)) i).card_mul_index
  rw [hi, Nat.card_perm, show Nat.card (Fin 5) = 5 from by simp] at hh
  norm_num [Nat.factorial] at hh ⊢
  omega

private def point_equiv (i : Fin 5) :
    MulAction.stabilizer (Equiv.Perm (Fin 5)) i ≃* Equiv.Perm (Fin 4) := by
  classical
  let X := {x : Fin 5 // x ≠ i}
  let f : MulAction.stabilizer (Equiv.Perm (Fin 5)) i →* Equiv.Perm X := {
    toFun g := g.val.subtypePerm (fun x => by
      have hg : g.val i = i := g.property
      simpa only [hg] using g.val.injective.ne_iff (x := x) (y := i))
    map_one' := by ext x; rfl
    map_mul' := by intros; ext x; rfl }
  have hfi : Function.Injective f := by
    intro g h he
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hx : x = i
    · subst x; exact g.property.trans h.property.symm
    · exact congrArg Subtype.val (DFunLike.congr_fun he ⟨x, hx⟩)
  have hX : Fintype.card X = 4 := by simp [X, Fintype.card_subtype_compl]
  have hc : Nat.card (MulAction.stabilizer (Equiv.Perm (Fin 5)) i) =
      Nat.card (Equiv.Perm X) := by
    rw [point_card, Nat.card_eq_fintype_card, Fintype.card_perm, hX]
    rfl
  let e := MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hfi, hc⟩)
  exact e.trans (Equiv.permCongrHom (Fintype.equivFinOfCardEq hX))

variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The literal overlap is a point stabilizer in the centralizer's five-point action. -/
theorem TypeAt.exists_overlap_five_marking (h : TypeAt z V) :
    ∃ (f : involutionCentralizer z →* Equiv.Perm (Fin 5)) (i : Fin 5),
      Function.Surjective f ∧ f.ker = pCore 2 (involutionCentralizer z) ∧
      (normalizer (V : Set G)).subgroupOf (involutionCentralizer z) =
        (MulAction.stabilizer (Equiv.Perm (Fin 5)) i).comap f := by
  let H := involutionCentralizer z
  let B := (normalizer (V : Set G)).subgroupOf H
  let e := h.centralizer_quotient.some
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (localCore z))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 H := by
    ext x
    change e (QuotientGroup.mk' (localCore z) x) = 1 ↔ x ∈ pCore 2 H
    rw [← e.map_one, e.injective.eq_iff]
    exact (QuotientGroup.eq_one_iff (N := localCore z) x).trans
      (by rw [h.centralizer_fitting])
  have hKB : f.ker ≤ B := by
    intro x hx
    exact (h.local_cores_le_intersection.1 ⟨x, hk ▸ hx, rfl⟩).2
  have hkc : Nat.card f.ker = 64 := by
    rw [hk, ← h.centralizer_fitting]
    exact h.centralizer_core_card
  have hbc : Nat.card B = 1536 := by
    rw [← card_subtype H B, subgroupOf_map_subtype, inf_comm]
    exact h.local_intersection_card
  have hmc : Nat.card (B.map f) = 24 := by
    have hh := (f.ker.subgroupOf B).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hKB).toEquiv, hkc, hbc] at hh
    change 64 * f.ker.relIndex B = 1536 at hh
    rw [relIndex_ker] at hh
    omega
  obtain ⟨i, hi⟩ :=
    Theory.SpecificGroups.Alternating.FivePointTwentyFour.exists_eq_stabilizer (B.map f) hmc
  refine ⟨f, i, hf, hk, ?_⟩
  rw [← hi, comap_map_eq, sup_eq_left.mpr hKB]

/-- The original overlap acts as S₄ modulo the involution-centralizer core. -/
theorem TypeAt.exists_overlap_four_quotient (h : TypeAt z V) :
    ∃ f : (involutionCentralizer z ⊓ normalizer (V : Set G) : Subgroup G) →*
        Equiv.Perm (Fin 4),
      Function.Surjective f ∧ f.ker = (pCore 2 (involutionCentralizer z)).comap
        (inclusion (show involutionCentralizer z ⊓ normalizer (V : Set G) ≤
          involutionCentralizer z from inf_le_left)) := by
  let H := involutionCentralizer z
  let I := H ⊓ normalizer (V : Set G)
  let Q := (pCore 2 H).map H.subtype
  have hQI : Q ≤ I := h.local_cores_le_intersection.1
  let j : I →* H := inclusion inf_le_left
  let e := h.centralizer_quotient.some
  let f := e.toMonoidHom.comp ((QuotientGroup.mk' (localCore z)).comp j)
  have hk : f.ker = (pCore 2 H).comap j := by
    ext x
    change e (QuotientGroup.mk' (localCore z) (j x)) = 1 ↔ j x ∈ pCore 2 H
    rw [← e.map_one, e.injective.eq_iff]
    exact (QuotientGroup.eq_one_iff (N := localCore z) (j x)).trans
      (by rw [h.centralizer_fitting])
  have hQ : (pCore 2 H).comap j = Q.subgroupOf I := by
    ext x
    change j x ∈ pCore 2 H ↔ (x : G) ∈ Q
    exact (mem_map_iff_mem H.subtype_injective).symm
  have hc : Nat.card f.ker = 64 := by
    rw [hk, hQ, Nat.card_congr (subgroupOfEquivOfLe hQI).toEquiv,
      card_map_of_injective H.subtype_injective, ← h.centralizer_fitting]
    exact h.centralizer_core_card
  have hfcard : Nat.card f.range = 24 := by
    have hh := f.ker.card_mul_index
    rw [hc, index_ker, show Nat.card I = 1536 from h.local_intersection_card] at hh
    omega
  obtain ⟨i, hi⟩ :=
    Theory.SpecificGroups.Alternating.FivePointTwentyFour.exists_eq_stabilizer f.range hfcard
  let a := (MulEquiv.subgroupCongr hi).trans (point_equiv i)
  refine ⟨a.toMonoidHom.comp f.rangeRestrict,
    a.surjective.comp f.rangeRestrict_surjective, ?_⟩
  rw [← hk]
  ext x
  change a (f.rangeRestrict x) = 1 ↔ f x = 1
  rw [← a.map_one, a.injective.eq_iff]
  exact Subtype.ext_iff

private theorem coreShape_not_comm {A : Type*} [Group A] [Finite A]
    (h : CoreShape A) : ¬ IsMulCommutative A := by
  intro hc
  obtain ⟨e⟩ := h.center_model
  have hh : Nat.card (center A) = 4 := by
    rw [Nat.card_congr e.toEquiv]
    simp
  rw [center_eq_top_iff.mpr hc, card_top, h.card] at hh
  contradiction

private theorem four_core_pair {A : Type*} [Group A] [Finite A]
    (f : A →* Equiv.Perm (Fin 4)) (hf : Function.Surjective f)
    (hkc : Nat.card f.ker = 64) (hkn : ¬ IsMulCommutative f.ker)
    (R : Subgroup A) [R.Normal] [IsMulCommutative R] (hRc : Nat.card R = 64) :
    Nat.card (f.ker ⊓ R : Subgroup A) = 16 ∧
      Nat.card (pCore 2 A) = 256 ∧ f.ker ⊔ R = pCore 2 A ∧
      Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) := by
  let C := Theory.SpecificGroups.SymmetricSix.DuadCalculation.core
  have hkp : IsPGroup 2 f.ker := IsPGroup.of_card (n := 6) (hkc.trans (by norm_num))
  have hRp : IsPGroup 2 R := IsPGroup.of_card (n := 6) (hRc.trans (by norm_num))
  let : (R.map f).Normal := (inferInstance : R.Normal).map f hf
  have hle : R.map f ≤ C := by
    rw [show C = pCore 2 (Equiv.Perm (Fin 4)) from
      Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq]
    exact le_sSup ⟨inferInstance, hRp.map f⟩
  have hmap : R.map f = C := by
    rcases Theory.SpecificGroups.SymmetricSix.DuadCalculation.normal_subgroup_core
      (R.map f) hle with hb | he
    · have hRk : R ≤ f.ker := (map_eq_bot_iff R).mp hb
      have he : R = f.ker := eq_of_le_of_card_ge hRk (by omega)
      exact (hkn (he ▸ inferInstanceAs (IsMulCommutative R))).elim
    · exact he
  have hjoin : f.ker ⊔ R = pCore 2 A := by
    rw [sup_comm, ← comap_map_eq, hmap,
      show C = pCore 2 (Equiv.Perm (Fin 4)) from
        Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq]
    exact f.comap_pCore_of_ker_isPGroup hf hkp
  have hpc : Nat.card (pCore 2 A) = 256 := by
    rw [f.card_pCore_of_ker_isPGroup hf hkp, hkc,
      ← Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq,
      Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_card]
  have hic : Nat.card (f.ker ⊓ R : Subgroup A) = 16 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes f.ker R
      (by rw [normalizer_eq_top]; exact le_top)
    rw [hkc, hRc, hjoin, hpc] at hh
    omega
  let q := Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom
  let g := q.comp f
  have hg : Function.Surjective g :=
    Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom_surjective.comp hf
  have hgk : IsPGroup 2 g.ker :=
    (IsElementaryAbelian.isPGroup 2 C).comap_of_ker_isPGroup f hkp
  have hge : g.ker = pCore 2 A := ker_eq_twoCore_of_surjective_perm_three g hg hgk
  exact ⟨hic, hpc, hjoin, ⟨(QuotientGroup.quotientMulEquivOfEq hge.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)⟩⟩

/-- The actual local cores meet in order sixteen and generate the overlap's two-core. -/
theorem TypeAt.local_cores_structure (h : TypeAt z V) :
    let H := involutionCentralizer z
    let M := normalizer (V : Set G)
    let I := H ⊓ M
    let Q := (pCore 2 H).map H.subtype
    let R := (pCore 2 M).map M.subtype
    Nat.card (Q ⊓ R : Subgroup G) = 16 ∧
      Nat.card (Q ⊔ R : Subgroup G) = 256 ∧
      (pCore 2 I).map I.subtype = Q ⊔ R ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) := by
  let H := involutionCentralizer z
  let M := normalizer (V : Set G)
  let I := H ⊓ M
  let Q := (pCore 2 H).map H.subtype
  let R := (pCore 2 M).map M.subtype
  have hQI : Q ≤ I := h.local_cores_le_intersection.1
  have hRI : R ≤ I := h.local_cores_le_intersection.2
  let QI := Q.subgroupOf I
  let RI := R.subgroupOf I
  let eQ : pCore 2 H ≃* QI :=
    ((pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (subgroupOfEquivOfLe hQI).symm
  let eR : pCore 2 M ≃* RI :=
    ((pCore 2 M).equivMapOfInjective M.subtype M.subtype_injective).trans
      (subgroupOfEquivOfLe hRI).symm
  have hQc : Nat.card QI = 64 := by
    rw [← Nat.card_congr eQ.toEquiv, ← h.centralizer_fitting]
    exact h.centralizer_core_card
  have hRc : Nat.card RI = 64 := by
    rw [← Nat.card_congr eR.toEquiv, ← h.normalizer_fitting]
    exact h.normalizer_core_card
  have hQs : CoreShape QI := (h.centralizer_core.of_equiv
    (MulEquiv.subgroupCongr h.centralizer_fitting)).of_equiv eQ
  let a := eR.symm.trans ((MulEquiv.subgroupCongr h.normalizer_fitting.symm).trans
    h.normalizer_core.some)
  let : IsMulCommutative RI := ⟨⟨fun x y => a.injective ((a.map_mul x y).trans
    ((mul_comm (a x) (a y)).trans (a.map_mul y x).symm))⟩⟩
  have hRe : RI = (pCore 2 M).comap
      (inclusion (show I ≤ M from inf_le_right)) := by
    ext x
    change (x : G) ∈ (pCore 2 M).map M.subtype ↔
      inclusion (show I ≤ M from inf_le_right) x ∈ pCore 2 M
    exact mem_map_iff_mem M.subtype_injective (K := pCore 2 M)
      (x := inclusion (show I ≤ M from inf_le_right) x)
  let : RI.Normal := by rw [hRe]; infer_instance
  obtain ⟨f, hf, hk⟩ := h.exists_overlap_four_quotient
  have hkQ : f.ker = QI := by
    rw [hk]
    ext x
    change inclusion (show I ≤ H from inf_le_left) x ∈ pCore 2 H ↔
      (x : G) ∈ (pCore 2 H).map H.subtype
    exact (mem_map_iff_mem H.subtype_injective).symm
  obtain ⟨hic, hpc, hjoin, he⟩ := four_core_pair f hf (hkQ.symm ▸ hQc)
    (hkQ.symm ▸ coreShape_not_comm hQs) RI hRc
  rw [hkQ] at hic hjoin
  have hi : Nat.card (Q ⊓ R : Subgroup G) = 16 := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hQI)).toEquiv]
    exact hic
  have hj : (pCore 2 I).map I.subtype = Q ⊔ R := by
    rw [← hjoin, ← subgroupOf_sup hQI hRI, subgroupOf_map_subtype,
      inf_eq_left.mpr (sup_le hQI hRI)]
  have hjc : Nat.card (Q ⊔ R : Subgroup G) = 256 := by
    rw [← hj, card_map_of_injective I.subtype_injective]
    exact hpc
  exact ⟨hi, hjc, hj, he⟩

end CFSG.Quasithin.HigmanSims
