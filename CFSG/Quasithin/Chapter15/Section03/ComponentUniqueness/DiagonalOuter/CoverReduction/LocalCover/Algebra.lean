module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.ModelWitnesses
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalAlgebra
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.MatrixModel
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.NormalSylowCoreCentralizer
public import Theory.Quasithin.EvenCharacteristic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SectionCentralizers
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowKernelCore

/-!
# Local algebra for the first reduction in 15.3.38

The diagonal action is extracted with its actual quotient marking. A highest
root subgroup in the image of a four-group bounds the field order; positivity
and evenness then force n=2. Reindexing preserves both the coefficient field
and the quotient equivalence, hence the actual order-three conjugation action.

The remaining lemmas compare conjugate cores and centralizers, eliminate the
odd part of a normal centralizer by Burnside transfer, and turn section-action
coverage into a literal subgroup product. `planeResidual M Y W` means
O²(Y ∩ C_M(W)); it is a residual, never a two-core. `PlaneOrder` records the
equalities for a compatible relabelling of both original planes.

These are conditional finite-group deductions. Construction of their local
inputs from the Borel and residual setup remains separate. None asserts the
numbered source theorem or assumes a center or full-centralizer certificate.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
proof of 15.3.38, printed pp.1135--1136.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
variable {G : Type*} [Group G] [Finite G]

noncomputable def planeResidual (M Y W : Subgroup G) : Subgroup G :=
  Stellmacher.twoResidualAmbient (Y ⊓ (M ⊓ centralizer (W : Set G)))

def centerImage (L : Subgroup G) : Subgroup G := (center L).map L.subtype

omit [Finite G] in
theorem centerImage_le (L : Subgroup G) : centerImage L ≤ L := map_subtype_le _

omit [Finite G] in
theorem centerImage_centralizes (L : Subgroup G) :
    centerImage L ≤ centralizer (L : Set G) := by
  rintro _ ⟨x, hx, rfl⟩ y hy
  exact congrArg Subtype.val (mem_center_iff.mp hx (⟨y, hy⟩ : L))

omit [Finite G] in
theorem marking_of_diagonal {L : Subgroup G} {y : G} {q : ℕ}
    (hy : orderOf y = 3) (h : Candidates.LinearDiagonalOnTwoQuotient L y q) :
    ∃ c : ProjectiveMarking L q, c.Diagonal y := by
  obtain ⟨F, hF, hf, hcard, e, α, d, hconj, hout, hcompat⟩ := h
  exact ⟨⟨F, hcard, e⟩, hy, d, hout, α, hconj, hcompat⟩

def projectiveMap {L : Subgroup G} {q : ℕ} (c : ProjectiveMarking L q) :
    L →* PSL(3,c.F) := c.equivalence.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

theorem field_size_le_plane {L W : Subgroup G} {q : ℕ} (c : ProjectiveMarking L q)
    (hWL : W ≤ L)
    (hroot : Matrix.PSL3Even.UnipotentGeometry.projectiveCenter c.F ≤
      (W.subgroupOf L).map (projectiveMap c)) : q ≤ Nat.card W := by
  have hc : Nat.card (Matrix.PSL3Even.UnipotentGeometry.projectiveCenter c.F) = q := by
    rw [Matrix.PSL3Even.UnipotentGeometry.projectiveCenter,
      ← Nat.card_congr (equivMapOfInjective _ _
        (Matrix.PSL3Even.UnipotentGeometry.projective_injective c.F)).toEquiv,
      Matrix.PSL3Even.UnipotentGeometry.card_Z, c.card]
  have h₁ := card_le_of_le hroot
  have h₂ := Nat.le_of_dvd (Nat.card_pos (α := W.subgroupOf L))
    ((W.subgroupOf L).card_map_dvd (projectiveMap c))
  rw [hc] at h₁
  rw [Nat.card_congr (subgroupOfEquivOfLe hWL).toEquiv] at h₂
  exact h₁.trans h₂

theorem parameter_eq_two {n : ℕ} (hn : 0 < n) (heven : Even n)
    (hbound : 2 ^ n ≤ 4) : n = 2 := by
  have hle : n ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
    exact hbound
  obtain ⟨k, hk⟩ := heven
  omega

omit [Finite G] in
/-- Fixed elements lift uniquely when the central kernel has no fixed points. -/
theorem fixed_eq_of_central_kernel {Q D W Z : Subgroup G}
    (hW : W ≤ Q ⊓ centralizer (D : Set G))
    (hfix : Q ⊓ centralizer (D : Set G) ≤ W ⊔ Z)
    (hZW : Z ≤ centralizer (W : Set G))
    (hZ : Z ⊓ centralizer (D : Set G) = ⊥) :
    Q ⊓ centralizer (D : Set G) = W := by
  apply le_antisymm _ hW
  intro x hx
  have hp : x ∈ (W : Set G) * (Z : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left W Z
      (hZW.trans (Subgroup.centralizer_le_normalizer _))]
    exact hfix hx
  obtain ⟨w, hw, z, hz, rfl⟩ := hp
  have hzD : z ∈ centralizer (D : Set G) :=
    (centralizer (D : Set G)).mul_mem_cancel_left (hW hw).2 |>.mp hx.2
  have hz1 : z = 1 := mem_bot.mp (hZ ▸ (show z ∈ Z ⊓ centralizer (D : Set G) from ⟨hz, hzD⟩))
  change w * z ∈ W
  rw [hz1, mul_one]
  exact hw

/-- The equal-size conjugate core contains Q, so equals Q. -/
theorem core_eq_and_invariant {A D Q : Subgroup G} (e : G ≃* G)
    (hA : A.map e.toMonoidHom = D) (hAQ : A.pCoreIn 2 = Q)
    (hQD : Q ≤ D.pCoreIn 2) : D.pCoreIn 2 = Q ∧ Q.map e.toMonoidHom = Q := by
  have hm : Q.map e.toMonoidHom = D.pCoreIn 2 := by
    rw [← hAQ, map_pCoreIn_of_injective 2 A e.toMonoidHom e.injective, hA]
  have hc : Nat.card (D.pCoreIn 2) = Nat.card Q := by
    rw [← hm]
    exact (Nat.card_congr (e.subgroupMap Q).toEquiv).symm
  have heq := eq_of_le_of_card_ge hQD hc.le
  exact ⟨heq.symm, hm.trans heq.symm⟩

omit [Finite G] in
/-- Conjugating the two centralizers determines the center's actual plane label. -/
theorem center_eq_of_interchange {Q A D Z V₁ V₂ : Subgroup G} (e : G ≃* G)
    (hQ : Q.map e.toMonoidHom = Q)
    (hD : D.map e.toMonoidHom = A)
    (hV : V₂.map e.toMonoidHom = V₁)
    (hZA : Q ⊓ centralizer (A : Set G) = Z)
    (hWD : Q ⊓ centralizer (D : Set G) = V₂) : Z = V₁ := by
  have hh := congrArg (Subgroup.map e.toMonoidHom) hWD
  rw [map_inf _ _ _ e.injective, Theory.Quasithin.map_centralizer, hQ, hD, hV,
    hZA] at hh
  exact hh

/-- The source's order argument after killing C_S(Y). -/
theorem centralizer_eq_plane {S L A D V₁ V₂ : Subgroup G}
    (hA : A = S ⊓ centralizer (L : Set G))
    (hS : S ≤ normalizer (L : Set G)) (hDS : D ≤ S) (hVS : V₂ ≤ S)
    (hDA : D ≤ V₂ ⊔ A) (hdis : A ⊓ D = ⊥)
    (hcard : Nat.card D = Nat.card A)
    (hVA : V₁ ≤ A) (hVcard : Nat.card V₁ = Nat.card V₂) : A = V₁ := by
  have hSn : S ≤ normalizer (A : Set G) := by
    rw [hA]
    exact le_normalizer_inf S.le_normalizer
      (hS.trans (normalizer_le_normalizer_centralizer L))
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes A D (hDS.trans hSn)
  rw [hdis, card_bot, one_mul, hcard] at hprod
  have hbound : Nat.card (A ⊔ D : Subgroup G) ≤ Nat.card (A ⊔ V₂ : Subgroup G) :=
    card_le_of_le (sup_le le_sup_left (hDA.trans (by rw [sup_comm])))
  have hsup := card_mul_eq_card_inf_mul_card_sup_of_normalizes A V₂ (hVS.trans hSn)
  have hpos : 1 ≤ Nat.card (A ⊓ V₂ : Subgroup G) := Nat.card_pos
  have hup : Nat.card (A ⊔ V₂ : Subgroup G) ≤ Nat.card A * Nat.card V₂ := by
    nlinarith
  have hsmall : Nat.card A ≤ Nat.card V₂ := by
    have hapos : 0 < Nat.card A := Nat.card_pos
    have : Nat.card A * Nat.card A ≤ Nat.card A * Nat.card V₂ :=
      hprod.trans_le (hbound.trans hup)
    exact Nat.le_of_mul_le_mul_left this hapos
  exact (eq_of_le_of_card_ge hVA (hVcard ▸ hsmall)).symm

/-- A central Sylow subgroup exhausts a group with trivial odd core. -/
theorem eq_top_of_central_sylow (P : Sylow 2 G)
    (hP : (P : Subgroup G) ≤ center G) (hodd : pPrimeCore 2 G = ⊥) :
    (P : Subgroup G) = ⊤ := by
  let : (P : Subgroup G).Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hP hx) g, mul_inv_cancel_right]
    exact hx⟩
  have hc : centralizer (P : Set G) = ⊤ := by
    apply top_unique
    intro x _ y hy
    exact (mem_center_iff.mp (hP hy) x).symm
  have hb := P.centralizer_le_sup_pPrimeCore_of_normal
  rw [hodd, sup_bot_eq, hc] at hb
  exact top_unique hb

/-- If the Sylow centralizer lies in L, Burnside transfer eliminates its odd part. -/
theorem centralizer_eq_sylow_centralizer (I L S : Subgroup G)
    (hLI : L ≤ I) (hIL : I ≤ normalizer (L : Set G))
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hodd : pPrimeCore 2 I = ⊥)
    (hCL : S ⊓ centralizer (L : Set G) ≤ L) :
    I ⊓ centralizer (L : Set G) = S ⊓ centralizer (L : Set G) := by
  let L' := L.subgroupOf I
  let : L'.Normal := normal_subgroupOf_of_le_normalizer hIL
  let C := centralizer (L' : Set I)
  let : C.Normal := normal_centralizer
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_normal C
  have hQc : (Q : Subgroup C) ≤ center C := by
    intro x hx
    have hxP : (x : I) ∈ (P : Subgroup I) := by
      rw [hQ] at hx
      exact hx
    have hxS : ((x : I) : G) ∈ S := hP ▸ mem_map_of_mem I.subtype hxP
    have hxC : ((x : I) : G) ∈ centralizer (L : Set G) := by
      intro l hl
      exact congrArg Subtype.val (x.property (⟨l, hLI hl⟩ : I) hl)
    have hxL : (x : I) ∈ L' := hCL ⟨hxS, hxC⟩
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (c.property x hxL).symm
  have hcore : pPrimeCore 2 C = ⊥ := by
    apply ((pPrimeCore 2 C).map_eq_bot_iff_of_injective C.subtype_injective).mp
    exact le_bot_iff.mp ((pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 C).trans hodd.le)
  have htop := eq_top_of_central_sylow Q hQc hcore
  apply le_antisymm
  · rintro g ⟨hgI, hgC⟩
    let c : C := ⟨⟨g, hgI⟩, fun l hl => Subtype.ext (hgC l hl)⟩
    have hcQ : c ∈ (Q : Subgroup C) := htop ▸ mem_top c
    rw [hQ] at hcQ
    exact ⟨hP ▸ mem_map_of_mem I.subtype hcQ, hgC⟩
  · exact inf_le_inf_right _ (hP ▸ map_subtype_le _)

/-- Transport the component center theorem through the literal inclusion in I. -/
theorem center_eq_twoCore_in {I L : Subgroup G} (hLI : L ≤ I)
    (hL : IsComponent I (L.subgroupOf I)) (hodd : pPrimeCore 2 I = ⊥) :
    center L = pCore 2 L := by
  let e := subgroupOfEquivOfLe hLI
  have hc : (center (L.subgroupOf I)).map e.toMonoidHom = center L := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.centerCongr e ⟨x, hx⟩).property
    · intro x hx
      exact ⟨e.symm x, ((Subgroup.centerCongr e).symm ⟨x, hx⟩).property,
        e.apply_symm_apply x⟩
  rw [← hc, component_center_eq_twoCore hL hodd, pCore_map_iso]

omit [Finite G] in
/-- If the two-core of YS lies in Y, it is exactly the two-core of Y. -/
theorem twoCore_eq_of_join_core {Y S Q : Subgroup G}
    (hSY : S ≤ normalizer (Y : Set G))
    (hcore : (Y ⊔ S : Subgroup G).pCoreIn 2 = Q) (hQY : Q ≤ Y) :
    Y.pCoreIn 2 = Q := by
  apply le_antisymm
  · exact (pCoreIn_mono_of_normalizes (show Y ≤ Y ⊔ S from le_sup_left)
      (sup_le Y.le_normalizer hSY)).trans hcore.le
  · apply le_pCoreIn_of_normalizes
    · exact hcore ▸ isPGroup_pCoreIn 2 (Y ⊔ S)
    · exact hQY
    · rw [← hcore]
      exact (show Y ≤ Y ⊔ S from le_sup_left).trans
        ((Y ⊔ S).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image (Y ⊔ S) (pCore 2 (Y ⊔ S : Subgroup G))))

omit [Finite G] in
/-- Action coverage modulo the centralizer becomes a literal three-factor product. -/
theorem product_of_section_action_coverage {I L D S : Subgroup G}
    [Group.IsPerfect L] (hcore : pCore 2 L ≤ center L)
    (hLI : L ≤ I) (hDI : D ≤ I) (hSI : S ≤ I)
    (hC : I ⊓ centralizer (L : Set G) ≤ L)
    (hcover : ∀ i ∈ I, ∃ l ∈ L, ∃ d ∈ D, ∃ s ∈ S,
      i * (l * d * s)⁻¹ ∈ Chapter4.sectionCentralizer L) :
    (I : Set G) = (L : Set G) * (D : Set G) * (S : Set G) := by
  apply Set.Subset.antisymm
  · intro i hi
    obtain ⟨l, hl, d, hd, s, hs, hc⟩ := hcover i hi
    rw [sectionCentralizer_eq_centralizer_of_perfect hcore] at hc
    have hk : i * (l * d * s)⁻¹ ∈ L := hC ⟨I.mul_mem hi
      (I.inv_mem (I.mul_mem (I.mul_mem (hLI hl) (hDI hd)) (hSI hs))), hc⟩
    refine ⟨(i * (l * d * s)⁻¹ * l) * d,
      ⟨i * (l * d * s)⁻¹ * l, L.mul_mem hk hl, d, hd, rfl⟩, s, hs, ?_⟩
    simp [mul_assoc]
  · rintro _ ⟨_, ⟨l, hl, d, hd, rfl⟩, s, hs, rfl⟩
    exact I.mul_mem (I.mul_mem (hLI hl) (hDI hd)) (hSI hs)

omit [Finite G] in
theorem centerImage_eq_inf (L : Subgroup G) :
    centerImage L = L ⊓ centralizer (L : Set G) := by
  apply le_antisymm (le_inf (centerImage_le L) (centerImage_centralizes L))
  rintro x ⟨hxL, hxC⟩
  exact ⟨⟨x, hxL⟩, mem_center_iff.mpr (fun l => Subtype.ext (hxC l l.property)), rfl⟩

omit [Finite G] in
theorem centralizer_join (A D : Subgroup G) :
    centralizer (A ⊔ D : Subgroup G) = centralizer (A : Set G) ⊓ centralizer (D : Set G) := by
  apply le_antisymm
  · exact le_inf (centralizer_le (show A ≤ A ⊔ D from le_sup_left))
      (centralizer_le (show D ≤ A ⊔ D from le_sup_right))
  · exact le_centralizer_iff.mpr (sup_le
      (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right))

omit [Finite G] in
theorem commutator_le_twoCore {Q D : Subgroup G}
    (hQ : IsPGroup 2 Q) (hQD : Q ≤ normalizer (D : Set G))
    (hDQ : D ≤ normalizer (Q : Set G)) : ⁅Q, D⁆ ≤ D.pCoreIn 2 := by
  apply le_pCoreIn_of_normalizes
  · exact hQ.to_le (le_normalizer_iff_commutator_le_left.mp hDQ)
  · rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp hQD
  · exact normalizer_commutator_ge_right Q D

omit [Finite G] in
/-- A plane centralized by an outside component excludes case (2) of 15.3.10. -/
theorem yplus_eq_y_of_centralized_plane {M Y S V₁ V₂ W Yplus L : Subgroup G}
    (h10 : Hypothesis15310 M Y S V₁ Yplus)
    (hcase : Chapter4.UniqueMaximalOvergroup (Y ⊔ S) M →
      Yplus = Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V₁ : Set G)) →
      normalizer (V₁ : Set G) ≤ M ∧ normalizer (V₂ : Set G) ≤ M)
    (hW : W = V₁ ∨ W = V₂) (hWC : W ≤ centralizer (L : Set G))
    (hLM : ¬ L ≤ M) : Yplus = Y := by
  rcases h10 with h | ⟨hu, hy⟩
  · exact h
  · have hLN : L ≤ normalizer (W : Set G) :=
      (le_centralizer_iff.mp hWC).trans (Subgroup.centralizer_le_normalizer _)
    obtain ⟨h₁, h₂⟩ := hcase hu hy
    rcases hW with rfl | rfl
    · exact (hLM (hLN.trans h₁)).elim
    · exact (hLM (hLN.trans h₂)).elim

omit [Finite G] in
/-- The actor and its quotient marking survive the two source model alternatives. -/
theorem marking_of_rankTwoDiagonal {Yplus L L₀ : Subgroup G}
    (h : Candidates.RankTwoDiagonal Yplus L L₀) :
    ∃ n : ℕ, 0 < n ∧ Even n ∧ ∃ y ∈ Yplus,
      ∃ c : ProjectiveMarking L (2 ^ n), c.Diagonal y ∧
        (Yplus : Set G) = (componentPart Yplus L : Set G) * (zpowers y : Set G) := by
  obtain ⟨_, _, y, hy, horder, hprod, hmodel⟩ := h
  rcases hmodel with ⟨n, hn, he, _, hd⟩ | hd
  · obtain ⟨c, hc⟩ := marking_of_diagonal horder hd
    exact ⟨n, hn, he, y, hy, c, hc, hprod⟩
  · obtain ⟨c, hc⟩ := marking_of_diagonal horder hd
    exact ⟨2, by decide, by decide, y, hy, c, hc, hprod⟩

/-- Both choices identify the actual planes, rather than just naming a family. -/
def PlaneOrder (V₁ V₂ W₁ W₂ : Subgroup G) : Prop :=
  (W₁ = V₁ ∧ W₂ = V₂) ∨ (W₁ = V₂ ∧ W₂ = V₁)

omit [Finite G] in
/-- Relabel the planes together with their actual interchange. -/
theorem choose_plane_order {V₁ V₂ A : Subgroup G} (e : G ≃* G)
    (h₁ : V₁.map e.toMonoidHom = V₂) (h₂ : V₂.map e.toMonoidHom = V₁)
    (hA : A ≤ centralizer (V₁ : Set G) ∨ A ≤ centralizer (V₂ : Set G)) :
    ∃ W₁ W₂ : Subgroup G, PlaneOrder V₁ V₂ W₁ W₂ ∧
      A ≤ centralizer (W₁ : Set G) ∧
      W₁.map e.toMonoidHom = W₂ ∧ W₂.map e.toMonoidHom = W₁ := by
  rcases hA with hA | hA
  · exact ⟨V₁, V₂, Or.inl ⟨rfl, rfl⟩, hA, h₁, h₂⟩
  · exact ⟨V₂, V₁, Or.inr ⟨rfl, rfl⟩, hA, h₂, h₁⟩

/-- Reindex the field cardinality without changing the field or quotient equivalence. -/
def resizeMarking {L : Subgroup G} {q q' : ℕ} (c : ProjectiveMarking L q)
    (h : q = q') : ProjectiveMarking L q' := ⟨c.F, c.card.trans h, c.equivalence⟩

omit [Finite G] in
theorem resizeMarking_diagonal {L : Subgroup G} {q q' : ℕ}
    (c : ProjectiveMarking L q) (h : q = q') (y : G) :
    (resizeMarking c h).Diagonal y ↔ c.Diagonal y := Iff.rfl

/-- The root group forces n=2 and retains the actor on exactly the same quotient marking. -/
theorem rank_and_marking_of_root {L W : Subgroup G} {n : ℕ}
    (c : ProjectiveMarking L (2 ^ n)) (hn : 0 < n) (heven : Even n)
    (hWL : W ≤ L) (hW : Nat.card W = 4)
    (hroot : Matrix.PSL3Even.UnipotentGeometry.projectiveCenter c.F ≤
      (W.subgroupOf L).map (projectiveMap c))
    {y : G} (hy : c.Diagonal y) :
    n = 2 ∧ ∃ h : 2 ^ n = 4, (resizeMarking c h).Diagonal y := by
  have hn2 := parameter_eq_two hn heven (hW ▸ field_size_le_plane c hWL hroot)
  have hq : 2 ^ n = 4 := by rw [hn2]; norm_num
  exact ⟨hn2, hq, hy⟩


/-- A root subgroup, with arbitrary inner choice of projective coordinates. -/
def RootInPlane {L : Subgroup G} {q : ℕ} (c : ProjectiveMarking L q)
    (W : Subgroup G) : Prop :=
  ∃ g : PSL(3,c.F),
    (Matrix.PSL3Even.UnipotentGeometry.projectiveCenter c.F).map
      (MulAut.conj g).toMonoidHom ≤ (W.subgroupOf L).map (projectiveMap c)

theorem field_size_le_of_root {L W : Subgroup G} {q : ℕ}
    (c : ProjectiveMarking L q) (hWL : W ≤ L) (hroot : RootInPlane c W) :
    q ≤ Nat.card W := by
  obtain ⟨g, hg⟩ := hroot
  have hc : Nat.card (Matrix.PSL3Even.UnipotentGeometry.projectiveCenter c.F) = q := by
    rw [Matrix.PSL3Even.UnipotentGeometry.projectiveCenter,
      ← Nat.card_congr (equivMapOfInjective _ _
        (Matrix.PSL3Even.UnipotentGeometry.projective_injective c.F)).toEquiv,
      Matrix.PSL3Even.UnipotentGeometry.card_Z, c.card]
  have h₁ := card_le_of_le hg
  rw [card_map_of_injective (MulAut.conj g).injective, hc] at h₁
  have h₂ := Nat.le_of_dvd (Nat.card_pos (α := W.subgroupOf L))
    ((W.subgroupOf L).card_map_dvd (projectiveMap c))
  rw [Nat.card_congr (subgroupOfEquivOfLe hWL).toEquiv] at h₂
  exact h₁.trans h₂

/-- The parameter deduction does not fix an arbitrary coordinate chart. -/
theorem parameter_eq_two_of_root {L W : Subgroup G} {n : ℕ}
    (c : ProjectiveMarking L (2 ^ n)) (hn : 0 < n) (heven : Even n)
    (hWL : W ≤ L) (hW : Nat.card W = 4) (hroot : RootInPlane c W) : n = 2 :=
  parameter_eq_two hn heven (hW ▸ field_size_le_of_root c hWL hroot)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
