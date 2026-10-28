module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Source


/-!
# Algebra for the two local incidence arguments in MS93 (1.7)

A fixed element has an invariant commutator image; irreducibility kills that
image when the element belongs to a local closure with proper image. Two
neighboring decompositions with disjoint value spaces then propagate
centralization. Relative normality and the three-subgroup lemma extend this
to the generated group. The binary seed evaluation yields generation modulo
its actual centralizer, without assuming a cyclic quotient.

These are conditional group-theoretic steps for Meierfrankenfeld--Stellmacher,
*Pushing up weak BN-pairs of rank two* (1993), pp.847--848. The geometric
premises still have to be constructed from the marked natural modules.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence
open Subgroup
open scoped commutatorElement
universe u
variable {M : Type u} [Group M]

-- Fixed elements have either zero or full pairing image. A proper local image
-- excludes the latter without any normality assumption on the local closure.
theorem fixed_local_centralizes (U W Z C L Y : Subgroup M) [W.Normal]
    (hUW : ⁅U, W⁆ ≤ Z) (hZW : Z ≤ centralizer (W : Set M))
    (hCU : C ≤ U) (hCL : ⁅C, L⁆ ≤ Z)
    (hirr : ∀ D : Subgroup M, D ≤ Z → L ≤ normalizer (D : Set M) → D = ⊥ ∨ D = Z)
    (hproper : ¬ Z ≤ ⁅Y, W⁆) :
    C ⊓ Y ≤ centralizer (W : Set M) := by
  have hWC : ⁅W, C⁆ ≤ Z := by
    rw [commutator_comm]
    exact (commutator_mono hCU le_rfl).trans hUW
  have ht : ⁅⁅C, L⁆, W⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (hCL.trans hZW)
  intro c hc
  by_contra hnc
  have hs := evaluation_surjective W C Z hWC hZW L ht hirr ⟨c, hc.1⟩ hnc
  apply hproper
  intro z hz
  obtain ⟨w, hw⟩ := hs ⟨z, hz⟩
  have hv : ⁅c, (w : M)⁆ = z := congrArg Subtype.val hw
  rw [← hv]
  exact commutator_mem_commutator hc.2 w.property

-- Commutator bounds extend across a join inside U, by a genuine evaluation
-- homomorphism; the bounding subgroup need not be normal in the ambient group.
theorem pairing_sup_bound (U W Z A B D : Subgroup M)
    (hUW : ⁅U, W⁆ ≤ Z) (hZU : Z ≤ centralizer (U : Set M))
    (hAU : A ≤ U) (hBU : B ≤ U)
    (hA : ⁅A, W⁆ ≤ D) (hB : ⁅B, W⁆ ≤ D) : ⁅A ⊔ B, W⁆ ≤ D := by
  apply commutator_le.mpr
  intro y hy w hw
  let f := evaluation U W Z hUW hZU ⟨w, hw⟩
  let K := ((D.subgroupOf Z).comap f).map U.subtype
  have hAK : A ≤ K := by
    intro a ha
    refine ⟨⟨a, hAU ha⟩, ?_, rfl⟩
    change ⁅w, a⁆ ∈ D
    rw [commutator_comm] at hA
    exact hA (commutator_mem_commutator hw ha)
  have hBK : B ≤ K := by
    intro b hb
    refine ⟨⟨b, hBU hb⟩, ?_, rfl⟩
    change ⁅w, b⁆ ∈ D
    rw [commutator_comm] at hB
    exact hB (commutator_mem_commutator hw hb)
  obtain ⟨v, hv, he⟩ := (sup_le hAK hBK) hy
  change ⁅w, (v : M)⁆ ∈ D at hv
  change (v : M) = y at he
  rw [he] at hv
  simpa only [commutatorElement_inv] using D.inv_mem hv

-- The two alternative neighboring decompositions force centralization.
theorem centralizes_of_two_decompositions (U W Z X Y A B C D E : Subgroup M)
    (hUW : ⁅U, W⁆ ≤ Z) (hZU : Z ≤ centralizer (U : Set M))
    (hXU : X ≤ U) (hAU : A ≤ U) (hBU : B ≤ U) (hCU : C ≤ U)
    (hYA : Y ≤ (X ⊔ A) ⊔ C) (hYB : Y ≤ (X ⊔ B) ⊔ C)
    (hA : ⁅A, W⁆ ≤ D) (hB : ⁅B, W⁆ ≤ E)
    (hC : C ≤ centralizer (W : Set M)) (hDE : D ⊓ E = ⊥) :
    W ⊓ centralizer (X : Set M) ≤ centralizer (Y : Set M) := by
  let T := W ⊓ centralizer (X : Set M)
  have hXT : ⁅X, T⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  have hCT : ⁅C, T⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hC.trans (centralizer_le inf_le_left))
  have hUT : ⁅U, T⁆ ≤ Z := (commutator_mono le_rfl inf_le_left).trans hUW
  have hYD : ⁅Y, T⁆ ≤ D := (commutator_mono hYA le_rfl).trans
    (pairing_sup_bound U T Z (X ⊔ A) C D hUT hZU (sup_le hXU hAU) hCU
      (pairing_sup_bound U T Z X A D hUT hZU hXU hAU
        (hXT.le.trans bot_le) ((commutator_mono le_rfl inf_le_left).trans hA))
      (hCT.le.trans bot_le))
  have hYE : ⁅Y, T⁆ ≤ E := (commutator_mono hYB le_rfl).trans
    (pairing_sup_bound U T Z (X ⊔ B) C E hUT hZU (sup_le hXU hBU) hCU
      (pairing_sup_bound U T Z X B E hUT hZU hXU hBU
        (hXT.le.trans bot_le) ((commutator_mono le_rfl inf_le_left).trans hB))
      (hCT.le.trans bot_le))
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [commutator_comm]
  exact bot_unique (hDE ▸ le_inf hYD hYE)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence
open Subgroup
open scoped commutatorElement
universe u
variable {M : Type u} [Group M]

theorem normalizes_centralizer (P X : Subgroup M)
    (h : P ≤ normalizer (X : Set M)) :
    P ≤ normalizer (centralizer (X : Set M) : Set M) :=
  h.trans (le_normalizer_of_normal_subgroupOf (Subgroup.centralizer_le_normalizer _))

theorem localGenerated_normalized (P X : Subgroup M) :
    P ≤ normalizer (localGenerated P X : Set M) := by
  have h := (normalClosure (X.subgroupOf P : Set P)).le_normalizer_map P.subtype
  intro p hp
  apply h
  exact ⟨⟨p, hp⟩, by rw [normalizer_eq_top]; trivial, rfl⟩

theorem centralizer_propagation (P R X W : Subgroup M) [W.Normal]
    (hgen : P ⊔ R = ⊤) (hXP : P ≤ normalizer (X : Set M))
    (hXR : X ≤ R)
    (hstep : W ⊓ centralizer (X : Set M) ≤
      centralizer (localGenerated R X : Set M)) :
    W ⊓ centralizer (X : Set M) = W ⊓ centralizer (generated X : Set M) := by
  let T := W ⊓ centralizer (X : Set M)
  have he : T = W ⊓ centralizer (localGenerated R X : Set M) := by
    apply le_antisymm (le_inf inf_le_left hstep)
    exact inf_le_inf_left W (centralizer_le (le_localGenerated R X hXR))
  have hPT : P ≤ normalizer (T : Set M) :=
    (le_inf le_normalizer_of_normal (normalizes_centralizer P X hXP)).trans
      inf_normalizer_le_normalizer_inf
  have hRT : R ≤ normalizer (T : Set M) := by
    rw [he]
    exact (le_inf le_normalizer_of_normal
      (normalizes_centralizer R _ (localGenerated_normalized R X))).trans
        inf_normalizer_le_normalizer_inf
  have hT : T.Normal := normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le hPT hRT))
  let := hT
  have hXT : X ≤ centralizer (T : Set M) := by
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  have hUT : generated X ≤ centralizer (T : Set M) := normalClosure_le_normal hXT
  apply le_antisymm
  · refine le_inf inf_le_left ?_
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hUT
  · exact inf_le_inf_left W (centralizer_le le_normalClosure)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence
open Subgroup
open scoped commutatorElement
universe u
variable {M : Type u} [Group M]

theorem triple_of_seed (U W X A L C : Subgroup M) [U.Normal] [W.Normal]
    (hWX : W ⊓ centralizer (X : Set M) ≤ centralizer (U : Set M))
    (hXW : ⁅X, W⁆ ≤ centralizer (A : Set M))
    (hXA : ⁅X, A⁆ ≤ C) (hCW : C ≤ centralizer (W : Set M))
    (hLA : L ≤ normalClosure (A : Set M)) :
    ⁅⁅W, L⁆, U⁆ = ⊥ := by
  have hAXW : ⁅⁅A, X⁆, W⁆ = ⊥ := by
    rw [commutator_comm A X]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hXA.trans hCW)
  have hXWA : ⁅⁅X, W⁆, A⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hXW
  have hWAX : ⁅⁅W, A⁆, X⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate hAXW hXWA
  have hWA : ⁅W, A⁆ ≤ centralizer (U : Set M) :=
    (le_inf (commutator_le_left W A)
      (commutator_eq_bot_iff_le_centralizer.mp hWAX)).trans hWX
  exact commutator_eq_bot_iff_le_centralizer.mpr
    ((commutator_mono le_rfl hLA).trans
      (commutator_normalClosure_le_of_normal W A (centralizer (U : Set M)) hWA))

theorem fixed_centralizes_of_triple (U W Z C L : Subgroup M)
    (hCU : C ≤ U) (hUW : ⁅U, W⁆ ≤ Z)
    (hCL : ⁅C, L⁆ ≤ Z) (hZW : Z ≤ centralizer (W : Set M))
    (htriple : ⁅⁅W, L⁆, U⁆ = ⊥) (hfixed : Z ⊓ centralizer (L : Set M) = ⊥) :
    ⁅C, W⁆ = ⊥ := by
  have hWLC : ⁅⁅W, L⁆, C⁆ = ⊥ :=
    bot_unique ((commutator_mono le_rfl hCU).trans htriple.le)
  have hLCW : ⁅⁅L, C⁆, W⁆ = ⊥ := by
    rw [commutator_comm L C]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hCL.trans hZW)
  have hCWL : ⁅⁅C, W⁆, L⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate hWLC hLCW
  exact bot_unique (hfixed ▸ le_inf ((commutator_mono hCU le_rfl).trans hUW)
    (commutator_eq_bot_iff_le_centralizer.mp hCWL))

-- A map with at most two values is generated modulo its kernel by any element
-- outside its kernel. This is used only after constructing the seed evaluation.
theorem binary_map_generation {D : Type*} [Group D] [Finite D]
    (W K : Subgroup M) (f : W →* D) (hcard : Nat.card D ≤ 2)
    (hker : ∀ w : W, f w = 1 ↔ (w : M) ∈ K)
    (w : W) (hw : (w : M) ∉ K) : W ≤ zpowers (w : M) ⊔ K := by
  classical
  let := Fintype.ofFinite D
  have hfw : f w ≠ 1 := fun h => hw ((hker w).mp h)
  have htwo (v : W) : f v = 1 ∨ f v = f w := by
    by_contra h
    push Not at h
    have hh : 2 < Fintype.card D := Fintype.two_lt_card_iff.mpr
      ⟨f v, 1, f w, h.1, h.2, hfw.symm⟩
    rw [Nat.card_eq_fintype_card] at hcard
    omega
  intro v hv
  rcases htwo ⟨v, hv⟩ with h | h
  · exact (show K ≤ zpowers (w : M) ⊔ K from le_sup_right) ((hker ⟨v, hv⟩).mp h)
  · have hk : (w : M)⁻¹ * v ∈ K := (hker (w⁻¹ * ⟨v, hv⟩)).mp (by
      simp only [map_mul, map_inv, h, inv_mul_cancel])
    have hh := (zpowers (w : M) ⊔ K).mul_mem
      ((show zpowers (w : M) ≤ zpowers (w : M) ⊔ K from le_sup_left) (mem_zpowers (w : M)))
      ((show K ≤ zpowers (w : M) ⊔ K from le_sup_right) hk)
    simpa only [mul_inv_cancel_left] using hh

theorem binary_seed_generation [Finite M]
    (U W Z X C D : Subgroup M)
    (hZW : Z ≤ centralizer (W : Set M)) (hDZ : D ≤ Z)
    (hXU : X ≤ U) (hXW : ⁅X, W⁆ ≤ D) (hcard : Nat.card D ≤ 2)
    (hCW : C ≤ centralizer (W : Set M))
    (hprop : W ⊓ centralizer (X : Set M) ≤ centralizer (U : Set M))
    (x : X) (hspan : X ≤ zpowers (x : M) ⊔ C)
    (w : W) (hw : (w : M) ∉ centralizer (U : Set M)) :
    W ≤ zpowers (w : M) ⊔ centralizer (U : Set M) := by
  let f : W →* D := centralCommutatorHom W D
    (hDZ.trans hZW)
    (x : M) (fun v hv => hXW (commutator_mem_commutator x.property hv))
  exact binary_map_generation W (centralizer (U : Set M)) f hcard (by
    intro v
    change (⟨⁅(x : M), (v : M)⁆, _⟩ : D) = 1 ↔ _
    rw [Subtype.ext_iff]
    constructor
    · intro hv
      have hx : (x : M) ∈ centralizer ({(v : M)} : Set M) :=
        mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp hv)
      have hC : C ≤ centralizer ({(v : M)} : Set M) := by
        intro c hc
        exact mem_centralizer_singleton_iff.mpr (hCW hc v v.property).symm
      have hX := hspan.trans (sup_le (zpowers_le.mpr hx) hC)
      exact hprop ⟨v.property, fun a ha =>
        (mem_centralizer_singleton_iff.mp (hX ha))⟩
    · intro hv
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hv x (hXU x.property))) w hw

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence
open Subgroup
open scoped commutatorElement
universe u
variable {M : Type u} [Group M]

theorem pairing_iSup_bound {ι : Sort*} (U W Z D : Subgroup M) (A : ι → Subgroup M)
    (hUW : ⁅U, W⁆ ≤ Z) (hZU : Z ≤ centralizer (U : Set M))
    (hAU : ∀ i, A i ≤ U) (hA : ∀ i, ⁅A i, W⁆ ≤ D) : ⁅⨆ i, A i, W⁆ ≤ D := by
  apply commutator_le.mpr
  intro y hy w hw
  let f := evaluation U W Z hUW hZU ⟨w, hw⟩
  let K := ((D.subgroupOf Z).comap f).map U.subtype
  have hAK : ∀ i, A i ≤ K := by
    intro i a ha
    refine ⟨⟨a, hAU i ha⟩, ?_, rfl⟩
    change ⁅w, a⁆ ∈ D
    have h := hA i
    rw [commutator_comm] at h
    exact h (commutator_mem_commutator hw ha)
  obtain ⟨v, hv, he⟩ := (iSup_le hAK) hy
  change ⁅w, (v : M)⁆ ∈ D at hv
  change (v : M) = y at he
  rw [he] at hv
  simpa only [commutatorElement_inv] using D.inv_mem hv

theorem commutator_conjugate_left (A W D : Subgroup M) [W.Normal]
    (h : ⁅A, W⁆ ≤ D) (g : M) :
    ⁅A.map (MulAut.conj g).toMonoidHom, W⁆ ≤ D.map (MulAut.conj g).toMonoidHom := by
  have he : W.map (MulAut.conj g).toMonoidHom = W :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  rw [← he, ← map_commutator]
  exact map_mono h

theorem conjugate_le_normal (A U : Subgroup M) [U.Normal] (hAU : A ≤ U) (g : M) :
    A.map (MulAut.conj g).toMonoidHom ≤ U := by
  rintro _ ⟨a, ha, rfl⟩
  exact (inferInstance : U.Normal).conj_mem _ (hAU ha) g

theorem localGenerated_le_of_normalizes (P A N : Subgroup M)
    (hPN : P ≤ normalizer (N : Set M)) (hAN : A ≤ N) : localGenerated P A ≤ N := by
  let : (N.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hPN
  apply map_le_iff_le_comap.mpr
  change normalClosure (A.subgroupOf P : Set P) ≤ N.subgroupOf P
  exact normalClosure_le_normal (fun a ha => hAN ha)

theorem localGenerated_commutator_bound (P A W N : Subgroup M) [N.Normal]
    (hPW : P ≤ normalizer (W : Set M)) (hAW : ⁅A, W⁆ ≤ N) :
    ⁅localGenerated P A, W⁆ ≤ N := by
  let q := QuotientGroup.mk' N
  let K := (centralizer (W.map q : Set (M ⧸ N))).comap q
  have hAK : A ≤ K := by
    apply map_le_iff_le_comap.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator, Subgroup.map_eq_bot_iff]
    simpa only [q, QuotientGroup.ker_mk'] using hAW
  have hPq : P.map q ≤ normalizer (W.map q : Set (M ⧸ N)) :=
    (map_mono hPW).trans (W.le_normalizer_map q)
  have hPK : P ≤ normalizer (K : Set M) := by
    rw [← comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective N)]
    exact map_le_iff_le_comap.mp (normalizes_centralizer _ _ hPq)
  have hlocal := localGenerated_le_of_normalizes P A K hPK hAK
  have hzero : (⁅localGenerated P A, W⁆).map q = ⊥ := by
    rw [map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr (map_le_iff_le_comap.mpr hlocal)
  simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hzero


/-- Restricted centralizers commute with actual group isomorphisms. -/
theorem map_restricted_centralizer (W X : Subgroup M) (a : M ≃* M) :
    (W ⊓ centralizer (X : Set M)).map a.toMonoidHom =
      W.map a.toMonoidHom ⊓ centralizer (X.map a.toMonoidHom : Set M) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨mem_map_of_mem _ hv.1, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    change a x * a v = a v * a x
    simpa only [map_mul] using congrArg a (hv.2 x hx)
  · rintro w ⟨⟨v, hv, rfl⟩, hc⟩
    refine ⟨v, ⟨hv, ?_⟩, rfl⟩
    intro x hx
    apply a.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using hc (a x) (mem_map_of_mem _ hx)

/-- Conjugate a bound with its seed centralizer restriction retained. -/
theorem commutator_conjugate_restricted (Y W X D : Subgroup M) [W.Normal]
    (h : ⁅Y, W ⊓ centralizer (X : Set M)⁆ ≤ D) (g : M) :
    ⁅Y.map (MulAut.conj g).toMonoidHom,
      W ⊓ centralizer (X.map (MulAut.conj g).toMonoidHom : Set M)⁆ ≤
        D.map (MulAut.conj g).toMonoidHom := by
  have he : W.map (MulAut.conj g).toMonoidHom = W :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  have hc := map_restricted_centralizer W X (MulAut.conj g)
  rw [he] at hc
  rw [← hc, ← map_commutator]
  exact map_mono h

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence
