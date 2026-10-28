module
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import CFSG.Quasithin.ChapterB.Section02.RankLifting
public import Theory.ElementaryAbelian.BinaryRankDifference
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Thompson omega-centers and a minimal maximum elementary actor

Balanced source ranks make `U C_A(U)` a maximum elementary subgroup in the
normal subgroup `Q`. The first Thompson omega-centers of `S` and `R` lie in
this replacement. Enlarging the index-two intersection `A ∩ R` by the second
omega-center forces it into `Q`, by minimality of the image of `A`. Equality
of the two relative centralizers then forces that omega-center to centralize
`A`. Residual generation and normalizer invariance give centralization of the
full ambient two-residual.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.1.12(4), printed p.1090, using B.2.3 and B.2.4. The selected subgroup's
mapped core and residual are explicit inputs; the rank enlargement and all
centralization deductions are proved here.
-/

open Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

private theorem omega_thompson_one_le_max (S K : Subgroup G)
    (hK : K ∈ elementaryAbelianMaxSubgroups S) :
    omegaOneCenterAmbient (thompsonJ S 1) ≤ K := by
  by_cases hr : 1 < twoRank S
  · have h := (lemma_B_2_3_2 S (show 0 ≤ 1 by omega) hr).1
    rw [(lemma_B_2_3_2 S (show 0 ≤ 1 by omega) hr).2,
      thompsonJ_zero] at h
    have hh : thompsonAlpha S ≤ K := by
      rw [(lemma_B_2_3_7 S).2]
      exact sInf_le (by rwa [thompsonFamily_zero])
    exact h.trans hh
  · have hJ : thompsonJ S 1 = ⊥ := by
      apply le_antisymm _ bot_le
      apply sSup_le
      intro A hA
      have hc : Nat.card A = 1 := by
        rw [hA.2.2.2]
        simp [Nat.sub_eq_zero_of_le (by omega : twoRank S ≤ 1)]
      exact (Subgroup.card_eq_one.mp hc).le
    rw [hJ]
    intro x hx
    have hx1 := ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1
    exact (show (⊥ : Subgroup G) ≤ K from bot_le) hx1

private theorem twoRank_eq_of_max_contained (S R K : Subgroup G)
    (hRS : R ≤ S) (hK : K ∈ elementaryAbelianMaxSubgroups S) (hKR : K ≤ R) :
    twoRank R = twoRank S := by
  have hK' : K ∈ elementaryAbelianMaxSubgroups R :=
    ⟨hKR, hK.2.1, fun A hAR he => hK.2.2 A (hAR.trans hRS) he⟩
  unfold twoRank
  rw [maxOrder_eq_card_of_mem R K hK', maxOrder_eq_card_of_mem S K hK]

private theorem omega_thompson_one_le_of_max_contained (S R K : Subgroup G)
    (hRS : R ≤ S) (hK : K ∈ elementaryAbelianMaxSubgroups S) (hKR : K ≤ R) :
    omegaOneCenterAmbient (thompsonJ S 1) ≤
      omegaOneCenterAmbient (thompsonJ R 1) := by
  have hr := twoRank_eq_of_max_contained S R K hRS hK hKR
  have hJ : thompsonJ R 1 ≤ thompsonJ S 1 := by
    apply sSup_le
    intro A hA
    exact le_sSup ⟨hA.1.trans hRS, hA.2.1, hr ▸ hA.2.2⟩
  by_cases h1 : 1 < twoRank R
  · rw [← (lemma_B_2_3_2 R (show 1 ≤ 1 by omega) h1).2]
    intro x hx
    obtain ⟨hxJ, hxp, hxc⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hx
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl x
      ⟨hKR (omega_thompson_one_le_max S K hK hx),
        Subgroup.mem_centralizer_iff.mpr (fun a ha => hxc a (hJ ha))⟩ hxp
  · have hJ0 : thompsonJ S 1 = ⊥ := by
      apply le_antisymm _ bot_le
      apply sSup_le
      intro A hA
      exact (Subgroup.card_eq_one.mp (by rw [hA.2.2.2]; simp [Nat.sub_eq_zero_of_le (by omega : twoRank S ≤ 1)])).le
    rw [hJ0]
    intro x hx
    exact (show (⊥ : Subgroup G) ≤ omegaOneCenterAmbient (thompsonJ R 1) from bot_le)
      ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1

private theorem max_of_codim_one_enlargement (S A B D : Subgroup G)
    (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (hBS : B ≤ S) [IsElementaryAbelian 2 B]
    (hDS : D ≤ S) [IsElementaryAbelian 2 D]
    (hDB : D ≤ Subgroup.centralizer (B : Set G))
    (hc : Nat.card B * 2 = Nat.card A) (hne : ¬ D ≤ B) :
    B ⊔ D ∈ elementaryAbelianMaxSubgroups S := by
  have he : IsElementaryAbelian 2 ↥(B ⊔ D) :=
    IsElementaryAbelian.sup_of_le_centralizer hDB
  have hi : B.relIndex (B ⊔ D) ≠ 1 := by
    intro h
    exact hne (le_sup_right.trans (Subgroup.relIndex_eq_one.mp h))
  have hip : 0 < B.relIndex (B ⊔ D) := Nat.pos_of_ne_zero
    (Subgroup.index_ne_zero_of_finite (H := B.subgroupOf (B ⊔ D)))
  have hcard := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) B (B ⊔ D)
    bot_le le_sup_left
  simp only [Subgroup.relIndex_bot_left] at hcard
  refine ⟨sup_le hBS hDS, he, fun C hCS hCe => (hA.2.2 C hCS hCe).trans ?_⟩
  rw [← hc, ← hcard]
  exact Nat.mul_le_mul_left _ (by omega)

/-- The enlargement step in 15.1.12(4), after the rank equality has made
`U C_A(U)` a maximum elementary subgroup inside `Q`. -/
private theorem omega_thompson_one_centralizes_minimal_actor
    (S Q R U A : Subgroup G) [Q.Normal] [U.Normal]
    [IsElementaryAbelian 2 U]
    (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (hmin : ∀ C ∈ elementaryAbelianMaxSubgroups S, ¬ C ≤ Q →
      Q.relIndex A ≤ Q.relIndex C)
    (hQR : Q ≤ R) (hRS : R ≤ S)
    (hidx : R.relIndex A = 2)
    (hK : U ⊔ (A ⊓ Subgroup.centralizer (U : Set G)) ∈
      elementaryAbelianMaxSubgroups S)
    (hKQ : U ⊔ (A ⊓ Subgroup.centralizer (U : Set G)) ≤ Q)
    (hc : U ⊓ Subgroup.centralizer (A : Set G) =
      U ⊓ Subgroup.centralizer (A ⊓ Q : Set G)) :
    omegaOneCenterAmbient (thompsonJ R 1) ≤ Subgroup.centralizer (A : Set G) := by
  let K := U ⊔ (A ⊓ Subgroup.centralizer (U : Set G))
  let D := omegaOneCenterAmbient (thompsonJ R 1)
  let B := A ⊓ R
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (show B ≤ A from inf_le_left)
  let _ : IsElementaryAbelian 2 D := omegaOneCenterAmbient_elementaryAbelian _
  have hKR : K ≤ R := hKQ.trans hQR
  have hKRmax : K ∈ elementaryAbelianMaxSubgroups R :=
    ⟨hKR, hK.2.1, fun C hCR he => hK.2.2 C (hCR.trans hRS) he⟩
  have hDK : D ≤ K := omega_thompson_one_le_max R K hKRmax
  have hDQ : D ≤ Q := hDK.trans hKQ
  have hDS : D ≤ S := hDQ.trans (hQR.trans hRS)
  have hcard : Nat.card B * 2 = Nat.card A := by
    have ht := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (R ⊓ A) A
      bot_le inf_le_right
    rw [Subgroup.inf_relIndex_right, hidx] at ht
    simpa only [Subgroup.relIndex_bot_left, inf_comm R A] using ht
  have hBR : B ∈ thompsonFamily R 1 := by
    apply (mem_thompsonFamily_iff_rank R B 1).mpr
    refine ⟨inf_le_right, inferInstance, ?_⟩
    rw [twoRank_eq_of_max_contained S R K hRS hK hKR]
    unfold twoRank
    rw [maxOrder_eq_card_of_mem S A hA, ← hcard, Nat.log_mul_base Nat.one_lt_two Nat.card_pos.ne']
  have hDB : D ≤ Subgroup.centralizer (B : Set G) := by
    intro d hd
    exact Subgroup.mem_centralizer_iff.mpr (fun b hb =>
      ((mem_omegaOneCenterAmbient_iff _ _).mp hd).2.2 b ((le_sSup hBR) hb))
  by_contra hDA
  have hDnB : ¬ D ≤ B := by
    intro h
    apply hDA
    exact (h.trans inf_le_left).trans
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hF := max_of_codim_one_enlargement S A B D hA
    (inf_le_left.trans hA.1) hDS hDB hcard hDnB
  have hBQ : B ≤ Q := by
    by_contra hn
    have hFn : ¬ B ⊔ D ≤ Q := fun h => hn (le_sup_left.trans h)
    have hminimal := hmin (B ⊔ D) hF hFn
    have hle : Q.relIndex (B ⊔ D) ≤ Q.relIndex B := by
      have hsup : B ⊔ D ≤ Q ⊔ B := sup_le le_sup_right (hDQ.trans le_sup_left)
      have ht := Subgroup.relIndex_le_of_le_right (H := Q) hsup
        (Subgroup.index_ne_zero_of_finite (H := Q.subgroupOf (Q ⊔ B)))
      simpa only [Subgroup.relIndex_sup_left] using ht
    have hi : Q.relIndex B * 2 = Q.relIndex A := by
      simpa only [hidx, inf_of_le_left hQR, inf_comm R A] using
        Subgroup.relIndex_inf_mul_relIndex Q R A
    have hip : 0 < Q.relIndex B := Nat.pos_of_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := Q.subgroupOf B))
    omega
  have hB : B = A ⊓ Q := le_antisymm (le_inf inf_le_left hBQ)
    (inf_le_inf_left A hQR)
  have hDA' : D ≤ Subgroup.centralizer (A : Set G) := by
    intro d hd
    obtain ⟨u, hu, c, hcC, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hDK hd)
    have hcA : c ∈ Subgroup.centralizer (A : Set G) :=
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr
        (inferInstance : IsMulCommutative A)) hcC.1
    have hcB : c ∈ Subgroup.centralizer (B : Set G) :=
      Subgroup.centralizer_le (show B ≤ A from inf_le_left) hcA
    have huB : u ∈ Subgroup.centralizer (B : Set G) := by
      have ht := (Subgroup.centralizer (B : Set G)).mul_mem (hDB hd)
        ((Subgroup.centralizer (B : Set G)).inv_mem hcB)
      simpa using ht
    have huA : u ∈ Subgroup.centralizer (A : Set G) := by
      have ht : u ∈ U ⊓ Subgroup.centralizer (A ⊓ Q : Set G) := ⟨hu, by
        change u ∈ Subgroup.centralizer ((A ⊓ Q : Subgroup G) : Set G)
        rw [← hB]
        exact huB⟩
      rw [← hc] at ht
      exact ht.2
    exact (Subgroup.centralizer (A : Set G)).mul_mem huA hcA
  exact hDA hDA'


private theorem normalizer_le_normalizer_omega_thompson (R : Subgroup G) (i : ℕ) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (omegaOneCenterAmbient (thompsonJ R i) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  change R.map (MulAut.conj g).toMonoidHom = R at hg
  change (omegaOneCenterAmbient (thompsonJ R i)).map (MulAut.conj g).toMonoidHom = _
  rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective,
    ← thompsonJ_map_equiv, hg]

private theorem max_replacement_of_balanced_ranks {W : Type*} [Group W]
    (S Q U A : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hA : A ∈ elementaryAbelianMaxSubgroups S) (hUQ : U ≤ Q) (hQS : Q ≤ S)
    (hkernel : A ⊓ Subgroup.centralizer (U : Set G) ≤ Q)
    (q : G →* W) (hk : q.ker = Subgroup.centralizer (U : Set G))
    (h1 : Nat.log 2 (Nat.card U) - Nat.log 2 (Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G))) =
      2 * Nat.log 2 (Q.relIndex A))
    (h2 : Nat.log 2 (Nat.card U) - Nat.log 2 (Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G))) =
      2 * Nat.log 2 ((Subgroup.centralizer (U : Set G)).relIndex (A ⊓ Q))) :
    U ⊔ (A ⊓ Subgroup.centralizer (U : Set G)) ∈ elementaryAbelianMaxSubgroups S := by
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let _ : IsElementaryAbelian 2 ↥(A ⊓ Q) := IsElementaryAbelian.of_le inf_le_left
  have hCA : A ⊓ Subgroup.centralizer (U : Set G) ≤ A ⊓ Q := le_inf inf_le_left hkernel
  have hi : (A ⊓ Q) ⊓ Subgroup.centralizer (U : Set G) =
      A ⊓ Subgroup.centralizer (U : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_right _ inf_le_left
    · exact le_inf hCA inf_le_right
  have ha := Subgroup.log_card_sub_log_card_eq_log_relIndex A
    (A ⊓ Subgroup.centralizer (U : Set G)) inf_le_left
  have hb := Subgroup.log_card_sub_log_card_eq_log_relIndex A (A ⊓ Q) inf_le_left
  have hab := Subgroup.log_card_sub_log_card_eq_log_relIndex (A ⊓ Q)
    ((A ⊓ Q) ⊓ Subgroup.centralizer (U : Set G)) inf_le_left
  rw [Subgroup.inf_relIndex_left] at ha hb hab
  rw [hi] at hab
  have hc := Nat.log_mono_right (b := 2)
    (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hCA))
  have hd := Nat.log_mono_right (b := 2)
    (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective (show A ⊓ Q ≤ A from inf_le_left)))
  have heq : Nat.log 2 (Nat.card U) - Nat.log 2 (Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G))) =
      Nat.log 2 (Nat.card (A.map q)) := by
    rw [← Subgroup.relIndex_ker, hk]
    omega
  exact (lemma_B_2_4_3 S U A (hUQ.trans hQS) hA q hk heq).1

/-- The source replacement and minimality argument centralizes the full
ambient two-residual. `R` and `L` will be the mapped two-core and two-residual
of the classification-selected subgroup `X`. -/
public theorem omega_thompson_one_centralizes_residual_of_minimal_actor
    {W : Type*} [Group W] (S Q R U A L : Subgroup G) [Q.Normal] [U.Normal]
    [IsElementaryAbelian 2 U] (hS : IsPGroup 2 S)
    (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (hmin : ∀ C ∈ elementaryAbelianMaxSubgroups S, ¬ C ≤ Q → Q.relIndex A ≤ Q.relIndex C)
    (hUQ : U ≤ Q) (hQR : Q ≤ R) (hRS : R ≤ S)
    (hkernel : A ⊓ Subgroup.centralizer (U : Set G) ≤ Q)
    (q : G →* W) (hk : q.ker = Subgroup.centralizer (U : Set G))
    (h1 : Nat.log 2 (Nat.card U) - Nat.log 2 (Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G))) =
      2 * Nat.log 2 (Q.relIndex A))
    (h2 : Nat.log 2 (Nat.card U) - Nat.log 2 (Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G))) =
      2 * Nat.log 2 ((Subgroup.centralizer (U : Set G)).relIndex (A ⊓ Q)))
    (hc : U ⊓ Subgroup.centralizer (A : Set G) = U ⊓ Subgroup.centralizer (A ⊓ Q : Set G))
    (hidx : R.relIndex A = 2) (hLR : L ≤ Subgroup.normalizer (R : Set G))
    (hcomm : L = ⁅L, A⁆) (hgen : L ⊔ S = ⊤) :
    omegaOneCenterAmbient (thompsonJ S 1) ≤ Subgroup.centralizer (pResidual 2 G : Set G) := by
  let K := U ⊔ (A ⊓ Subgroup.centralizer (U : Set G))
  have hK : K ∈ elementaryAbelianMaxSubgroups S :=
    max_replacement_of_balanced_ranks S Q U A hA hUQ (hQR.trans hRS) hkernel q hk h1 h2
  have hKQ : K ≤ Q := sup_le hUQ hkernel
  let E := omegaOneCenterAmbient (thompsonJ S 1)
  let D := omegaOneCenterAmbient (thompsonJ R 1)
  have hED : E ≤ D := omega_thompson_one_le_of_max_contained S R K hRS hK (hKQ.trans hQR)
  have hDA : D ≤ Subgroup.centralizer (A : Set G) :=
    omega_thompson_one_centralizes_minimal_actor S Q R U A hA hmin hQR hRS hidx hK hKQ hc
  have hLD : L ≤ Subgroup.normalizer (D : Set G) :=
    hLR.trans (normalizer_le_normalizer_omega_thompson R 1)
  have hL : L ≤ Subgroup.centralizer (D : Set G) := by
    calc
      L = ⁅L, A⁆ := hcomm
      _ ≤ ⁅L, Subgroup.centralizer (D : Set G)⁆ :=
        Subgroup.commutator_mono le_rfl (Subgroup.le_centralizer_iff.mp hDA)
      _ ≤ Subgroup.centralizer (D : Set G) :=
        Subgroup.le_normalizer_iff_commutator_le_right.mp
          (hLD.trans (Subgroup.normalizer_le_normalizer_centralizer D))
  have hLE : L ≤ Subgroup.centralizer (E : Set G) := hL.trans (Subgroup.centralizer_le hED)
  have hSN : S ≤ Subgroup.normalizer (E : Set G) :=
    S.le_normalizer.trans (normalizer_le_normalizer_omega_thompson S 1)
  have hEN : E.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply top_unique
    rw [← hgen]
    exact sup_le (hLE.trans (Subgroup.centralizer_le_normalizer _)) hSN
  let := hEN
  have hCEgen : Subgroup.centralizer (E : Set G) ⊔ S = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact sup_le_sup hLE le_rfl
  have hres : pResidual 2 G ≤ Subgroup.centralizer (E : Set G) :=
    sInf_le ⟨inferInstance, Subgroup.isPGroup_quotient_of_sup_eq_top _ S hS hCEgen⟩
  exact Subgroup.le_centralizer_iff.mp hres

end CFSG.Quasithin.ChapterB
