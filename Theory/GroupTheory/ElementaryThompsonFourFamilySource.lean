module
public import Theory.GroupTheory.ElementaryThompsonFourFamily
public import Theory.GroupTheory.PGroup.InvariantThompsonPairNormalizer
/-!
# Closing Thompson stability from an invariant four-member family

The source geometry makes both extra members distinct from the invariant
core pair. With [R:S]=2 their stabilizers in R are exactly S. Normalizers of R
preserve the complementary pair, so the source core stabilizer discharges
the four-family count. The same extra-member stabilizer gives the pointwise
kernel for any ambient overgroup whose core stabilizer is R.

Source: Aschbacher–Smith C.6.1, printed p.165.
-/
public section
open Subgroup
namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem count (Q A : Subgroup G) :
    Nat.card ↥(Q ⊓ A) * Q.relIndex A = Nat.card A := by
  simpa only [relIndex_bot_left,inf_relIndex_right] using
    relIndex_mul_relIndex (⊥ : Subgroup G) (Q ⊓ A) A bot_le inf_le_right

private theorem four_extra_distinct (R S Q W P P' : Subgroup G)
    (hf : elementaryAbelianMaxSubgroups R = {Q,W,P,P'})
    (hg : FourFamilyGeometry S Q W P P' (Q ⊓ W)) :
    P ≠ Q ∧ P ≠ W ∧ P' ≠ Q ∧ P' ≠ W ∧ P ≠ P' := by
  have hQ : Q ∈ elementaryAbelianMaxSubgroups R := by rw [hf]; simp
  have hP : P ∈ elementaryAbelianMaxSubgroups R := by rw [hf]; simp
  have hP' : P' ∈ elementaryAbelianMaxSubgroups R := by rw [hf]; simp
  have hcard (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups R) : Nat.card A = Nat.card Q :=
    le_antisymm (hQ.2.2 A hA.1 hA.2.1) (hA.2.2 Q hQ.1 hQ.2.1)
  have hnot (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups R)
      (hi : Q.relIndex A ≤ 2) (he : Q ⊓ A = Q ⊓ W) : False := by
    have hc := count Q A
    rw [he,hcard A hA] at hc
    have hp : 0 < Nat.card (Q ⊓ W : Subgroup G) := Nat.card_pos
    have hh := hg.core_card
    nlinarith
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro he
    apply hnot P' hP' hg.adjacent_right
    simpa only [he] using hg.opposite_second
  · intro he
    exact hnot P hP hg.adjacent_left (he ▸ rfl)
  · intro he
    apply hnot P hP hg.adjacent_left
    simpa only [he,inf_comm P Q] using hg.opposite_second
  · intro he
    exact hnot P' hP' hg.adjacent_right (he ▸ rfl)
  · intro he
    exact hg.cross_ne (by rw [he])

/-- The extra-member stabilizer is S once R/S has order two. -/
theorem four_family_extra_stabilizer (R S Q W P P' : Subgroup G)
    (hf : elementaryAbelianMaxSubgroups R = {Q,W,P,P'})
    (hi : {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} = {Q,W})
    (hg : FourFamilyGeometry S Q W P P' (Q ⊓ W))
    (hSR : S ≤ R) (hidx : S.relIndex R = 2)
    (hn : ∀ A ∈ elementaryAbelianMaxSubgroups R,S ≤ normalizer (A : Set G)) :
    R ⊓ normalizer (P : Set G) = S := by
  have hP : P ∈ elementaryAbelianMaxSubgroups R := by rw [hf]; simp
  have hd := four_extra_distinct R S Q W P P' hf hg
  have hnot : ¬ R ≤ normalizer (P : Set G) := by
    intro hh
    have hp : P ∈ {Q,W} := hi ▸ (show P ∈ {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} from ⟨hP,hh⟩)
    exact (Set.mem_insert_iff.mp hp).elim hd.1 (fun h => hd.2.1 (Set.mem_singleton_iff.mp h))
  let A := R ⊓ normalizer (P : Set G)
  have hSA : S ≤ A := le_inf hSR (hn P hP)
  have hm := relIndex_mul_relIndex S A R hSA inf_le_left
  rw [hidx] at hm
  have hneq : A.relIndex R ≠ 1 := fun he => hnot ((relIndex_eq_one.mp he).trans inf_le_right)
  have hiAR : 0 < A.relIndex R := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hiSA : 0 < S.relIndex A := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have htwo : 2 ≤ A.relIndex R := by omega
  have hle : A ≤ S := relIndex_eq_one.mp (by nlinarith)
  exact le_antisymm hle hSA

private theorem extra_pair_action (R S Q W P P' : Subgroup G)
    (hf : elementaryAbelianMaxSubgroups R = {Q,W,P,P'})
    (hi : {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} = {Q,W})
    (hg : FourFamilyGeometry S Q W P P' (Q ⊓ W))
    (a : G) (ha : a ∈ normalizer (R : Set G)) :
    (P.map (MulAut.conj a).toMonoidHom = P ∧ P'.map (MulAut.conj a).toMonoidHom = P') ∨
    (P.map (MulAut.conj a).toMonoidHom = P' ∧ P'.map (MulAut.conj a).toMonoidHom = P) := by
  have hd := four_extra_distinct R S Q W P P' hf hg
  have hP : P ∈ elementaryAbelianMaxSubgroups R := by rw [hf]; simp
  have hP' : P' ∈ elementaryAbelianMaxSubgroups R := by rw [hf]; simp
  have hinv : {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} = {W,Q} := by
    rw [hi,Set.pair_comm]
  have hback (C : Subgroup G) (hC : C = Q ∨ C = W) :
      C.map (MulAut.conj a⁻¹).toMonoidHom = Q ∨ C.map (MulAut.conj a⁻¹).toMonoidHom = W := by
    rcases hC with hC|hC
    · subst C
      exact Theory.GroupTheory.normalizer_preserves_invariant_maxFamily_pair R Q W hi
        ((normalizer (R : Set G)).inv_mem ha)
    · subst C
      exact (Theory.GroupTheory.normalizer_preserves_invariant_maxFamily_pair R W Q hinv
        ((normalizer (R : Set G)).inv_mem ha)).symm
  have hm (B : Subgroup G) (hB : B ∈ elementaryAbelianMaxSubgroups R) (hBQ : B ≠ Q) (hBW : B ≠ W) :
      B.map (MulAut.conj a).toMonoidHom = P ∨ B.map (MulAut.conj a).toMonoidHom = P' := by
    have hh := (maxFamily_map_injective_iff (MulAut.conj a).toMonoidHom (MulAut.conj a).injective R B).mpr hB
    have heR : R.map (MulAut.conj a).toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp ha
    rw [heR,hf] at hh
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hh
    have hex (C : Subgroup G) (hc : C = Q ∨ C = W) (he : B.map (MulAut.conj a).toMonoidHom = C) : False := by
      have hb : B = C.map (MulAut.conj a⁻¹).toMonoidHom := by
        rw [←he,map_map]
        have hec : (MulAut.conj a⁻¹).toMonoidHom.comp (MulAut.conj a).toMonoidHom = MonoidHom.id G := by
          ext z; simp [MulAut.conj_apply,mul_assoc]
        rw [hec,map_id]
      exact (hback C hc).elim (fun h => hBQ (hb.trans h)) (fun h => hBW (hb.trans h))
    exact hh.elim (fun h => (hex Q (Or.inl rfl) h).elim)
      (fun h => h.elim (fun h => (hex W (Or.inr rfl) h).elim) id)
  have hn : P'.map (MulAut.conj a).toMonoidHom ≠ P.map (MulAut.conj a).toMonoidHom :=
    fun he => hd.2.2.2.2 (map_injective (MulAut.conj a).injective he).symm
  rcases hm P hP hd.1 hd.2.1 with hp|hp
  · exact Or.inl ⟨hp,(hm P' hP' hd.2.2.1 hd.2.2.2.1).resolve_left (fun h => hn (h.trans hp.symm))⟩
  · exact Or.inr ⟨hp,(hm P' hP' hd.2.2.1 hd.2.2.2.1).resolve_right (fun h => hn (h.trans hp.symm))⟩

/-- The four-family source index and core stabilizer discharge the whole count. -/
theorem thompson_stable_of_invariant_four_family (M R S Q W P P' : Subgroup G)
    (hf : elementaryAbelianMaxSubgroups R = {Q,W,P,P'})
    (hinv : {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} = {Q,W})
    (hg : FourFamilyGeometry S Q W P P' (Q ⊓ W))
    (hRM : R ≤ M) (hSR : S ≤ R) (hi : R.relIndex M = 2) (hiS : S.relIndex R = 2)
    (hMS : M ≤ normalizer (R : Set G))
    (hn : ∀ A ∈ elementaryAbelianMaxSubgroups R,S ≤ normalizer (A : Set G))
    (hcontrol : M ⊓ normalizer (Q : Set G) = R) :
    elementaryAbelianMaxJ M = elementaryAbelianMaxJ R := by
  have hQn : Q ∈ elementaryAbelianMaxSubgroups R ∧ R ≤ normalizer (Q : Set G) := by
    change Q ∈ {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)}
    rw [hinv]; exact Set.mem_insert _ _
  have hWn : W ∈ elementaryAbelianMaxSubgroups R ∧ R ≤ normalizer (W : Set G) := by
    change W ∈ {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)}
    rw [hinv]; simp
  have hswap (a : G) (ha : a ∈ M) (har : a ∉ R) :
      Q.map (MulAut.conj a).toMonoidHom = W ∧ W.map (MulAut.conj a).toMonoidHom = Q := by
    have hs (b : G) (hb : b ∈ M) (hbr : b ∉ R) : Q.map (MulAut.conj b).toMonoidHom = W :=
      (Theory.GroupTheory.normalizer_preserves_invariant_maxFamily_pair R Q W hinv (hMS hb)).resolve_left
        (fun he => hbr (hcontrol ▸ (show b ∈ M ⊓ normalizer (Q : Set G) from
          ⟨hb,mem_normalizer_iff_map_conj_eq.mpr he⟩)))
    refine ⟨hs a ha har,?_⟩
    have hai : a⁻¹ ∉ R := fun hh => har (by simpa only [inv_inv] using R.inv_mem hh)
    rw [←hs a⁻¹ (M.inv_mem ha) hai,map_map]
    have he : (MulAut.conj a).toMonoidHom.comp (MulAut.conj a⁻¹).toMonoidHom = MonoidHom.id G := by
      ext z; simp [MulAut.conj_apply,mul_assoc]
    rw [he,map_id]
  have hidx : S.relIndex M ≤ 4 := by
    have hh := relIndex_mul_relIndex S R M hSR hRM
    rw [hiS,hi] at hh
    omega
  exact thompson_stable_of_four_family_geometry M R S Q W P P' (Q ⊓ W) hg hRM hSR hQn.1 hi hidx
    hQn.2 hWn.2 hswap (fun a ha => extra_pair_action R S Q W P P' hf hinv hg a (hMS ha))
    (four_family_extra_stabilizer R S Q W P P' hf hinv hg hSR hiS hn).le

/-- The full overgroup acts on the four-member family with kernel S. -/
theorem four_family_pointwise_kernel (Λ R S Q W P P' : Subgroup G)
    (hf : elementaryAbelianMaxSubgroups R = {Q,W,P,P'})
    (hinv : {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} = {Q,W})
    (hg : FourFamilyGeometry S Q W P P' (Q ⊓ W))
    (hSR : S ≤ R) (hiS : S.relIndex R = 2)
    (hn : ∀ A ∈ elementaryAbelianMaxSubgroups R,S ≤ normalizer (A : Set G))
    (hcontrol : Λ ⊓ normalizer (Q : Set G) = R) :
    ∀ g ∈ Λ,(∀ A ∈ elementaryAbelianMaxSubgroups R,g ∈ normalizer (A : Set G)) ↔ g ∈ S := by
  intro g hgΛ
  constructor
  · intro hfix
    have hQ : Q ∈ elementaryAbelianMaxSubgroups R := by rw [hf]; simp
    have hP : P ∈ elementaryAbelianMaxSubgroups R := by rw [hf]; simp
    have hgR : g ∈ R := hcontrol ▸ (show g ∈ Λ ⊓ normalizer (Q : Set G) from ⟨hgΛ,hfix Q hQ⟩)
    exact (four_family_extra_stabilizer R S Q W P P' hf hinv hg hSR hiS hn) ▸ ⟨hgR,hfix P hP⟩
  · intro hgS A hA
    exact hn A hA hgS
end Stellmacher
