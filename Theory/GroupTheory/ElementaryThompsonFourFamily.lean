module
public import Theory.GroupTheory.ElementaryThompsonPairExtension
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Thompson stability from a four-member elementary square

The counting proof keeps the action on both opposite pairs. If an elementary
subgroup moves an extra member, its Baumann intersection lies in the common
intersection. If it stabilizes that member, the adjacent index bound forces
it to centralize the common intersection. Two distinct crossing commutator
lines rule out the surviving automorphism. This avoids asserting that every
outside involution has only central fixed points.

Source application: Aschbacher–Smith C.6.1, printed p.165.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem count_four (Q A : Subgroup G) :
    Nat.card ↥(Q ⊓ A) * Q.relIndex A = Nat.card A := by
  simpa only [relIndex_bot_left,inf_relIndex_right] using
    relIndex_mul_relIndex (⊥ : Subgroup G) (Q ⊓ A) A bot_le inf_le_right

/-- The four-family Thompson count uses the stabilizer of an extra member,
rather than a blanket assertion about fixed points of every outside element. -/
theorem thompson_stable_of_four_family (M R S Q Q' P P' I : Subgroup G)
    (hRM : R ≤ M) (hSR : S ≤ R) (hQ : Q ∈ elementaryAbelianMaxSubgroups R)
    (hi : R.relIndex M = 2) (hidx : S.relIndex M ≤ 4)
    (hcover : ∀ B : Subgroup G, B ≤ S → IsElementaryAbelian 2 B →
      B ≤ Q ∨ B ≤ Q' ∨ B ≤ P ∨ B ≤ P')
    (hQQ' : Q ⊓ Q' = I) (hPP' : P ⊓ P' = I)
    (hQP : Q.relIndex P ≤ 2) (hQP' : Q.relIndex P' ≤ 2)
    (hlarge : 4 * Nat.card I ≤ Nat.card Q)
    (hswap : ∀ a ∈ M, a ∉ R →
      Q.map (MulAut.conj a).toMonoidHom = Q' ∧
      Q'.map (MulAut.conj a).toMonoidHom = Q)
    (hpair : ∀ a ∈ M,
      (P.map (MulAut.conj a).toMonoidHom = P ∧
        P'.map (MulAut.conj a).toMonoidHom = P') ∨
      (P.map (MulAut.conj a).toMonoidHom = P' ∧
        P'.map (MulAut.conj a).toMonoidHom = P))
    (hRP : R ⊓ normalizer (P : Set G) ≤ S)
    (hRI : R ⊓ centralizer (I : Set G) ≤ S)
    (hMIP : (M ⊓ centralizer (I : Set G)) ⊓ normalizer (P : Set G) ≤ S) :
    elementaryAbelianMaxJ M = elementaryAbelianMaxJ R := by
  have hJ : elementaryAbelianMaxJ M ≤ R := by
    apply sSup_le
    intro A hA
    let : IsElementaryAbelian 2 A := hA.2.1
    by_contra hn
    obtain ⟨a,ha,har⟩ := SetLike.not_le_iff_exists.mp hn
    let B := A ⊓ S
    have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le inf_le_left
    have hcardQ : Nat.card Q ≤ Nat.card A := hA.2.2 Q (hQ.1.trans hRM) hQ.2.1
    have hcount4 : Nat.card A ≤ 4 * Nat.card B := by
      have hm : S.relIndex M ≠ 0 := index_ne_zero_of_finite
      have hidxA := (relIndex_le_of_le_right (H := S) hA.1 hm).trans hidx
      have hc := count_four S A
      rw [inf_comm S A] at hc
      dsimp only [B]
      nlinarith
    have hcount2 (hE : A ⊓ R ≤ S) : Nat.card A ≤ 2 * Nat.card B := by
      have hidxA := relIndex_le_of_le_right (H := R) hA.1 (by omega : R.relIndex M ≠ 0)
      rw [hi] at hidxA
      have hc := count_four R A
      rw [inf_comm R A] at hc
      have heq : A ⊓ R = B := le_antisymm (le_inf inf_le_left hE) (inf_le_inf_left A hSR)
      rw [heq] at hc
      nlinarith
    have hfixed (b : G) (hb : b ∈ A) (z : G) (hz : z ∈ B) :
        (MulAut.conj b).toMonoidHom z = z := by
      change b * z * b⁻¹ = z
      rw [setLike_mul_comm hb hz.1,mul_inv_cancel_right]
    have hmove {C D : Subgroup G} (hBC : B ≤ C) {b : G} (hb : b ∈ A)
        (hm : C.map (MulAut.conj b).toMonoidHom = D) : B ≤ C ⊓ D := by
      intro z hz
      exact ⟨hBC hz,hm ▸ mem_map.mpr ⟨z,hBC hz,hfixed b hb z hz⟩⟩
    have hAI (hIB : I ≤ B) : A ≤ centralizer (I : Set G) := by
      intro z hz i hi
      exact congrArg Subtype.val (hA.2.1.is_comm.comm (⟨i,(hIB hi).1⟩ : A) ⟨z,hz⟩)
    have hfalse (hBI : B ≤ I) : False := by
      have hcardB := card_le_of_le hBI
      have heq : B = I := eq_of_le_of_card_ge hBI (by nlinarith)
      have hE : A ⊓ R ≤ S := by
        rintro z ⟨hzA,hzR⟩
        exact hRI ⟨hzR,hAI heq.ge hzA⟩
      have hc := hcount2 hE
      have hp : 0 < Nat.card I := Nat.card_pos
      nlinarith
    have hsw := hswap a (hA.1 ha) har
    by_cases hAP : A ≤ normalizer (P : Set G)
    · have hE : A ⊓ R ≤ S := by
        rintro z ⟨hzA,hzR⟩
        exact hRP ⟨hzR,hAP hzA⟩
      have hcA := hcount2 hE
      have hQI : B ⊓ Q ≤ I := by
        rintro z ⟨hzB,hzQ⟩
        rw [←hQQ']
        exact ⟨hzQ,hsw.1 ▸ mem_map.mpr ⟨z,hzQ,hfixed a ha z hzB⟩⟩
      have hbound (C : Subgroup G) (hBC : B ≤ C) (hc : Q.relIndex C ≤ 2) :
          Nat.card B ≤ 2 * Nat.card (B ⊓ Q : Subgroup G) := by
        have hb := (relIndex_le_of_le_right (H := Q) hBC index_ne_zero_of_finite).trans hc
        have hh := count_four Q B
        rw [inf_comm Q B] at hh
        nlinarith
      have hb : Nat.card B ≤ 2 * Nat.card (B ⊓ Q : Subgroup G) := by
        rcases hcover B inf_le_right hB with hBQ | hBQ' | hBP | hBP'
        · exact (hfalse ((hmove hBQ ha hsw.1).trans hQQ'.le)).elim
        · exact (hfalse ((hmove hBQ' ha hsw.2).trans (inf_comm Q' Q ▸ hQQ'.le))).elim
        · exact hbound P hBP hQP
        · exact hbound P' hBP' hQP'
      have hcI := card_le_of_le hQI
      have heq : B ⊓ Q = I := eq_of_le_of_card_ge hQI (by nlinarith)
      have hIB : I ≤ B := heq.ge.trans inf_le_left
      have haS := hMIP ⟨⟨hA.1 ha,hAI hIB ha⟩,hAP ha⟩
      exact har (hSR haS)
    · obtain ⟨b,hb,hbn⟩ := SetLike.not_le_iff_exists.mp hAP
      have hbmove := (hpair b (hA.1 hb)).resolve_left (fun hf =>
        hbn (mem_normalizer_iff_map_conj_eq.mpr hf.1))
      apply hfalse
      rcases hcover B inf_le_right hB with hBQ | hBQ' | hBP | hBP'
      · exact (hmove hBQ ha hsw.1).trans hQQ'.le
      · exact (hmove hBQ' ha hsw.2).trans (inf_comm Q' Q ▸ hQQ'.le)
      · exact (hmove hBP hb hbmove.1).trans hPP'.le
      · exact (hmove hBP' hb hbmove.2).trans (inf_comm P' P ▸ hPP'.le)
  have h₁ := elementaryAbelianMaxOrder_le_and_j_le_of_eq R M hRM
  have h₂ := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le M R hJ
  have he := le_antisymm h₁.1 h₂.1
  exact le_antisymm (h₂.2 he.symm) (h₁.2 he)
end Stellmacher
namespace Subgroup
variable {G : Type*} [Group G]
private theorem crossed_line_fixed {I Z : Subgroup G} (hZI : Z ≤ I) {a : G}
    (ha : a ∈ centralizer (I : Set G)) : Z.map (MulAut.conj a).toMonoidHom = Z := by
  apply le_antisymm
  · rintro _ ⟨z,hz,rfl⟩
    change a * z * a⁻¹ ∈ Z
    rw [←ha z (hZI hz),mul_inv_cancel_right]
    exact hz
  · intro z hz
    refine ⟨z,hz,?_⟩
    change a * z * a⁻¹ = z
    rw [←ha z (hZI hz),mul_inv_cancel_right]

/-- Crossing commutator lines detect the automorphisms fixing one opposite
pair while exchanging the other. Such an actor cannot fix the whole common
intersection pointwise. -/
theorem not_centralizes_of_crossed_commutators (Q Q' P P' I : Subgroup G)
    (hZI : ⁅Q ⊓ P,Q' ⊓ P'⁆ ≤ I)
    (hne : ⁅Q ⊓ P,Q' ⊓ P'⁆ ≠ ⁅Q ⊓ P',Q' ⊓ P⁆)
    (a : G)
    (hq : Q.map (MulAut.conj a).toMonoidHom = Q')
    (hq' : Q'.map (MulAut.conj a).toMonoidHom = Q)
    (hp : P.map (MulAut.conj a).toMonoidHom = P)
    (hp' : P'.map (MulAut.conj a).toMonoidHom = P') :
    a ∉ centralizer (I : Set G) := by
  intro ha
  have hz := crossed_line_fixed hZI ha
  rw [map_commutator,map_inf _ _ _ (MulAut.conj a).injective,
    map_inf _ _ _ (MulAut.conj a).injective,hq,hq',hp,hp',commutator_comm] at hz
  exact hne hz.symm

theorem not_centralizes_of_crossed_commutators' (Q Q' P P' I : Subgroup G)
    (hZI : ⁅Q ⊓ P,Q' ⊓ P'⁆ ≤ I)
    (hne : ⁅Q ⊓ P,Q' ⊓ P'⁆ ≠ ⁅Q ⊓ P',Q' ⊓ P⁆)
    (a : G)
    (hq : Q.map (MulAut.conj a).toMonoidHom = Q)
    (hq' : Q'.map (MulAut.conj a).toMonoidHom = Q')
    (hp : P.map (MulAut.conj a).toMonoidHom = P')
    (hp' : P'.map (MulAut.conj a).toMonoidHom = P) :
    a ∉ centralizer (I : Set G) := by
  intro ha
  have hz := crossed_line_fixed hZI ha
  rw [map_commutator,map_inf _ _ _ (MulAut.conj a).injective,
    map_inf _ _ _ (MulAut.conj a).injective,hq,hq',hp,hp'] at hz
  exact hne hz.symm
end Subgroup
namespace Stellmacher
variable {G : Type*} [Group G]
/-- The elementary square and its two distinguished crossing commutator lines. -/
structure FourFamilyGeometry (S Q Q' P P' I : Subgroup G) : Prop where
  cover : ∀ B : Subgroup G, B ≤ S → IsElementaryAbelian 2 B →
    B ≤ Q ∨ B ≤ Q' ∨ B ≤ P ∨ B ≤ P'
  opposite_first : Q ⊓ Q' = I
  opposite_second : P ⊓ P' = I
  adjacent_left : Q.relIndex P ≤ 2
  adjacent_right : Q.relIndex P' ≤ 2
  core_card : 4 * Nat.card I ≤ Nat.card Q
  first_cross_le : ⁅Q ⊓ P,Q' ⊓ P'⁆ ≤ I
  cross_ne : ⁅Q ⊓ P,Q' ⊓ P'⁆ ≠ ⁅Q ⊓ P',Q' ⊓ P⁆

variable [Finite G]
theorem thompson_stable_of_four_family_geometry (M R S Q Q' P P' I : Subgroup G)
    (geometry : FourFamilyGeometry S Q Q' P P' I)
    (hRM : R ≤ M) (hSR : S ≤ R) (hQ : Q ∈ elementaryAbelianMaxSubgroups R)
    (hi : R.relIndex M = 2) (hidx : S.relIndex M ≤ 4)
    (hRQ : R ≤ normalizer (Q : Set G)) (hRQ' : R ≤ normalizer (Q' : Set G))
    (hswap : ∀ a ∈ M, a ∉ R →
      Q.map (MulAut.conj a).toMonoidHom = Q' ∧
      Q'.map (MulAut.conj a).toMonoidHom = Q)
    (hpair : ∀ a ∈ M,
      (P.map (MulAut.conj a).toMonoidHom = P ∧
        P'.map (MulAut.conj a).toMonoidHom = P') ∨
      (P.map (MulAut.conj a).toMonoidHom = P' ∧
        P'.map (MulAut.conj a).toMonoidHom = P))
    (hRP : R ⊓ normalizer (P : Set G) ≤ S) :
    elementaryAbelianMaxJ M = elementaryAbelianMaxJ R := by
  have hPP : P ≠ P' := by
    intro he
    apply geometry.cross_ne
    rw [he]
  have hRI : R ⊓ centralizer (I : Set G) ≤ S := by
    rintro a ⟨haR,haI⟩
    by_contra haS
    have hamove := (hpair a (hRM haR)).resolve_left (fun hh =>
      haS (hRP ⟨haR,mem_normalizer_iff_map_conj_eq.mpr hh.1⟩))
    exact not_centralizes_of_crossed_commutators' Q Q' P P' I geometry.first_cross_le
      geometry.cross_ne a (mem_normalizer_iff_map_conj_eq.mp (hRQ haR))
      (mem_normalizer_iff_map_conj_eq.mp (hRQ' haR)) hamove.1 hamove.2 haI
  have hMIP : (M ⊓ centralizer (I : Set G)) ⊓ normalizer (P : Set G) ≤ S := by
    rintro a ⟨⟨haM,haI⟩,haP⟩
    by_cases haR : a ∈ R
    · exact hRP ⟨haR,haP⟩
    · have hs := hswap a haM haR
      have hfix := mem_normalizer_iff_map_conj_eq.mp haP
      have hp := (hpair a haM).resolve_right (fun hh => hPP (hfix.symm.trans hh.1))
      exact (not_centralizes_of_crossed_commutators Q Q' P P' I geometry.first_cross_le
        geometry.cross_ne a hs.1 hs.2 hp.1 hp.2 haI).elim
  exact thompson_stable_of_four_family M R S Q Q' P P' I hRM hSR hQ hi hidx
    geometry.cover geometry.opposite_first geometry.opposite_second geometry.adjacent_left
    geometry.adjacent_right geometry.core_card hswap hpair hRP hRI hMIP
end Stellmacher
