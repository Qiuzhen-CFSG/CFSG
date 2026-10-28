module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Bender
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeExtensionProjectiveModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.LinearThree
public import Theory.Mathieu.M22.TripleCover.Recognition
public import Theory.ElementaryAbelian.PrimeRankCard
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.PerfectCenterFrattini
public import Theory.GroupTheory.PerfectNormalizerLift

/-!
# Central-cover identification for the original Mathieu point residual

A proper full-Sylow local subgroup of order 17280 excludes the binary
special-linear and special-unitary three-dimensional covers. The projective
image in the linear case has order 5760 or 17280, while its actual parabolic
residual is an affine SL₂ group of neither order. Odd-field covers have
two-rank at most two; the alternating covers are too small. Thus a containing
three-cover of two-rank at least four is the concrete triple cover of M₂₂.
All covering kernels survive the comparison with the projective carriers.

Source: Aschbacher–Smith, A.3.6(2), A.3.12 and 8.2.13, printed
pp.43–48 and 722–723. The original marked-cocode application is in
NonFFSourceMathieuM24CoverSieve. The remaining simple containing rows and
full source assembly belong to qt-d-1222-nonff-mathieu.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
open ChapterA.Section03.SourceEmbeddings Chapter1.Section02.LocalModels

private theorem affine_card {F : Type*} [Field F] [Finite F] :
    Nat.card (Matrix.SL2.Affine F) = Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
  change Nat.card (Fin 2 → F) * Nat.card SL(2,F) = _
  rw [Nat.card_fun, Nat.card_fin, GorensteinWalter.sl2_card_formula]
  ring

private theorem not_affine_order (q : ℕ)
    (h : q ^ 3 * (q ^ 2 - 1) = 5760 ∨ q ^ 3 * (q ^ 2 - 1) = 17280) : False := by
  have hq : q ≤ 7 := by
    by_contra! hh
    have h3 : 512 ≤ q ^ 3 := Nat.pow_le_pow_left hh 3
    have h2 : 64 ≤ q ^ 2 := Nat.pow_le_pow_left hh 2
    have hm := Nat.mul_le_mul h3 (show 63 ≤ q ^ 2 - 1 by omega)
    rcases h with h | h <;> omega
  interval_cases q <;> norm_num at h

private theorem central_image_order {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hk : Nat.card f.ker ∣ 3)
    (B : Subgroup G) (hB : Nat.card B = 17280) :
    Nat.card (B.map f) = 5760 ∨ Nat.card (B.map f) = 17280 := by
  let r := f.subgroupMap B
  let j : r.ker →* f.ker := {
    toFun x := ⟨x.val.val,congrArg Subtype.val x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun x : f.ker => (x : G)) h))
  have hd := (card_dvd_of_injective j hj).trans hk
  have he := card_eq_card_quotient_mul_card_subgroup r.ker
  rw [hB,Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective r
    (f.subgroupMap_surjective B)).toEquiv] at he
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with hh | hh
  · rw [hh,mul_one] at he
    exact .inr he.symm
  · rw [hh] at he
    exact .inl (by omega)

/-- A full-Sylow local subgroup of order 17280 cannot lie properly in a
binary projective three-space after a central quotient of order dividing three. -/
theorem not_binary_three_central_image
    {G F : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hne : B ≠ ⊤) (hcard : Nat.card B = 17280)
    (f : G →* PSL(3,F)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center G) (hk : Nat.card f.ker ∣ 3) : False := by
  let : Group.IsSolvable f.ker := Group.isSolvable_of_comm fun x y =>
    Subtype.ext (mem_center_iff.mp (hc y.property) x)
  have hp : B.map f ≠ ⊤ := by
    intro ht
    apply hne
    apply top_unique
    apply le_of_map_le_of_perfect f hc ⊤ B
    rw [ht]
    exact le_top
  have hm := Chapter1.Section02.localCComponents_map_of_solvable_ker hB f
  have horder := central_image_order f hk B hcard
  by_cases hn' : 1 < n
  · obtain ⟨g,hg⟩ := FiveLocalFF.linear_three_local_placement hF hn'
      (S.mapSurjective hf) (B.map f) hm hp
    have hconj := Nat.card_congr ((MulAut.conj g).subgroupMap (B.map f)).toEquiv
    change Nat.card (B.map f) = Nat.card ((B.map f).map (MulAut.conj g).toMonoidHom) at hconj
    rcases hg with hg | hg
    · rw [hg, Nat.card_congr (Matrix.PSL3.LinearThree.pointLocalEquivAffine F).toEquiv,
        affine_card] at hconj
      exact not_affine_order (Nat.card F) (hconj ▸ horder)
    · rw [hg, Nat.card_congr (Matrix.PSL3.LinearThree.lineLocalEquivAffine F).toEquiv,
        affine_card] at hconj
      exact not_affine_order (Nat.card F) (hconj ▸ horder)
  · have hn1 : n = 1 := by omega
    have hd := (B.map f).card_subgroup_dvd_card
    rw [Matrix.PSL3.LinearThree.card_projective F,hF,hn1] at hd
    rcases horder with ho | ho <;> rw [ho] at hd <;> norm_num at hd

/-- Among the genuine central-three-cover rows of A.3.6, the original
residual of order 17280 and rank at least four forces the concrete triple M22. -/
theorem triple_cover_of_local_residual
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hne : B ≠ ⊤) (hcard : Nat.card B = 17280) (hr : 4 ≤ primeRank 2 G)
    (hc : Nat.card (center G) = 3) (hm : ThreeCoverModel G) :
    Nonempty (G ≃* Sporadic.Mathieu.M22TripleCover) := by
  have ht : (⊤ : Subgroup G).IsCComponent :=
    (show IsComponent G ⊤ from ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  cases hm with
  | alternating_six hm =>
    have hd := B.card_subgroup_dvd_card
    have ho := card_eq_card_quotient_mul_card_subgroup (center G)
    rw [Nat.card_congr hm.2.2.some.toEquiv,nat_card_alternatingGroup,hc] at ho
    rw [hcard,ho] at hd
    norm_num [Nat.factorial] at hd
  | alternating_seven hm =>
    have hd := B.card_subgroup_dvd_card
    have ho := card_eq_card_quotient_mul_card_subgroup (center G)
    rw [Nat.card_congr hm.2.2.some.toEquiv,nat_card_alternatingGroup,hc] at ho
    rw [hcard,ho] at hd
    norm_num [Nat.factorial] at hd
  | mathieu hm => exact Sporadic.Mathieu.M22TripleCover.nonempty_mulEquiv hc hm.2.2
  | classical unitary q hq hm =>
    rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
    · cases unitary with
      | false =>
        obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
        let : Fintype F := Fintype.ofFinite F
        let : CharP F 2 := charP_of_card_eq_prime_pow
          (by simpa only [Nat.card_eq_fintype_card] using hF)
        let f := (Matrix.PSL3.projection F).comp e.toMonoidHom
        have hk : f.ker = center G := by
          ext x
          change e x ∈ (Matrix.PSL3.projection F).ker ↔ x ∈ center G
          rw [Matrix.PSL3.projection_ker,mem_center_iff,mem_center_iff]
          constructor
          · intro hx y
            apply e.injective
            simpa only [map_mul] using hx (e y)
          · intro hx y
            obtain ⟨y,rfl⟩ := e.surjective y
            simpa only [map_mul] using congrArg e (hx y)
        exact (not_binary_three_central_image hn hF S B hB hne hcard f
          ((Matrix.PSL3.projection_surjective F).comp e.surjective)
          hk.le (by rw [hk,hc])).elim
      | true =>
        obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
        have he := eq_of_binary_su3_containing_component S hB ht le_top (by omega : 0 < n)
          ⟨F,inferInstance,inferInstance,J,hF,hconj,⟨topEquiv.trans e⟩⟩
        exact (hne he).elim
    · let : Fact q.Prime := ⟨hp⟩
      have hh := odd_three_two_rank ho unitary (Or.inr hm)
      omega

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
