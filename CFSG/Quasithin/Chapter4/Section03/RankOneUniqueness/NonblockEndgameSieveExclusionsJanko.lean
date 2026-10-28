module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveContracts
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne
public import Theory.SpecificGroups.Janko1.PerfectSubgroupCore
public import Theory.GroupTheory.PerfectSubgroupAutomorphismFixer
public import Theory.GroupTheory.NormalPrimeOrder
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.GroupTheory.InnerImageGeometry
public import GorensteinWalter.PSL2Center
public import Theory.GroupTheory.PrimeCentralizerExclusion

/-!
# Excluding the J₁ row of the literal nonblock quotient sieve

The two-core of the perfect secondary projection is central in the actual
J₁ model. This makes the original torus centralize the entire secondary
action image. Every J₁ automorphism is inner. A centralizing automorphism
of order three would therefore come from an element of the secondary
projection's center: its order is divisible by three, whereas nine does
not divide the J₁ order. That center lies in the two-core, a contradiction.
Cauchy's theorem now kills the actual torus image when n = 2.

Source: Aschbacher–Smith, original 4.3.16(3) and the following elimination,
printed p.618. Both the component quotient and its action remain literal.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

private theorem janko_center : center Janko1.Model = ⊥ := by
  rcases (inferInstance : (center Janko1.Model).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative Janko1.Model (center_eq_top_iff.mp h)).elim

/-- The actual secondary two-core image is central in the J₁ row. -/
theorem SecondaryData.coreImageCentral_of_janko (s : SecondaryData c n)
    (e : (s.component ⧸ pCore 2 s.component) ≃* Janko1.Model) :
    SecondaryData.CoreImageCentral s := by
  let f := e.toMonoidHom.comp (SecondaryData.secondaryProjection s)
  let := secondary_perfect c
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hcore : (pCore 2 (secondary c)).map f.rangeRestrict ≤ pCore 2 f.range :=
    le_sSup ⟨(inferInstance : (pCore 2 (secondary c)).Normal).map _ f.rangeRestrict_surjective,
      pCore_isPGroup.map _⟩
  have hc := hcore.trans (Janko1.perfect_subgroup_pCore_two_le_center f.range)
  intro a ha
  obtain ⟨x,hx,rfl⟩ := ha
  obtain ⟨u,hu,heu⟩ := hx
  have hxa : x = ⟨u,(s.secondary_le.trans (map_subtype_le _)) u.property⟩ := Subtype.ext heu.symm
  rw [hxa,SecondaryData.action_secondary]
  rintro b ⟨y,hy,rfl⟩
  have hya : y = ⟨(⟨y,hy⟩ : secondary c),(s.secondary_le.trans (map_subtype_le _)) hy⟩ := rfl
  rw [hya,SecondaryData.action_secondary]
  have huC := hc (mem_map_of_mem f.rangeRestrict hu)
  have heq := congrArg (fun z : f.range => (z : Janko1.Model))
    (mem_center_iff.mp huC (f.rangeRestrict ⟨y,hy⟩))
  have heq' : SecondaryData.secondaryProjection s ⟨y,hy⟩ * SecondaryData.secondaryProjection s u =
      SecondaryData.secondaryProjection s u * SecondaryData.secondaryProjection s ⟨y,hy⟩ := by
    apply e.injective
    change f ⟨y,hy⟩ * f u = f u * f ⟨y,hy⟩ at heq
    simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul] using heq
  simpa only [← map_mul] using congrArg (MulAut.conj : (s.component ⧸ pCore 2 s.component) →* MulAut _) heq'

/-- No automorphism of order three centralizes the entire secondary image. -/
theorem SecondaryData.janko_prime_exclusion (s : SecondaryData c n) (hn : n = 2)
    (e : (s.component ⧸ pCore 2 s.component) ≃* Janko1.Model)
    {a : MulAut (s.component ⧸ pCore 2 s.component)}
    (ha : a ∈ centralizer (SecondaryData.secondaryImage s : Set _)) : orderOf a ≠ 3 := by
  subst n
  let H := (SecondaryData.secondaryProjection s).range
  let := SecondaryData.secondaryProjection_perfect s
  have h3H : 3 ∣ Nat.card H := by
    obtain ⟨F,_,_,hF,⟨em⟩⟩ := SecondaryData.secondaryProjection_model s
    obtain ⟨ea⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (K := F) (by simpa using hF)
    have hc : Nat.card (H ⧸ pCore 2 H) = 60 := by
      rw [Nat.card_congr (em.trans ea).toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hd := card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 H))
      (QuotientGroup.mk'_surjective _)
    rw [hc] at hd
    exact (by decide : 3 ∣ 60).trans hd
  have hcenter : center (H ⧸ pCore 2 H) = ⊥ := by
    obtain ⟨F,_,_,_,⟨em⟩⟩ := SecondaryData.secondaryProjection_model s
    apply (eq_bot_iff_forall _).mpr
    intro z hz
    have hz' : em z ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨y,rfl⟩ := em.surjective y
      simpa only [map_mul] using congrArg em (mem_center_iff.mp hz y)
    rw [GorensteinWalter.psl2_center_eq_bot,mem_bot] at hz'
    exact em.injective (hz'.trans (map_one em).symm)
  have hJ : center (s.component ⧸ pCore 2 s.component) = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    have hx' : e x ∈ center Janko1.Model := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨y,rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hx y)
    rw [janko_center,mem_bot] at hx'
    exact e.injective (hx'.trans (map_one e).symm)
  apply inner_automorphism_orderOf_ne_prime_of_square_not_dvd H h3H
    (by rw [Nat.card_congr e.toEquiv,Janko1.card_model]; norm_num)
    (center_le_pCore_of_quotient_center_eq_bot hcenter) (by decide : Nat.Coprime 2 3) hJ a
  · have he : SecondaryData.secondaryImage s = H.map MulAut.conj :=
      SecondaryData.secondary_action_image s
    rwa [← he]
  · obtain ⟨g,hg⟩ := Janko1.OuterCertificate.aut_inner (MulAut.congr e a)
    obtain ⟨x,hx⟩ := (MulAut.congr_inner_iff e a).mp ⟨g,hg.symm⟩
    exact ⟨x,hx.symm⟩

/-- The nontrivial torus action excludes the J₁ alternative at n = 2. -/
theorem SecondaryData.not_janko_model (s : SecondaryData c n) (hn : n = 2) :
    ¬ Nonempty ((s.component ⧸ pCore 2 s.component) ≃* Janko1.Model) := by
  rintro ⟨e⟩
  apply s.torus_action_ne_bot
  apply SecondaryData.torusImage_eq_bot_of_prime_centralizer s (by omega)
    (SecondaryData.coreImageCentral_of_janko s e)
  intro p hp _ hd a _ hc horder
  have hp3 : p = 3 := by
    rw [hn] at hd
    norm_num at hd
    exact (Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_left hp.ne_one
  exact SecondaryData.janko_prime_exclusion s hn e hc (horder.trans hp3)
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
