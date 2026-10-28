module
public import Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms
public import Theory.GroupTheory.GeneralizedFitting.SquareWreath
public import Theory.GroupTheory.SolvableSylowControl
public import Theory.GroupTheory.PCoreFrattiniTransport
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.BenderNormalizers
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters

/-!
# Full automorphism group of the exchanged A₅ square

A solvable overgroup of an ambient Sylow two-subgroup normalizes a Sylow
of the normal A₅ square. Its two-core therefore contains a subgroup of
order sixteen. If its two-core quotient has order 72, its order is divisible
by 1152. The normal square has order 3600, so the ambient group has order
divisible by 28800, the order of Aut(A₅ × A₅). Faithful conjugation is
therefore surjective and gives the actual S₅ wreath isomorphism.

The solvable Sylow control comes from the binary component theorem in
Chapter 1; `FourSource` applies this order argument to the original outside H.
Source: Aschbacher--Smith 14.6.14(3), printed p.1033.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter1.XiEmbedding.SwappedSylow
local notation "A5" => alternatingGroup (Fin 5)
local notation "W5" => RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))

private theorem a5_model : ClassicalGroup.IsPSL A5 2 (2^2) := by
  refine ⟨GaloisField 2 2,inferInstance,inferInstance,?_,
    ⟨Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm⟩⟩
  exact GaloisField.card 2 2 (by decide)

private theorem a5_pair_control : SolvableSylowControl 2 (A5 × A5) := by
  intro S B hs hSB
  let : Group.IsSolvable (B ⊔ (S : Subgroup (A5 × A5)) : Subgroup (A5 × A5)) := by
    rw [sup_eq_left.mpr hSB]
    exact hs
  exact binary_model_prod_le_normalizer (by decide) a5_model S B

private theorem a5_card : Nat.card A5 = 60 := by
  rw [nat_card_alternatingGroup,Nat.card_fin]
  norm_num [Nat.factorial]

private theorem a5_pair_sylow_card (S : Sylow 2 (A5 × A5)) : Nat.card S = 16 := by
  rw [S.card_eq_multiplicity,Nat.card_prod,a5_card]
  rw [show 60 * 60 = 2^4 * 225 by decide,
    Nat.factorization_mul (by decide) (by decide)]
  have h16 : Nat.factorization 16 2 = 4 :=
    Nat.factorization_pow_self (n := 4) Nat.prime_two
  have h225 : Nat.factorization 225 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by decide)
  change 2 ^ (Nat.factorization 16 2 + Nat.factorization 225 2) = 16
  rw [h16,h225]
  rfl

/-- The solvable Sylow overgroup of the marked A₅ square forces the whole
ambient automorphism group when its two-core quotient has order 72. -/
theorem a5_square_full_automorphism
    {Q : Type*} [Group Q] [Finite Q]
    (N B : Subgroup Q) [N.Normal]
    (e : N ≃* A5 × A5) (hc : centralizer (N : Set Q) = ⊥)
    (T : Sylow 2 Q) (hTB : (T : Subgroup Q) ≤ B)
    (hB : Group.IsSolvable B) (hcard : Nat.card (B ⧸ pCore 2 B) = 72) :
    Nonempty (Q ≃* W5) := by
  obtain ⟨P,hP⟩ := T.exists_subgroupOf_eq_of_normal N
  have hPN : (P : Subgroup N).map N.subtype ≤ B := by
    rw [hP,subgroupOf_map_subtype]
    exact inf_le_left.trans hTB
  have hcontrol : SolvableSylowControl 2 N :=
    SolvableSylowControl.of_equiv e a5_pair_control
  let := hB
  have hn : B ≤ normalizer (((P : Subgroup N).map N.subtype) : Set Q) :=
    hcontrol.normalizes_sylow N B P (by simp [normalizer_eq_top]) hPN
  have hp : (P : Subgroup N).map N.subtype ≤ B.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (P.isPGroup'.map N.subtype) hPN hn
  have hPc : Nat.card ((P : Subgroup N).map N.subtype) = 16 := by
    rw [card_map_of_injective N.subtype_injective]
    let S := P.mapSurjective (f := e.toMonoidHom) e.surjective
    have hh := a5_pair_sylow_card S
    change Nat.card ((P : Subgroup N).map e.toMonoidHom) = 16 at hh
    rwa [card_map_of_injective e.injective] at hh
  have hcore : 16 ∣ Nat.card (pCore 2 B) := by
    have hh := hPc ▸ Subgroup.card_dvd_of_le hp
    simpa only [pCoreIn,card_map_of_injective B.subtype_injective] using hh
  have hBdiv : 1152 ∣ Nat.card Q := by
    have hh : 16 * 72 ∣ Nat.card B := by
      rw [←(pCore 2 B).card_mul_index,index_eq_card,hcard]
      exact Nat.mul_dvd_mul_right hcore 72
    exact hh.trans B.card_subgroup_dvd_card
  have hNdiv : 3600 ∣ Nat.card Q := by
    have hncard : Nat.card N = 3600 := by
      rw [Nat.card_congr e.toEquiv,Nat.card_prod,a5_card]
    exact hncard ▸ N.card_subgroup_dvd_card
  have hdiv : 28800 ∣ Nat.card Q := by
    have hh := Nat.lcm_dvd hBdiv hNdiv
    norm_num at hh
    exact hh
  let w := Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.wreathEquiv
  let f : Q →* W5 := w.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : Q →* MulAut N))
  have hf : Function.Injective f := w.symm.injective.comp
    ((MulAut.congr e).injective.comp (MulAut.conjNormal_injective_of_centralizer_eq_bot N hc))
  have hw : Nat.card W5 = 28800 := by
    rw [RegularWreathProduct.card,Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card,Nat.factorial]
  have hle : Nat.card W5 ≤ Nat.card Q := hw ▸ Nat.le_of_dvd Nat.card_pos hdiv
  exact ⟨MulEquiv.ofBijective f (hf.bijective_of_nat_card_le hle)⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
