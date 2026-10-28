module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.PermutationOvergroups
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.SeedGeometry
public import Theory.Representation.BinaryAlternatingSevenControl.PlaneStabilizer

/-!
# The literal four-plus-three placement in the rank-four branch

Every subgroup of order 72 in A₇ is a conjugate of the four-plus-three
partition stabilizer. The faithful binary plane stabilizer has this order.
For the original proper quotient, its full preimage is solvable and contains
the point parabolic, so 14.7.29 puts it in the original seed normalizer.
This proves equality with the actual local intersection, preserving the
quotient homomorphism and the same seven-letter conjugation.

Source: Aschbacher–Smith 14.7.50, printed p.1064, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Equiv
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.FourExclusion
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry.PermutationOvergroups

private theorem solvable_card_seventy_two (P : Subgroup (alternatingGroup (Fin 7)))
    (hP : Nat.card P = 72) : Group.IsSolvable P := by
  apply Theory.GroupTheory.isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hpd
  have h : p ∣ 2 ^ 3 * 3 ^ 2 := by simpa only [hP, show 2 ^ 3 * 3 ^ 2 = 72 by decide] using hpd
  simpa only [hp.dvd_mul, hp.prime.dvd_pow_iff_dvd (by decide : 3 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by decide : 2 ≠ 0),
    Nat.prime_dvd_prime_iff_eq hp Nat.prime_two,
    Nat.prime_dvd_prime_iff_eq hp Nat.prime_three] using h

/-- Every subgroup of order 72 in A₇ is an actual four-plus-three stabilizer
in conjugate seven-letter coordinates. -/
theorem subgroup_card_seventy_two_placement
    (P : Subgroup (alternatingGroup (Fin 7))) (hP : Nat.card P = 72) :
    ∃ σ : Equiv.Perm (Fin 7), σ ∈ alternatingGroup (Fin 7) ∧
      P = fourThreeStabilizer.comap
        ((MulAut.conj σ).toMonoidHom.comp (alternatingGroup (Fin 7)).subtype) := by
  let B := alternatingGroup (Fin 7)
  let S : Sylow 2 P := Sylow.nonempty.some
  have hS : Nat.card S = 8 := by
    rw [Sylow.card_eq_multiplicity,hP,show 72 = 2^3 * 3^2 by decide,
      Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow,
      Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3)]
  let Q : Subgroup B := (S : Subgroup P).map P.subtype
  have hQ : Nat.card Q = 8 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective]
    exact hS
  have hi : Q.index = 315 := by
    have hh := Q.card_mul_index
    rw [hQ,nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh
    omega
  let R : Sylow 2 B := (S.isPGroup'.map P.subtype).toSylow (by rw [hi]; decide)
  let := solvable_card_seventy_two P hP
  obtain ⟨σ,K,hK,hσ,hPK,_,_,_,_,_,_⟩ :=
    solvable_sylow_overgroup_compatible_placement B le_rfl R P (map_subtype_le _)
  let ψ := (MulAut.conj σ).toMonoidHom.comp B.subtype
  have hψ : Function.Injective ψ := (MulAut.conj σ).injective.comp B.subtype_injective
  rcases hK with rfl | rfl
  · refine ⟨σ,hσ,?_⟩
    apply eq_of_le_of_card_ge hPK
    have h1 : Nat.card (fourThreeStabilizer.comap ψ) ∣ 144 := by
      simpa only [fourThreeStabilizer_card] using
        card_comap_dvd_of_injective fourThreeStabilizer ψ hψ
    have h2 : Nat.card (fourThreeStabilizer.comap ψ) ∣ 2520 := by
      have hh := (fourThreeStabilizer.comap ψ).card_subgroup_dvd_card
      change Nat.card (fourThreeStabilizer.comap ψ) ∣ Nat.card (alternatingGroup (Fin 7)) at hh
      have hc : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
        rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
      rwa [hc] at hh
    have hdiv : Nat.card (fourThreeStabilizer.comap ψ) ∣ 72 := Nat.dvd_gcd h1 h2
    rw [hP]
    exact Nat.le_of_dvd (by decide) hdiv
  · have hd := (card_dvd_of_le hPK).trans
      (card_comap_dvd_of_injective pairStabilizer ψ hψ)
    rw [hP,pairStabilizer_card] at hd
    norm_num at hd


open Representation Representation.BinaryOffender

/-- The stabilizer of any plane in a faithful binary A₇ four-space is the
four-plus-three stabilizer in actual conjugate seven-letter coordinates. -/
theorem four_plane_partition_placement
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (τ : Representation (ZMod 2) (alternatingGroup (Fin 7)) X)
    (hf : Function.Injective τ) (hd : Module.finrank (ZMod 2) X = 4)
    (E : Submodule (ZMod 2) X) (hE : Module.finrank (ZMod 2) E = 2) :
    ∃ σ : Equiv.Perm (Fin 7), σ ∈ alternatingGroup (Fin 7) ∧
      subspaceStabilizer τ E = fourThreeStabilizer.comap
        ((MulAut.conj σ).toMonoidHom.comp (alternatingGroup (Fin 7)).subtype) :=
  subgroup_card_seventy_two_placement _
    (BinaryAlternatingSevenControl.plane_stabilizer_card τ hf hd E hE)

open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open scoped IsMulCommutative
universe u v w
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type v} {X : Type w}
  [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup X] [Module (ZMod 2) X]
  {I : Subgroup G} {ρ : Representation (ZMod 2) I W}

omit [Finite G] in
private theorem seed_normalizer_quotient_stabilizes
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (τ : Representation (ZMod 2) (alternatingGroup (Fin 7)) X)
    (π : I →* alternatingGroup (Fin 7))
    (p : ρ.IntertwiningMap (τ.comp π)) :
    ((normalizer (V : Set G)).subgroupOf I).map π ≤
      subspaceStabilizer τ ((c.imageSpace V).map p.toLinearMap) := by
  apply le_subspaceStabilizer
  rintro _ ⟨g,hg,rfl⟩ _ ⟨v,hv,rfl⟩
  refine ⟨ρ g v,c.imageSpace_apply_mem V g hg v hv,?_⟩
  change p (ρ g v) = (τ.comp π) g (p v)
  rw [p.isIntertwining]

/-- In the original local, the full inverse image of the quotient seed-plane
stabilizer is exactly the original seed normalizer. Solvability and 14.7.29
discharge the difficult reverse inclusion. -/
theorem local_four_seed_stabilizer_eq
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (τ : Representation (ZMod 2) (alternatingGroup (Fin 7)) X)
    (π : I →* alternatingGroup (Fin 7)) (hπ : IsPGroup 2 π.ker)
    (p : ρ.IntertwiningMap (τ.comp π)) (hp : p.toLinearMap.ker ≠ ⊤)
    (hf : Function.Injective τ) (hd : Module.finrank (ZMod 2) X = 4)
    [FiniteDimensional (ZMod 2) X] :
    (subspaceStabilizer τ ((c.imageSpace V).map p.toLinearMap)).comap π =
      (normalizer (V : Set G)).subgroupOf I := by
  let E := (c.imageSpace V).map p.toLinearMap
  let P := subspaceStabilizer τ E
  let D := P.comap π
  let J := D.map I.subtype
  have hE : Module.finrank (ZMod 2) E = 2 :=
    local_quotient_seed_finrank h hI c p hp
  let : Group.IsSolvable P := solvable_card_seventy_two P
    (BinaryAlternatingSevenControl.plane_stabilizer_card τ hf hd E hE)
  let : Group.IsNilpotent π.ker := hπ.isNilpotent
  let : Group.IsSolvable D := isSolvable_comap_of_solvable_ker π P
  have hJs : Group.IsSolvable J :=
    Group.isSolvable_of_surjective (I.subtype.subgroupMap_surjective D)
  have hn := seed_normalizer_quotient_stabilizes c τ π p
  have hND : (normalizer (V : Set G)).subgroupOf I ≤ D := map_le_iff_le_comap.mp hn
  have hJH : J ≤ F.H := (map_subtype_le D).trans hI.2.1
  have hbaseI : F.Li L 1 ⊔ (T : Subgroup G) ≤ I := by
    exact sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI)
  have hbaseV : F.Li L 1 ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) :=
    sup_le ((F.Li_le L 1).trans (inf_le_left.trans h.chosen.normalizes))
      (h.sylow_normalizes_seed_at structural)
  have hbaseJ : F.Li L 1 ⊔ (T : Subgroup G) ≤ J := by
    intro g hg
    exact ⟨⟨g,hbaseI hg⟩,hND (hbaseV hg),rfl⟩
  have hJM := GuardedSource.solvable_point_overgroup_le_normalizer
    d h hab structural previous faithful earlier J hJH hbaseJ hJs
  have hne : F.Vi 1 ≠ ⊥ := by
    intro hz
    have hh := F.card 1 (by decide)
    simp [hz] at hh
  have hnormal := structural.intersection_normalizer h.source h.chosen
    hne (F.le_seed 1) (le_rfl : F.H ≤ normalizer (F.Vi 1 : Set G))
  have hJV : J ≤ normalizer (V : Set G) := by
    have hh := le_inf hJH hJM
    rw [hnormal] at hh
    exact hh.trans inf_le_right
  exact le_antisymm (fun g hg => hJV ⟨g,hg,rfl⟩) hND

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.FourExclusion
