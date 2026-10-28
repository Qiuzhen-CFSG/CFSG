module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartan
public import Theory.SpecificGroups.SU3.BorelTorus.Basic
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.Derived
public import Theory.Alternating.PrimeRank
public import Theory.GroupTheory.PerfectCentralCoverOddRankRigidity

/-!
# The normal E.2 residual with an odd Hall subgroup of order three

The Hall order bounds every odd divisor of the original maximal subgroup.
The marked torus fixes each surviving binary field exponent at two. The
full unitary and symplectic Borel tori then exclude their rows, leaving the
A₅ row and the projective linear-three group over four elements. Every
odd-characteristic row is excluded by its proved generation bound.

The A₅ recognition retains the possible central cover: its two-core-free
quasisimple cover has odd center, and perfect-cover transfer kills this
kernel because A₅ has odd-prime rank at most one. No equality of generation
parameters across the maximal core is used.
Source: Aschbacher--Smith E.2.2 and 9.2.7, printed pp.215--216,731--732.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceOldResidual
open ChapterB ChapterE ChapterE.Section06.FixedPointBounds
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem odd_dvd_card_dvd_hall {B : Subgroup X}
    (hHall : IsHallSubgroup oddPrimes B) {n : ℕ} (hn : Odd n)
    (hd : n ∣ Nat.card X) : n ∣ Nat.card B := by
  have hcop : Nat.Coprime n B.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpn hpi
    have hp2 : p ≠ 2 := fun he => hn.not_two_dvd_nat (he ▸ hpn)
    exact hHall.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hpi hp2
  exact hcop.dvd_of_dvd_mul_right (B.card_mul_index ▸ hd)

omit [Finite X] in
theorem odd_dvd_maximal_dvd_three {M B : Subgroup X} (hBM : B ≤ M)
    (hHall : IsHallSubgroup oddPrimes (B.subgroupOf M)) (hB3 : Nat.card B = 3)
    {n : ℕ} (hn : Odd n) (hd : n ∣ Nat.card M) : n ∣ 3 := by
  have he := odd_dvd_card_dvd_hall hHall hn hd
  rwa [Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv,hB3] at he

omit [Finite X] in
theorem model_borel_card_dvd {M K : Subgroup X}
    {A : Type*} [Group A] [Finite A] {P : Subgroup A}
    (hm : ModelBorelPair M K P) : Nat.card P ∣ Nat.card M := by
  obtain ⟨e,he⟩ := hm
  rw [← Nat.card_congr (componentBorelEquiv P e he).toEquiv]
  exact (card_map_dvd _ _).trans (card_dvd_of_le (show M ⊓ K ≤ M from inf_le_left))

omit [Finite X] in
theorem parameter_le_two_of_cyclic {M : Subgroup X}
    (hsize : ∀ n : ℕ, Odd n → n ∣ Nat.card M → n ∣ 3)
    {f : ℕ} (hf : 0 < f)
    (hcyc : ∃ C : Subgroup X, C ≤ M ∧ IsCyclic C ∧ Nat.card C = 2^f-1) : f ≤ 2 := by
  obtain ⟨C,hCM,_,hC⟩ := hcyc
  have ho : Odd (2^f-1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (even_two.pow_of_ne_zero (by omega)) odd_one
  have hd := hsize _ ho
    (hC ▸ card_dvd_of_le hCM)
  have hs : 2^f-1 ≤ 3 := Nat.le_of_dvd (by decide) hd
  apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
  have hp : 0 < 2^f := pow_pos (by decide) _
  omega

theorem not_unitary_model {M K : Subgroup X}
    (hsize : ∀ n : ℕ, Odd n → n ∣ Nat.card M → n ∣ 3)
    {f : ℕ} (hm : UnitaryModel M K f) : False := by
  have hf : 0 < f := by obtain ⟨_,_,_,_,_,_,hf,_⟩ := hm; omega
  have hle := parameter_le_two_of_cyclic hsize hf hm.cyclic
  obtain ⟨F,hF,hfin,hchar,J,hJ,hf,hcard,hconj,_,hp⟩ := hm
  have he : f=2 := by omega
  subst f
  let P := BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.projectiveTorus J hJ
  have hP : Nat.card P = 15 := by
    simpa using BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.projective_card J hJ hcard hconj
  have hdiv : 15 ∣ Nat.card M := hP ▸ (card_dvd_of_le
    (show P ≤ unitaryBorel J hJ from le_sup_right)).trans (model_borel_card_dvd hp)
  have hh := hsize 15 (by decide) hdiv
  norm_num at hh

omit [Finite X] in
theorem not_symplectic_model {M K : Subgroup X}
    (hsize : ∀ n : ℕ, Odd n → n ∣ Nat.card M → n ∣ 3)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (hm : ModelBorelPair M K (sp4DerivedBorel F)) : False := by
  let := Theory.SpecificGroups.SymplecticFour.perfect_of_card_gt_two (by omega : 2 < Nat.card F)
  have hD : commutator (Theory.SpecificGroups.SymplecticFour.Sp F) = ⊤ :=
    Group.IsPerfect.commutator_eq_top
  have hle : Theory.SpecificGroups.SymplecticFour.borel (F := F) ≤
      commutator (Theory.SpecificGroups.SymplecticFour.Sp F) := by rw [hD]; exact le_top
  have hbc : Nat.card (sp4DerivedBorel F) =
      Nat.card (Theory.SpecificGroups.SymplecticFour.borel (F := F)) :=
    Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv
  have htor : 9 ∣ Nat.card (Theory.SpecificGroups.SymplecticFour.borel (F := F)) := by
    have hh := card_dvd_of_surjective (Theory.SpecificGroups.SymplecticFour.borelCharacters (F := F))
      Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.characters_surjective
    simpa [Nat.card_prod,Nat.card_units,hF] using hh
  have hh := hsize 9 (by decide)
    (htor.trans (hbc ▸ model_borel_card_dvd hm))
  norm_num at hh

private theorem center_odd_of_twoCore_eq_bot (C : Type*) [Group C] [Finite C]
    (h2 : pCore 2 C = ⊥) : Odd (Nat.card (center C)) := by
  by_contra hodd
  have hd : 2 ∣ Nat.card (center C) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center C) 2 hd
  let Y := (zpowers z).map (center C).subtype
  have hYc : Y ≤ center C := map_subtype_le _
  let : Y.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hYc hx) g, mul_inv_cancel_right]
    exact hx⟩
  have hYp : IsPGroup 2 Y := by
    apply IsPGroup.of_card (n := 1)
    simp only [Y, card_map_of_injective (center C).subtype_injective,
      Nat.card_zpowers, hz, pow_one]
  have hle : Y ≤ pCore 2 C := le_sSup ⟨inferInstance, hYp⟩
  have hz1 : (z : C) = 1 := (h2 ▸ hle) (mem_map_of_mem _ (mem_zpowers z))
  have : z = 1 := Subtype.ext hz1
  simp [this] at hz

theorem a5_equiv_of_twoReduced_quasisimple_surjective
    {C : Type*} [Group C] [Finite C] [IsQuasisimple C]
    (h2 : pCore 2 C = ⊥) (f : C →* alternatingGroup (Fin 5))
    (hf : Function.Surjective f) : Nonempty (C ≃* alternatingGroup (Fin 5)) := by
  have hfc : f.ker ≤ center C := by
    rcases IsQuasisimple.normal_le_center_or_eq_top f.ker with hc | he
    · exact hc
    · have hbot : f.range = ⊥ := MonoidHom.range_eq_bot_iff.mpr
        (MonoidHom.ker_eq_top_iff.mp he)
      exact (bot_ne_top (hbot.symm.trans (MonoidHom.range_eq_top.mpr hf))).elim
  let c : PerfectCentralCovering.Cover C (alternatingGroup (Fin 5)) :=
    { toMonoidHom := f, surjective := hf, isPerfect := inferInstance, ker_le_center := hfc }
  have hodd : Odd (Nat.card f.ker) :=
    (center_odd_of_twoCore_eq_bot C h2).of_dvd_nat (card_dvd_of_le hfc)
  have hk := c.ker_eq_bot_of_odd_of_odd_primeRank_le_one hodd (by
    intro p hp ho
    rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 5 p hp
      (fun he => by subst p; norm_num at ho)]
    have hp3 : 3 ≤ p := by have := hp.two_le; obtain ⟨k,hk⟩ := ho; omega
    apply Nat.lt_succ_iff.mp
    exact (Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega))
  exact ⟨MulEquiv.ofBijective f ⟨(MonoidHom.ker_eq_bot_iff f).mp hk,hf⟩⟩

theorem component_twoCore_quotient_a5_of_star
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (K : Subgroup X) (hK : K.IsCComponent)
    (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (e : sourceImage (minimalParabolicMax S hP) K ≃* alternatingGroup (Fin 5)) :
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) := by
  let := hqs
  let g := DiagramHall.linearSourceComparison S hP K
  let d := cComponentTwoCoreQuotientEquiv hK
  let f := (e.toMonoidHom.comp g).comp d.toMonoidHom
  exact a5_equiv_of_twoReduced_quasisimple_surjective (pCore_quotient_pCore_eq_bot 2)
    f (e.surjective.comp ((DiagramHall.linearSourceComparison_surjective S hP K).comp d.surjective))

theorem normal_component_a5_or_linear_three_four
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (hs : ¬Group.IsSolvable X) (hn : 1 < generationParameter X)
    (K : Subgroup X) (hK : K.IsCComponent) [K.Normal]
    (hqs : IsQuasisimple (K ⧸ pCore 2 K)) (hgen : K ⊔ (S : Subgroup X) = ⊤)
    (hsize : ∀ n : ℕ, Odd n → n ∣ Nat.card (minimalParabolicMax S hP) → n ∣ 3) :
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∨
      ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax S hP) K) 3 4 := by
  have hA := ChapterA.Section02.theoremA_knownSimple (G := X)
  have hC : ∀ (G : Type _) [Group G] [Finite G],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple G :=
    fun _ _ _ => ChapterA.Section02.theoremC_knownSimple
  rcases source_normal_geometric_cases hA hC hX S hP hs K hK hgen with h2|h3|hb|hl|hsp|hbi
  · exact (single_odd_linear_false_of_parameter_gt_one hA hX S hP hs K hK hgen h2 hn).elim
  · obtain ⟨p,hp,ho,_,huni|hlin⟩ := h3
    · exact (normal_odd_three_false_of_parameter_gt_one hA hX S hP hs K hK hgen hp ho
        (.inr huni.2) hn).elim
    · obtain ⟨_,F,hF,hfin,hcard,e,_⟩ := hlin
      exact (normal_odd_three_false_of_parameter_gt_one hA hX S hP hs K hK hgen hp ho
        (.inl ⟨F,hF,hfin,hcard,⟨e⟩⟩) hn).elim
  · cases hb with
    | linear f hf hm =>
      have hb := source_linear_borel_model S hP hs K hK hgen hf hm
      have hf2 := parameter_le_two_of_cyclic hsize (by omega) hb.cyclic
      have he : f=2 := by omega
      subst f
      obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
      obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
        (show Nat.card F=4 from hcard)
      exact .inl (component_twoCore_quotient_a5_of_star S hP K hK hqs (e.trans a))
    | unitary f hf hm =>
      exact (not_unitary_model hsize (source_unitary_borel_model S hP hs K hK hgen hf hm)).elim
    | suzuki m hm he =>
      have hb := source_suzuki_borel_model S hP hs K hK hgen hm he
      have hf2 := parameter_le_two_of_cyclic hsize (by omega) hb.cyclic
      omega
  · obtain ⟨f,hf,hm⟩ := hl
    have hb := source_binary_linear_three_model S hP hs K hK hgen hf hm
    have hf2 := parameter_le_two_of_cyclic hsize hf hb.cyclic
    have hu := normal_classical_parameter_le hA hX S hP hs K hK hgen (.inr (.inr ⟨hf,hm⟩))
    have he : f=2 := by omega
    subst f
    exact .inr hm
  · obtain ⟨f,hf,hm⟩ := hsp
    have hb := source_binary_symplectic_model S hP hs K hK hgen hf hm
    have hf2 := parameter_le_two_of_cyclic hsize (by omega) hb.cyclic
    have he : f=2 := by omega
    subst f
    rcases hb with ⟨F,hF,hfin,hchar,_,hcard,e,hB,_⟩ | ⟨F,hF,hfin,hchar,_,hcard,e,hB,_⟩
    · exact .inr ⟨F,hF,hfin,hcard,⟨e⟩⟩
    · exact (not_symplectic_model hsize hcard ⟨e,hB⟩).elim
  · exact ((Nat.not_le_of_gt hn) (normal_binary_six_parameter_le S hP hs K hK hgen hbi)).elim

end CFSG.Quasithin.Chapter10.SourceOldResidual
