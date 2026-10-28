module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.ReeFour.LowerObstruction.Kernel
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.ReeFour.LowerObstruction.OddConfinement.LinearParabolic
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.ReeFour.LowerObstruction.OddConfinement.SuzukiParabolic
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon

/-!
# Excluding the odd Ree branch through its two actual parabolics

The intrinsic two-core of an E1 member meets its root subgroup by the literal
rank-one condition. Embed that core in the Ree group. The proved finite
Borel--Tits argument on the actual Ree octagon places its normalizer, and
hence the member, in a conjugate of a full parabolic. Conjugation preserves
the concrete root family and the rank in the intrinsic two-core quotient.

The matrix-root calculations in `LinearParabolic` and `SuzukiParabolic`
exclude rank one for a full root-family member inside either full parabolic.
They discharge the local premises of the earlier conditional reduction.
Consequently this E1 case is impossible, proving its required confinement
in `modelNormalizer`. The full parabolics retain their complementary tori;
the source factors with Suzuki and linear quotients are their seeds.

The final application derives the kernel intersection from
`odd_kernel_meets_root`. No simplicity hypothesis is needed for this E1
branch. The E2 branch and the complete E.1.14(1) obstruction remain with
the parent assembly.

Source: Aschbacher--Smith E.1.2(E1) and E.1.14(1), printed pp.209--210 and
214 of `refs/quasithin.pdf`; the latter cites Aschbacher, *GF(2)-representations
of finite groups*, Lemma 4.7 (DOI 10.2307/2374202). The normalizer reduction
uses the established Ree octagon and finite Borel--Tits, GLS3 Theorem 3.1.3.
The parameter hypothesis includes the smallest positive case m = 1, q = 8.
-/

public section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour.LowerObstruction
open Subgroup ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds
open ReeF4.MaximalSubgroups.AbelianCharacteristic
open ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry

/-- A subgroup with nontrivial intrinsic two-core lies in a conjugate of an
actual full Ree parabolic. All octagon and apartment premises are discharged. -/
theorem exists_parabolic_of_twoCore_ne_bot {m : ℕ} (hm : 0 < m)
    (K : Subgroup (Model m)) (hcore : pCore 2 K ≠ ⊥) :
    ∃ (g : Model m) (s : Side),
      K.map (MulAut.conj g).toMonoidHom ≤ Parabolics.parabolic m s := by
  let R := (pCore 2 K).map K.subtype
  have hR : R ≠ ⊥ := fun hz =>
    hcore (((pCore 2 K).map_eq_bot_iff_of_injective K.subtype_injective).mp hz)
  have hKR : K ≤ normalizer (R : Set (Model m)) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, K.range_subtype] using
      (pCore 2 K).le_normalizer_map K.subtype
  have hindex : Odd (ConverseParabolics.unipotent m).index := by
    rw [unipotent_eq_rootUnipotent]
    exact OuterLocal.LargeAutomorphisms.unipotent_index_odd_of_standard
      (canonicalLocalBlockInput m)
      (LargeLocalSeeds.FixedBruhat.standardUnipotent_index_odd (canonicalLocalBlockInput m))
  obtain ⟨g, s, _, hgs⟩ := normalizer_cover_of_octagon
    (octagonGeometry m hm) hindex (oddApartmentStabilizers m hm)
    R hR (pCore_isPGroup.map K.subtype)
  refine ⟨g, s, ?_⟩
  rw [parabolic_eq_rootParabolic] at hgs
  exact (map_mono hKR).trans hgs

/-- The literal E1 rank-one condition supplies the nontrivial two-core
needed for the geometric reduction, using `odd_kernel_meets_root`. -/
theorem odd_member_parabolic_reduction {m : ℕ} (hm : 0 < m)
    {A K : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hK : IsEMember (unipotent m) A K) (hodd : ECaseOdd A K) :
    ∃ (g : Model m) (s : Side),
      A.map (MulAut.conj g).toMonoidHom ∈ rootFamily m ∧
      A.map (MulAut.conj g).toMonoidHom ≤ K.map (MulAut.conj g).toMonoidHom ∧
      K.map (MulAut.conj g).toMonoidHom ≤ Parabolics.parabolic m s ∧
      ECaseOdd (A.map (MulAut.conj g).toMonoidHom)
        (K.map (MulAut.conj g).toMonoidHom) := by
  have hmeet := odd_kernel_meets_root hm hA hK hodd
  have hcore : pCore 2 K ≠ ⊥ := fun hz => hmeet (by rw [hz, inf_bot_eq])
  obtain ⟨g, s, hgs⟩ := exists_parabolic_of_twoCore_ne_bot hm K hcore
  exact ⟨g, s, rootFamily_conjugationInvariant m A hA g,
    map_mono hK.2.2.1, hgs, hodd.map_injective _ (MulAut.conj g).injective⟩

/-- Conditional E1 exclusion from the two parabolic rank calculations.
These are local quotient assertions, not normalizer-confinement assumptions. -/
theorem not_odd_of_parabolic_rank_exclusions {m : ℕ} (hm : 0 < m)
    (hsuzuki : ∀ A K : Subgroup (Model m), A ∈ rootFamily m → A ≤ K →
      K ≤ Parabolics.parabolic m .suzuki →
      Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) ≠ 1)
    (hlinear : ∀ A K : Subgroup (Model m), A ∈ rootFamily m → A ≤ K →
      K ≤ Parabolics.parabolic m .linear →
      Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) ≠ 1)
    {A K : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hK : IsEMember (unipotent m) A K) : ¬ ECaseOdd A K := by
  intro hodd
  obtain ⟨g, s, hAg, hAKg, hKg, hoddg⟩ := odd_member_parabolic_reduction hm hA hK hodd
  obtain ⟨p, _, _, _, _, _, hrank⟩ := hoddg
  cases s with
  | suzuki => exact hsuzuki _ _ hAg hAKg hKg hrank
  | linear => exact hlinear _ _ hAg hAKg hKg hrank

/-- Application to the exact proposed trapping subgroup. The local quotient
exclusions remain explicit; the kernel-intersection premise has been discharged
by its existing producer in `odd_member_parabolic_reduction`. -/
theorem odd_member_le_modelNormalizer_of_parabolic_rank_exclusions
    {m : ℕ} (hm : 0 < m)
    (hsuzuki : ∀ A K : Subgroup (Model m), A ∈ rootFamily m → A ≤ K →
      K ≤ Parabolics.parabolic m .suzuki →
      Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) ≠ 1)
    (hlinear : ∀ A K : Subgroup (Model m), A ∈ rootFamily m → A ≤ K →
      K ≤ Parabolics.parabolic m .linear →
      Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) ≠ 1)
    {A K : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hK : IsEMember (unipotent m) A K) (hodd : ECaseOdd A K) :
    K ≤ modelNormalizer m :=
  (not_odd_of_parabolic_rank_exclusions hm hsuzuki hlinear hA hK hodd).elim

/-- The two concrete parabolic calculations exclude E1 whenever the intrinsic
two-core is nontrivial. Conjugation uses the actual root family and transports
the literal quotient-rank condition in `ECaseOdd`. -/
theorem not_odd_of_twoCore_ne_bot {m : ℕ} (hm : 0 < m)
    {A K : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hAK : A ≤ K) (hcore : pCore 2 K ≠ ⊥) : ¬ ECaseOdd A K := by
  intro hodd
  obtain ⟨g, s, hgs⟩ := exists_parabolic_of_twoCore_ne_bot hm K hcore
  have hAg := rootFamily_conjugationInvariant m A hA g
  have hAKg := map_mono (f := (MulAut.conj g).toMonoidHom) hAK
  obtain ⟨p, _, _, _, _, _, hrank⟩ :=
    hodd.map_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  cases s with
  | suzuki => exact suzuki_parabolic_root_rank_ne_one hm hAg hAKg hgs hrank
  | linear => exact linear_root_rank_ne_one hm hAg hAKg hgs hrank

/-- The E1 confinement interface consumed by the parent obstruction assembly.
The specified root intersection makes O₂(K) nontrivial, so the proved
parabolic rank exclusions rule out this case. -/
theorem odd_member_le_modelNormalizer_of_kernel_meets_root
    {m : ℕ} (hm : 0 < m)
    {A K : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hK : IsEMember (unipotent m) A K) (hodd : ECaseOdd A K)
    (hmeet : A.subgroupOf K ⊓ pCore 2 K ≠ ⊥) : K ≤ modelNormalizer m := by
  have hcore : pCore 2 K ≠ ⊥ := fun hz => hmeet (by rw [hz, inf_bot_eq])
  exact (not_odd_of_twoCore_ne_bot hm hA hK.2.2.1 hcore hodd).elim

/-- E1 containment with its kernel-intersection premise discharged by the
literal rank-one producer. This includes m = 1, q = 8. -/
theorem odd_member_le_modelNormalizer {m : ℕ} (hm : 0 < m)
    {A K : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hK : IsEMember (unipotent m) A K) (hodd : ECaseOdd A K) :
    K ≤ modelNormalizer m :=
  odd_member_le_modelNormalizer_of_kernel_meets_root hm hA hK hodd
    (odd_kernel_meets_root hm hA hK hodd)

/-- No E-member for this full root family satisfies the source E1 condition.
Both parabolic quotient-rank premises of the conditional assembly are proved. -/
theorem not_odd_member {m : ℕ} (hm : 0 < m)
    {A K : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hK : IsEMember (unipotent m) A K) : ¬ ECaseOdd A K :=
  not_odd_of_parabolic_rank_exclusions hm
    (fun _ _ hB hBJ hJP => suzuki_parabolic_root_rank_ne_one hm hB hBJ hJP)
    (fun _ _ hB hBJ hJP => linear_root_rank_ne_one hm hB hBJ hJP) hA hK

end CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour.LowerObstruction
