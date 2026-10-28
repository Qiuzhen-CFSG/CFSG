module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.SmallUnitaryCover
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalSmallExclusion
public import Theory.Representation.BinaryResidualSection
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.GroupTheory.GeneralizedFitting.CentralCoverLift

/-!
# The actual unitary Frattini section at fixed-field order two

A nontrivial irreducible binary SU3(2) action has kernel in a Sylow
normalizer, by the rank-one maximality property and a nonzero Sylow-fixed
vector. Its projective kernel is then a normal two-subgroup. The actual
root actor has trivial two-core, so the possible kernel is scalar. The
field-two degree obstruction makes the action faithful and forces degree
at least six.

The original source gives a faithful six-dimensional Frattini section.
Its nontrivial two-residual survives on an irreducible section; the degree
bound forces that section to be the whole space. This proves irreducibility
without perfectness. Together with the existing larger-field argument it
constructs the full actor profile and actual irreducible action for all
positive binary field degrees and either endpoint orientation.

Sources: Fong--Seitz I (4D), (6A)(c), pp.21--23,37--38; DGS (11.8), p.175.
The original profile and the generic surjective cover with its projective
square remain the inputs of their independent source producers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure

private theorem irreducible_kernel_le_sylow_normalizer
    {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) D V) [σ.IsIrreducible]
    (hnt : ∃ g, σ g ≠ 1) (T : Sylow 2 D) (hf : RankOneSylowFacts T) :
    σ.ker ≤ normalizer (T : Set D) := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial σ
  obtain ⟨v,hv,hfix⟩ := pGroup_fix_nonzero_vector (F := ZMod 2)
    (by simp only [ZMod.ringChar_zmod_n]; decide)
    (by simpa only [ZMod.ringChar_zmod_n] using T.isPGroup') (σ.comp (T : Subgroup D).subtype)
  apply le_sup_left.trans (hf.unique_maximal _ le_sup_right (lt_top_iff_ne_top.mpr ?_))
  intro hsup
  have hV : v ∈ invariants (σ.comp (⊤ : Subgroup D).subtype) := by
    have he := σ.invariants_comp_sup σ.ker (T : Subgroup D)
    rw [hsup] at he
    rw [he]
    refine ⟨?_,hfix⟩
    intro g
    change σ g v = v
    rw [show σ g = 1 from g.property]
    rfl
  have hh := le_ker_of_normal_invariants_ne_bot σ (⊤ : Subgroup D)
    (fun hb => hv (by simpa only [hb,Submodule.mem_bot] using hV))
  obtain ⟨g,hg⟩ := hnt
  exact hg (hh (mem_top g))

/-- Every nontrivial small-unitary irreducible has only a possible scalar
kernel. The original two-core hypothesis suffices in the nonperfect case. -/
private theorem small_unitary_irreducible_kernel_le_scalar
    {E V : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hE : Nat.card E = 2^2)
    (hconj : ∀ x, J.conj x = x^2)
    (hcore : pCore 2 (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥)
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) J.specialSubgroup V) [σ.IsIrreducible]
    (hnt : ∃ g, σ g ≠ 1) : σ.ker ≤ J.specialToProjective.ker := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ J.specialToProjective_surjective
  let T : Sylow 2 J.specialSubgroup := Sylow.nonempty.some
  let S := T.mapSurjective J.specialToProjective_surjective
  have hk := irreducible_kernel_le_sylow_normalizer σ hnt T
    (rankOneSylowFacts_su3 J 1 (by decide) (by simpa using hE) (by simpa using hconj) T)
  have hm : σ.ker.map J.specialToProjective ≤ (S : Subgroup _) := by
    have hh := map_mono (f := J.specialToProjective) hk
    rw [T.normalizer_map_surjective J.specialToProjective J.specialToProjective_surjective] at hh
    exact hh.trans_eq (DGS85.Noncommuting.psu_two_self_normalizing J hE hconj S)
  have hp := S.isPGroup'.to_le hm
  let : (σ.ker.map J.specialToProjective).Normal :=
    Normal.map inferInstance J.specialToProjective J.specialToProjective_surjective
  have hle : σ.ker.map J.specialToProjective ≤ pCore 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    le_sSup ⟨inferInstance,hp⟩
  intro g hg
  exact mem_bot.mp (hcore ▸ hle (mem_map_of_mem J.specialToProjective hg))

/-- Every nontrivial irreducible binary SU3(2) representation has degree at
least six. This uses the real scalar kernel and no perfectness. -/
private theorem small_unitary_irreducible_degree
    {E V : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hE : Nat.card E = 2^2)
    (hconj : ∀ x, J.conj x = x^2)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcore : pCore 2 (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥)
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) J.specialSubgroup V) [σ.IsIrreducible]
    (hnt : ∃ g, σ g ≠ 1) : 6 ≤ Module.finrank (ZMod 2) V := by
  by_contra! hd
  have hk := small_unitary_irreducible_kernel_le_scalar J hE hconj hcore σ hnt
  have hi := small_unitary_faithful_of_scalar_kernel J hE hconj hJ σ hk (by omega)
  exact (not_le_of_gt hd) (small_special_unitary_faithful_degree J hE hconj hJ σ hi)

/-- A faithful binary six-space for SU3(2) is irreducible. A nontrivial
two-residual survives on a simple section, whose degree forces the whole space. -/
private theorem small_unitary_faithful_six_irreducible
    {E V : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hE : Nat.card E = 2^2)
    (hconj : ∀ x, J.conj x = x^2)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcore : pCore 2 (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥)
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) J.specialSubgroup V)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 6) : σ.IsIrreducible := by
  have hR : pResidual 2 J.specialSubgroup ≠ ⊥ := by
    intro hb
    have hp : IsPGroup 2 J.specialSubgroup :=
      (isPGroup_quotient_pResidual 2).of_equiv
        ((QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot)
    obtain ⟨k,hk⟩ := hp.exists_card_eq
    have h3 : 3 ∣ 2^k := by
      rw [←hk,small_special_unitary_card J hE hconj hJ]
      decide
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h3)
  obtain ⟨U,N,hirr,hnt⟩ := exists_irreducible_section_surviving_twoPerfect
    (ρ := σ) (pResidual 2 J.specialSubgroup) (isPPerfect_pResidual 2)
    (by simpa only [(MonoidHom.ker_eq_bot_iff _).mpr hf,le_bot_iff] using hR)
  let : N.quotientRepresentation.IsIrreducible := hirr
  have hn : ∃ g, N.quotientRepresentation g ≠ 1 := by
    by_contra! hh
    exact hnt (fun g _ => hh g)
  have hmin := small_unitary_irreducible_degree J hE hconj hJ hcore N.quotientRepresentation hn
  have hsum := Submodule.finrank_quotient_add_finrank N.toSubmodule
  have hUle := U.toSubmodule.finrank_le
  have hUdim : Module.finrank (ZMod 2) U.toSubmodule = 6 := by omega
  have hNdim : Module.finrank (ZMod 2) N.toSubmodule = 0 := by omega
  have hUb : U.toSubmodule ≠ ⊥ := by
    intro hb
    rw [hb,finrank_bot] at hUdim
    contradiction
  let : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hUb
  have hNb : N.toSubmodule = ⊥ := Submodule.finrank_eq_zero.mp hNdim
  let : U.toRepresentation.IsIrreducible := ⟨by
    intro W
    rcases N.le_or_sup_eq_top_of_irreducible_quotient W with hw | hw
    · left
      apply Subrepresentation.toSubmodule_injective
      change W.toSubmodule = ⊥
      exact bot_unique ((show W.toSubmodule ≤ N.toSubmodule from hw).trans hNb.le)
    · right
      apply Subrepresentation.toSubmodule_injective
      change W.toSubmodule = ⊤
      simpa only [hNb,bot_sup_eq] using hw⟩
  have hUt : U = ⊤ := Subrepresentation.toSubmodule_injective
    (Submodule.eq_top_of_finrank_eq (hUdim.trans hd.symm))
  have ha := (Subrepresentation.irreducible_iff_isAtom U).mp inferInstance
  rw [hUt] at ha
  exact isSimpleOrder_iff_isAtom_top.mpr ha

open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)
include e h

/-- The full actor and the actual irreducible Frattini section are both
constructed from the original profile and covering transport, including q = 2. -/
theorem marked_unitary_profile_irreducible_all_of_cover
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split j)
    (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (π : J.specialSubgroup →* rankOne Q split j) (hπ : Function.Surjective π)
    (hπν : ∀ a, ν (RootLocalCover.projection Q split j (π a)) = J.specialToProjective a)
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1)
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2))
    (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2)) :
    Nonempty (UnitaryActorProfile Q split j J hVj ν) ∧
      (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)).IsIrreducible := by
  by_cases hn2 : 2 ≤ n
  · exact marked_unitary_profile_of_cover Q split e h J hn2 hE hconj hJ
      hm i j hij hVi hVj s ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  have hn1 : n = 1 := by omega
  subst n
  have hinj := marked_small_unitary_cover_injective Q split e h J
    (by simpa using hE) (by simpa using hconj) hJ hm i j hij hVi hVj s ν π hπν
    (by simpa using hindexi) (by simpa using hindexj) hQi hderived hfrattini
  refine ⟨marked_unitary_profile_all_of_cover Q split e h J hn hE hconj hJ
    hm i j hij hVi hVj s ν π hπ hπν hindexi hindexj hQi hderived hfrattini,?_⟩
  let κ := MulEquiv.ofBijective π ⟨hinj,hπ⟩
  have hpc : pCore 2 J.specialSubgroup = ⊥ := by
    apply map_injective (f := κ.toMonoidHom) κ.injective
    rw [pCore_map_iso,Subgroup.map_bot,rankOne_twoCore_eq_bot Q split j s hVj]
  have hpc' : pCore 2 (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
    rw [←J.specialToProjective.map_pCore_of_central_kernel
      J.specialToProjective_surjective J.specialToProjective_ker_le_center,
      hpc,Subgroup.map_bot]
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1 hn hE hconj
  have hc := (marked_unitary_section Q split e h J hn hE hf hJ
    hm i j hij hVi hVj s ν hindexi hindexj hQi hderived hfrattini).2.1
  let V := (simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j)
  let ρ := elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)
  have hρ : Function.Injective ρ := by
    intro a b hab
    apply marked_remainderFrattiniAction_injective Q e h split j s hVj
    ext v
    exact Additive.ofMul.injective
      (congrArg (fun f : Module.End (ZMod 2) (Additive V) => f (Additive.ofMul v)) hab)
  have hd : Module.finrank (ZMod 2) (Additive V) = 6 := by
    have hd := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod] at hd
    apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
    change 2 ^ Module.finrank (ZMod 2) (Additive V) = 2^6
    rw [←hd]
    exact hc
  exact (irreducible_comp_surjective_iff π hπ ρ).mp
    (small_unitary_faithful_six_irreducible J (by simpa using hE)
      (by simpa using hconj) hJ hpc' (ρ.comp π) (hρ.comp hinj) hd)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
