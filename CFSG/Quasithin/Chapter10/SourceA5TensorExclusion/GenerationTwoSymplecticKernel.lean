module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticQuotient
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.EvenNormalQuotient
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.TwoRank
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even

/-!
# The original symplectic action kernel

Factor the given residual action through the literal two-core quotient.
The quotient is an SQTK C-component. A nonquasisimple component with an odd
kernel would have two-rank one by coprime rank transport; an even kernel
would give a prime-field PSL2 quotient of two-rank two. Both contradict the
actual Sp4(4) quotient's two-rank six. Its trivial multiplier then makes the
specified surjection injective. Only after constructing this core-quotient
marking do we apply the original central-orbit theorem.

This discharges the kernel premise in generation-two assembly and in the
Frattini-small block branch. Whole-block recognition in the non-Frattini
case and the original plane maps remain separate obligations of
qt-d-tensor-sp4-plane.

Source: Aschbacher--Smith 9.3.6--10, pp.733--734, A.3.6, pp.43--45,
and I.1.3, p.407. The kernel-parity argument follows the existing
NoncentralFitting.AlternatingSevenQuotient proof with the symplectic rank
and central-cover calculations replacing its A7 order exclusion.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
open scoped MatrixGroups
open ChapterA.Section03.NoncentralFitting Theory.SpecificGroups.SymplecticFour

private theorem quasisimple_of_large_quotient_two_rank
    {H S : Type*} [Group H] [Finite H] [Group S] [Finite S] [Nontrivial S]
    {κ : GroupClass} (hH : IsSQTK κ H) (hO : pCore 2 H = ⊥)
    (hC : (⊤ : Subgroup H).IsCComponent)
    (f : H →* S) (hf : Function.Surjective f) (hrank : 3 ≤ primeRank 2 S) :
    IsQuasisimple H := by
  by_contra hnot
  have hproper : f.ker ≠ ⊤ := by
    intro he
    obtain ⟨a,ha⟩ := exists_ne (1 : S)
    obtain ⟨x,rfl⟩ := hf a
    exact ha (MonoidHom.mem_ker.mp (he ▸ mem_top x))
  have heven : Even (Nat.card f.ker) := by
    by_contra he
    have hodd := Nat.not_even_iff_odd.mp he
    have heq := primeRank_eq_of_surjective_of_coprime 2 f hf hodd.coprime_two_left
    have hh : 2 ≤ primeRank 2 (⊤ : Subgroup H) := by
      rw [primeRank_equiv 2 (topEquiv : (⊤ : Subgroup H) ≃* H),heq]
      omega
    let := quasisimple_of_two_le_two_rank hH hO hC hh
    exact hnot (IsQuasisimple.of_mulEquiv topEquiv)
  obtain ⟨_,p,hp,hp3,⟨ep⟩⟩ := intrinsic_even_normal_quotient hH hO hC hnot f.ker hproper heven
  let : Fact p.Prime := ⟨hp⟩
  have heq := primeRank_equiv 2 (ep.symm.trans (QuotientGroup.quotientKerEquivOfSurjective f hf))
  rw [Theory.PSL2.primeField_two_rank hp3] at heq
  omega

private theorem sp4_equiv_of_cComponent_surjection
    {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]
    {κ : GroupClass} (hH : IsSQTK κ H) (hO : pCore 2 H = ⊥)
    (hC : (⊤ : Subgroup H).IsCComponent) (hF : Nat.card F = 4)
    (f : H →* Sp F) (hf : Function.Surjective f) :
    Function.Injective f := by
  let : CharP F 2 := EvenProjective.charTwo_of_card (f := 2) hF
  let : IsSimpleGroup (Sp F ⧸ center (Sp F)) := SimpleQuotients.isSimpleGroup (by omega)
  let : IsSimpleGroup (Sp F) := (EvenProjective.equiv (F := F)).isSimpleGroup
  have hrank : 3 ≤ primeRank 2 (Sp F) := by
    have hr := EvenTwoRank.three_mul_le_rank (n := 2) hF
    omega
  let := quasisimple_of_large_quotient_two_rank hH hO hC f hf hrank
  have hfc : f.ker ≤ center H := by
    rcases IsQuasisimple.normal_le_center_or_eq_top f.ker with hc | he
    · exact hc
    · have hbot : f.range = ⊥ := MonoidHom.range_eq_bot_iff.mpr
        (MonoidHom.ker_eq_top_iff.mp he)
      exact (bot_ne_top (hbot.symm.trans (MonoidHom.range_eq_top.mpr hf))).elim
  exact CentralCovers.Even.cover_injective (by omega : 3 < Nat.card F)
    { toMonoidHom := f, surjective := hf, isPerfect := inferInstance, ker_le_center := hfc }

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e}

namespace GenerationTwoOvergroup
variable (c : m.GenerationTwoOvergroup)

theorem symplectic_core_quotient_of_action
    (hr : IsPReduced 2
      (omegaOrbit (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M))) :
    letI := hr.normal
    Nonempty (((pResidual 2 c.M).map (actionMk (omegaOrbit
      (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)))) ≃*
        Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) →
    Nonempty ((pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) := by
  let := hr.normal
  rintro ⟨eact⟩
  let K := pResidual 2 c.M
  let W := omegaOrbit (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
  let f := eact.toMonoidHom.comp ((actionMk W).subgroupMap K)
  have hf : Function.Surjective f := eact.surjective.comp ((actionMk W).subgroupMap_surjective K)
  have hcore : pCore 2 K ≤ f.ker := by
    have hpc : (pCore 2 K).map K.subtype ≤ pCore 2 c.M :=
      le_sSup ⟨inferInstance, pCore_isPGroup.map K.subtype⟩
    intro k hk
    have hact : (actionMk W).subgroupMap K k = 1 := by
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).mpr
        (le_centralizer_iff.mp hr.le_centralizer_pCore (hpc (mem_map_of_mem K.subtype hk)))
    change eact ((actionMk W).subgroupMap K k) = 1
    rw [hact, map_one]
  let Q := K ⧸ pCore 2 K
  let g : Q →* Sp ChapterB.QuasisimpleSource.BinaryField.four.Carrier :=
    QuotientGroup.lift (pCore 2 K) f hcore
  have hg : Function.Surjective g := QuotientGroup.lift_surjective_of_surjective _ f hf _
  have hH : c.M ∈ Chapter1.H G := by
    intro hb
    exact c.core_ne_bot (((pCore 2 c.M).map_eq_bot_iff_of_injective c.M.subtype_injective).mp hb)
  have hsqK := (Chapter3.sqtk_of_mem_H D.simpleQTKE hH).subgroup K
  have hsqQ : IsSQTK KnownSimple.IsKnownSimple Q := by
    refine ⟨?_,hsqK.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 K) pCore_isPGroup).trans
      (hsqK.stronglyQuasithin p hp ho)
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using c.component_product.1.subgroupOf le_rfl
  let : Group.IsNilpotent (pCore 2 K) := pCore_isNilpotent
  have hbar : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      htop.map_quotient (pCore 2 K)
  have hinj := sp4_equiv_of_cComponent_surjection hsqQ (pCore_quotient_pCore_eq_bot 2)
    hbar ChapterB.QuasisimpleSource.BinaryField.four.card_eq g hg
  exact ⟨MulEquiv.ofBijective g ⟨hinj,hg⟩⟩

end GenerationTwoOvergroup

/-- The supplied action image now identifies the original ambient kernel,
without assuming an intrinsic quotient marking. -/
theorem symplecticKernelRecognition (m : SourceA5TensorModel D e) :
    m.SymplecticKernelRecognition := by
  intro c W hr
  let := hr.normal
  intro hact
  obtain ⟨eK⟩ := c.symplectic_core_quotient_of_action hr hact
  exact (source_tensor_sp4_msCentralOrbit D m.sylow_not_normalizes_component
    c.M (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
    c.outside c.sylow (pResidual 2 c.M) c.component_product.1
    ChapterB.QuasisimpleSource.BinaryField.four.card_eq eK c.fitting_center.1
    c.component_product.2.2.2).2.1

namespace GenerationTwoOvergroup

/-- The original action marking suffices for the proved Frattini-small branch;
there is no remaining action-kernel hypothesis. -/
theorem sp4_block_of_marked_action_frattini_small (c : m.GenerationTwoOvergroup)
    (hr : IsPReduced 2
      (omegaOrbit (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)))
    (hsmall : ⁅pCore 2 c.M, pResidual 2 c.M⁆ ≤
      (frattini (pCore 2 c.M)).map (pCore 2 c.M).subtype ⊔
        omegaCenterIn (pCore 2 c.M)) :
    letI := hr.normal
    Nonempty (((pResidual 2 c.M).map (actionMk (omegaOrbit
      (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)))) ≃*
        Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) →
      ChapterC.IsSp4FourBlock (pResidual 2 c.M) := by
  let := hr.normal
  intro hact
  obtain ⟨eK⟩ := c.symplectic_core_quotient_of_action hr hact
  exact c.sp4_block_of_quotient_frattini_small eK hsmall

end GenerationTwoOvergroup

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
