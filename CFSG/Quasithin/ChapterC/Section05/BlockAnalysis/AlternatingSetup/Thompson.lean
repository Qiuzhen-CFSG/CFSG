module

public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup.Action
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Baumann
public import CFSG.Quasithin.ChapterB.Section02.RankLifting

/-!
# The source Thompson and Baumann images

B.2.4 turns a nontrivial maximum elementary image into an offender. The
all-image B.3.2 bound makes its codimension exact, so the image contains a
transposition. Together with the original A₅ image this proves that the
normalizing group acts as S₅. The genuine S₅ stable-family calculation then
identifies both J(T) and Baum(T) with the transposition four-group.

Source: Aschbacher–Smith C.5.4(3), printed p.155.
-/
public section
open Subgroup Stellmacher BinaryPermutation Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
open ChapterB.Offenders
variable {G : Type*} [Group G] [Finite G]
variable (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* Equiv.Perm (Fin 5)) (hker : q.ker = centralizer (V : Set G))
    (e : V ≃* Multiplicative (core (Fin 5)))
    (he : ∀ (s : G) (u : V),
      (e.symm (Multiplicative.ofAdd
        (coreRepresentation (Fin 5) (q s) (e u).toAdd)) : G) = s * (u : G) * s⁻¹)

include he hker

theorem fixedCodim_coordinates (A : Subgroup G) :
    ChapterB.BaumannArgument.fixedCodim V A =
      fixedCodim (coreRepresentation (Fin 5)) (A.map q) := by
  let π := QuotientGroup.mk' (centralizer (V : Set G))
  let f := QuotientGroup.lift _ q hker.symm.le
  let ρ := NormalElementaryQuotient.representation V π
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let E : Additive V ≃ₗ[ZMod 2] core (Fin 5) :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) e.bijective
  have hE : ∀ g v, E (ρ g v) = coreRepresentation (Fin 5) (f g) (E v) := by
    intro g v
    obtain ⟨s,rfl⟩ := QuotientGroup.mk'_surjective _ g
    apply Multiplicative.ofAdd.injective
    apply e.symm.injective
    apply Subtype.ext
    change (e.symm (e (ρ (π s) v).toMul) : G) = _
    rw [e.symm_apply_apply]
    exact (NormalElementaryQuotient.representation_apply V π
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) s v).trans (he s v.toMul).symm
  rw [ChapterB.BaumannArgument.fixedCodim_eq_centralizer_quotient V π
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _),
    fixedCodim_map_equivariant ρ (coreRepresentation (Fin 5)) f E hE, map_map]
  rfl

theorem max_image_caseA (R A : Subgroup G) (hVR : V ≤ R)
    (hA : A ∈ elementaryAbelianMaxSubgroups R) (hne : A.map q ≠ ⊥) :
    CaseAFamily 5 (A.map q) := by
  let : IsElementaryAbelian 2 A := hA.2.1
  have hb := ChapterB.lemma_B_2_4_1 R V A hVR hA.1 0
    (by rw [maxOrder_eq_card_of_mem R A hA, Nat.sub_zero]) q hker hne
  change ChapterB.BaumannArgument.fixedCodim V A - 0 ≤ rank (A.map q) at hb
  rw [Nat.sub_zero,fixedCodim_coordinates V q hker e he] at hb
  have hel : IsElementaryTwo (A.map q) := ⟨hne,IsElementaryAbelian.map q⟩
  have hn : rank (A.map q) ≤ fixedCodim (coreRepresentation (Fin 5)) (A.map q) := by
    by_contra h
    exact Odd.not_isStrongOffender_core (Or.inl rfl) (A.map q)
      ⟨hel,Nat.lt_of_not_ge h⟩
  apply Odd.caseAFamily_of_elementary_and_fixedCodim_full_eq_rank (Or.inl rfl) hel
  rw [← fixedCodim_core_eq_full_odd (Fin 5) (by decide)]
  exact le_antisymm hb hn

theorem surjective_of_thompson_moves (R : Subgroup G) (hVR : V ≤ R)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (V : Set G))
    (hA : alternatingGroup (Fin 5) ≤ q.range) : Function.Surjective q := by
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups R, A.map q ≠ ⊥ := by
    by_contra! hall
    apply hJ
    rw [← hker]
    exact sSup_le fun A hA => (Subgroup.map_eq_bot_iff A).mp (hall A hA)
  obtain ⟨A,hAR,hne⟩ := hex
  obtain ⟨n,hn,_,a,ha⟩ := max_image_caseA V q hker e he R A hVR hAR hne
  have hs : ((MulAut.conj a) (pairSwap 5 0)).IsSwap :=
    ⟨a 0,a 1,a.injective.ne (by decide),Equiv.symm_trans_swap_trans (0 : Fin 5) 1 a⟩
  have ht : (MulAut.conj a) (pairSwap 5 0) ∈ q.range := by
    apply map_le_range q A
    rw [ha]
    exact mem_map_of_mem _ (pairSwap_mem 0 hn)
  have hdvd := index_dvd_of_le hA
  rw [alternatingGroup.index_eq_two] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hi | hi
  · exact MonoidHom.range_eq_top.mp (index_eq_one.mp hi)
  · rw [Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi,
      Equiv.Perm.mem_alternatingGroup,hs.sign_eq] at ht
    exact (by decide : (-1 : ℤˣ) ≠ 1) ht |>.elim

omit [Finite G] in
/-- Coordinates on the whole source image, with surjectivity now proved. -/
theorem quotient_equivariant (hq : Function.Surjective q) :
    let p := e.toMonoidHom.toAdditiveLeft.toZModLinearMap 2
    ∀ g v, p (NormalElementaryQuotient.representation V q hq hker g v) =
      coreRepresentation (Fin 5) g (p v) := by
  intro p g v
  obtain ⟨s,rfl⟩ := hq g
  apply Multiplicative.ofAdd.injective
  apply e.symm.injective
  apply Subtype.ext
  change (e.symm (e (NormalElementaryQuotient.representation V q hq hker (q s) v).toMul) : G) = _
  rw [e.symm_apply_apply]
  exact (NormalElementaryQuotient.representation_apply V q hq hker s v).trans (he s v.toMul).symm

theorem thompson_baumann_image (T : Sylow 2 G) (hVT : V ≤ T)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hA : alternatingGroup (Fin 5) ≤ q.range) :
    (elementaryAbelianMaxJ (T : Subgroup G)).map q =
        (ChapterB.baumann (T : Subgroup G)).map q ∧
      ∃ a : Equiv.Perm (Fin 5), (ChapterB.baumann (T : Subgroup G)).map q =
        (ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom := by
  have hq := surjective_of_thompson_moves V q hker e he T hVT hJ hA
  let p := e.toMonoidHom.toAdditiveLeft.toZModLinearMap 2
  have hp : Function.Bijective p := e.bijective
  have h := SymmetricFive.source_thompson_baumann V T hVT q hq hker p hp.2
    (quotient_equivariant V q hker e he hq) (by
      intro v hv g hg
      have hz : v = 0 := hp.1 (hv.trans (map_zero p).symm)
      rw [hz,map_zero]) hJ
  exact ⟨h.1,h.2.2⟩
end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
