module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.Components
public import Theory.GroupTheory.PrimeRankResidualCentralizer

/-!
# The exterior residual in the full component quotient

The actual residual F=L_A has F/O₂(F) isomorphic to PSL₅(2). Its embedding
in a selected component descends to K/Z(K) with a two-group kernel: that
kernel is central in F, and PSL₅(2) is centerless. Thus its perfect image
retains cubic rank at least two and an order divisible by 31. The original
module supplies a nontrivial normalized two-subgroup; if it vanished in the
central quotient, V=[V,F] would vanish already.

No simplification of the central cover is made, and no inner-action or
uniqueness hypothesis is added. The actual placement theorem supplies the
one required inclusion F≤K. LocalModels applies these data to the complete
characteristic-two catalogue in the exterior odd-normalizer consumer.
Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
open Chapter4 Chapter4.Section04 Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The literal two-local configuration forced by the placed exterior residual. -/
@[expose] def ExteriorComponentLocalData (Q : Type*) [Group Q] : Prop :=
  ∃ B P : Subgroup Q, Group.IsPerfect B ∧ 2 ≤ primeRank 3 B ∧
    IsPGroup 2 P ∧ P ≠ ⊥ ∧ B ≤ normalizer (P : Set Q) ∧ P ≤ B ∧ 31 ∣ Nat.card B

/-- Transfer both subgroups and their normalization along the actual model marking. -/
theorem ExteriorComponentLocalData.of_mulEquiv
    {Q S : Type*} [Group Q] [Finite Q] [Group S]
    (h : ExteriorComponentLocalData Q) (e : Q ≃* S) : ExteriorComponentLocalData S := by
  let : Finite S := Finite.of_equiv Q e.toEquiv
  obtain ⟨B,P,hB,hr,hP,hne,hn,hPB,h31⟩ := h
  let := hB
  refine ⟨B.map e.toMonoidHom, P.map e.toMonoidHom, Group.IsPerfect.map _,
    ?_, hP.map _, ?_, (map_mono hn).trans (P.le_normalizer_map e.toMonoidHom), map_mono hPB, ?_⟩
  · exact hr.trans_eq (primeRank_equiv 3 (e.subgroupMap B))
  · exact fun he => hne ((map_eq_bot_iff_of_injective P e.injective).mp he)
  · rwa [card_map_of_injective e.injective]

private theorem central_kernel_le_twoCore
    {F K : Type*} [Group F] [Finite F] [Group K]
    (e : (F ⧸ pCore 2 F) ≃* Representation.SL5TenDimensional.Group)
    (j : F →* K) (hj : Function.Injective j) :
    ((QuotientGroup.mk' (center K)).comp j).ker ≤ pCore 2 F := by
  let S := Representation.SL5TenDimensional.Group
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 5 (by decide)
  let : IsSimpleGroup S := Representation.SL5TenDimensional.projectiveEquiv.isSimpleGroup
  let : Group.IsPerfect S := Atlas.sl_perfect 5 (by decide)
  have hz : center S = ⊥ := by
    rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp ht)).elim
  let π : F →* S := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))
  have hs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  intro x hx
  have hc : j x ∈ center K := (QuotientGroup.eq_one_iff _).mp hx
  have hcx : x ∈ center F := mem_center_iff.mpr (fun y => hj (by
    simpa only [map_mul] using mem_center_iff.mp hc (j y)))
  have hcπ : π x ∈ center S := mem_center_iff.mpr (by
    intro y
    obtain ⟨z,rfl⟩ := hs y
    simpa only [map_mul] using congrArg π (mem_center_iff.mp hcx z))
  have he : π x = 1 := by simpa only [hz, mem_bot] using hcπ
  apply (QuotientGroup.eq_one_iff x).mp
  exact e.injective (he.trans (map_one e).symm)

/-- The placed residual has a perfect image of cubic rank at least two
normalizing a nontrivial two-subgroup in the literal central quotient. -/
theorem exterior_oddNormalizer_placed_local
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (hAM : A ≤ s.marking.M) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype) :
    ExteriorComponentLocalData (K ⧸ center K) := by
  let F := oddActorResidual L A
  let N := normalizer (A : Set G)
  let k := K.equivMapOfInjective N.subtype N.subtype_injective
  let j : F →* K := k.symm.toMonoidHom.comp (inclusion hFK)
  have hj : Function.Injective j := k.symm.injective.comp (inclusion_injective hFK)
  let f := (QuotientGroup.mk' (center K)).comp j
  obtain ⟨_, hmove, hVF, _⟩ := s.marking.centralizing_actor_cover h A hAM hodd hAV
  have hVF' : V ≤ F := hVF.trans (pCoreIn_le 2 F)
  let W := V.subgroupOf F
  have hFW : F ≤ normalizer (V : Set G) :=
    ((oddActorResidual_le L A).trans inf_le_left).trans D.normalizes
  have hn : (⊤ : Subgroup F) ≤ normalizer (W : Set F) := by
    intro x _ y
    exact hFW x.property (y : G)
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  let := D.elementary
  have hP : IsPGroup 2 (W.map f) := (IsElementaryAbelian.isPGroup 2 V).comap_subtype.map f
  have hne : W.map f ≠ ⊥ := by
    intro hb
    have hk := (map_eq_bot_iff W).mp hb
    have hc : V ≤ centralizer (F : Set G) := by
      intro v hv y hy
      have hz : j (⟨v,hVF' hv⟩ : F) ∈ center K :=
        (QuotientGroup.eq_one_iff _).mp (hk hv)
      have he : (⟨y,hy⟩ : F) * ⟨v,hVF' hv⟩ = ⟨v,hVF' hv⟩ * (⟨y,hy⟩ : F) :=
        hj (by simpa only [map_mul] using mem_center_iff.mp hz (j ⟨y,hy⟩))
      exact congrArg Subtype.val he
    exact D.ne_bot (hmove.trans (commutator_eq_bot_iff_le_centralizer.mpr hc))
  obtain ⟨⟨e,_⟩,_⟩ := s.marking.oddActorResidual_quotient h A hAM hodd hAV
  have hk : IsPGroup 2 f.ker := pCore_isPGroup.to_le (central_kernel_le_twoCore e j hj)
  have hr : 2 ≤ primeRank 3 F := by
    rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 F) pCore_isPGroup,
      primeRank_equiv 3 (e.trans Representation.SL5TenDimensional.projectiveEquiv)]
    exact Theory.SpecificGroups.Classical.BinaryFiveRanks.projective_threeRank_ge_two
  have hr' : primeRank 3 f.range = primeRank 3 F := by
    rw [MonoidHom.range_eq_map f]
    exact (ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 3) f hk
      (⊤ : Subgroup F)).trans (primeRank_equiv 3 Subgroup.topEquiv)
  have h31F : 31 ∣ Nat.card F := by
    have hc : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
      have hh := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
      calc
        _ = ∏ i : Fin 5, (2 ^ 5 - 2 ^ (i : ℕ)) := by
          simpa only [Nat.card_zmod, Nat.reduceSub, Nat.gcd_one_right, mul_one] using hh
        _ = 9999360 := by decide
    have hd : 31 ∣ Nat.card (F ⧸ pCore 2 F) := by
      rw [Nat.card_congr (e.trans Representation.SL5TenDimensional.projectiveEquiv).toEquiv, hc]
      decide
    exact hd.trans (card_quotient_dvd_card _)
  have h31 : 31 ∣ Nat.card f.range := by
    have hcount : Nat.card f.ker * Nat.card f.range = Nat.card F := by
      rw [← index_ker]
      exact f.ker.card_mul_index
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    have hc : Nat.Coprime 31 (Nat.card f.ker) := by
      rw [hn]
      exact (by decide : Nat.Coprime 31 2).pow_right n
    exact hc.dvd_of_dvd_mul_left (hcount.symm ▸ h31F)
  refine ⟨f.range,W.map f,Group.IsPerfect.range f,hr' ▸ hr,hP,hne,?_,map_le_range f W,h31⟩
  simpa only [← MonoidHom.range_eq_map] using
    (map_mono (f := f) hn).trans (W.le_normalizer_map f)

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
