module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedJankoPlacements
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFourPlacement

/-!
# The moved J₄ residual normalizer has even index

A maximal two-local containing a full Sylow subgroup normalizes a nonzero
normal elementary subgroup of that Sylow. The checked J₄ catalogue puts a
minimal invariant subgroup either in the Mathieu local or in a pure row
of order at most eight. The former excludes the full SL₃(4) cover. In the
latter, every nontrivial image of the perfect cover retains its simple
central quotient of order 20160, larger than GL₃(2); hence the small subgroup
centralizes the residual, contrary to its proved odd centralizer.

Thus the actual residual normalizer contains no full Sylow subgroup and has
even index. The application uses its literal component quotient and the
original full covering action. The remaining even-index local placement
and its exclusion stay with qt-d-1222-natural-odd-kernel-normalizer; no
exhaustive classification of all J₄ two-locals is asserted here.

Source: Aschbacher--Smith, proof of 4.4.3, printed p.622, and GLS3 Table5.3i.
The imported J₄ catalogue retains its native matrix certificate attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem small_action_trivial
    (F : BinaryField) (hF : F.degree = 2)
    {X E : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    [IsQuasisimple (X ⧸ pCore 2 X)] [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (e : (X ⧸ pCore 2 X) ≃* SL(3,F.Carrier)) (hE : Nat.card E ≤ 8)
    (f : X →* MulAut E) : f = 1 := by
  by_contra hne
  let q := QuotientGroup.mk' (pCore 2 X)
  have hproper : f.ker ≠ ⊤ := fun ht => hne (MonoidHom.ker_eq_top_iff.mp ht)
  have hc : f.ker.map q ≤ center (X ⧸ pCore 2 X) := by
    rcases IsQuasisimple.normal_le_center_or_eq_top (f.ker.map q) with hc | ht
    · exact hc
    · have hsup : f.ker ⊔ pCore 2 X = ⊤ := by
        have hm := congrArg (Subgroup.comap q) ht
        simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hm
      have hp := isPGroup_quotient_of_sup_eq_top f.ker (pCore 2 X) pCore_isPGroup hsup
      let : Group.IsNilpotent (X ⧸ f.ker) := hp.isNilpotent
      exact (hproper (top_unique (by simpa only [solvableResidual_eq_top] using
        solvableResidual_le_of_solvable_quotient f.ker))).elim
  let c := (QuotientGroup.mk' (center (X ⧸ pCore 2 X))).comp q
  have hk : f.ker ≤ c.ker := by
    intro x hx
    exact (QuotientGroup.eq_one_iff (q x)).mpr (hc (mem_map_of_mem q hx))
  let g := QuotientGroup.lift f.ker c hk
  have hcSur : Function.Surjective c :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hg : Function.Surjective g :=
    QuotientGroup.lift_surjective_of_surjective f.ker c hcSur hk
  let a := QuotientGroup.quotientKerEquivRange f
  have hbound := Nat.card_le_card_of_surjective (g.comp a.symm.toMonoidHom)
    (hg.comp a.symm.surjective)
  have hquot : Nat.card ((X ⧸ pCore 2 X) ⧸ center (X ⧸ pCore 2 X)) = 20160 := by
    have hcard := card_eq_card_quotient_mul_card_subgroup (center (X ⧸ pCore 2 X))
    have hz : Nat.card (center (X ⧸ pCore 2 X)) = 3 := by
      rw [Nat.card_congr (centerCongr e).toEquiv,Atlas.ExceptionalSupport.card_sl_center]
      norm_num [F.card_eq,hF]
    rw [hz,Nat.card_congr e.toEquiv,linear_three_order,F.card_eq,hF] at hcard
    omega
  change Nat.card ((X ⧸ pCore 2 X) ⧸ center (X ⧸ pCore 2 X)) ≤ Nat.card f.range at hbound
  rw [hquot] at hbound
  have hAut : Nat.card (MulAut E) ≤ 168 := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
    have hn3 : n ≤ 3 := by
      have hp : 2 ^ n < 2 ^ 4 := by rw [←hn]; omega
      have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hp
      omega
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E n hn]
    interval_cases n <;> norm_num [Fin.prod_univ_succ]
  have hsmall := (Nat.card_le_card_of_injective f.range.subtype
    f.range.subtype_injective).trans hAut
  omega

private noncomputable def fixedSylow : Sylow 2 Janko4.Model :=
  Janko4.OuterReduction.OddIndex.twoSubgroup_isPGroup.toSylow (by
    rw [Janko4.OuterReduction.OddIndex.twoSubgroup,index_map_subtype,
      Janko4.OuterReduction.OddIndex.localTwoSubgroup_index]
    exact Nat.Prime.not_dvd_mul Nat.prime_two (by decide)
      Janko4.OuterReduction.max1_odd_index_unconditional)

private theorem fixed_cover_not_sylow_local
    (F : BinaryField) (hF : F.degree = 2) (X M : Subgroup Janko4.Model)
    [Group.IsPerfect X] [IsQuasisimple (X ⧸ pCore 2 X)]
    (e : (X ⧸ pCore 2 X) ≃* SL(3,F.Carrier))
    (ho : Odd (Nat.card (centralizer (X : Set Janko4.Model))))
    (hXM : X ≤ M) (hM : IsMaximalTwoLocal M)
    (hS : Janko4.OuterReduction.OddIndex.twoSubgroup ≤ M) : False := by
  obtain ⟨R,hR,_,heR,hMR⟩ := exists_normal_elementary_normalizer_of_sylow_le fixedSylow hM hS
  let E := R.map (fixedSylow : Subgroup Janko4.Model).subtype
  have he : IsElementaryAbelian 2 E := by
    let := heR
    exact IsElementaryAbelian.map _
  have hne : E ≠ ⊥ := fun hz => hR ((map_eq_bot_iff_of_injective _ Subtype.val_injective).mp hz)
  rcases ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFour.fixed_pair_minimal_alternative
    M E (map_subtype_le R) hne he hS hMR.le with hmax | ⟨B,hB,_,heB,hcard,hMB⟩
  · have hh := Normalizers.FixedSummand.Centralizer.janko_cover_not_le_mathieu_conjugate F hF X e 1
    apply hh
    intro x hx
    exact ⟨x,hmax (hXM hx),by simp⟩
  · let := heB
    have hXB := hXM.trans hMB
    let f := B.normalizerMonoidHom.comp (inclusion hXB)
    have hf := small_action_trivial F hF e hcard f
    have hXC : X ≤ centralizer (B : Set Janko4.Model) := by
      intro x hx
      have hk : inclusion hXB ⟨x,hx⟩ ∈ B.normalizerMonoidHom.ker := by
        change f ⟨x,hx⟩ = 1
        rw [hf]
        rfl
      rwa [normalizerMonoidHom_ker] at hk
    have hBC := le_centralizer_iff.mp hXC
    have h2 : 2 ∣ Nat.card B := by
      obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
      have hn0 : n ≠ 0 := by
        intro hn0
        rw [hn0,pow_zero] at hn
        exact hB (B.eq_bot_of_card_eq hn)
      rw [hn]
      exact dvd_pow_self 2 hn0
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr
      (h2.trans (card_dvd_of_le hBC)))

/-- The full covering residual with odd centralizer cannot lie in a maximal
two-local containing a full Sylow subgroup of the native J₄ carrier. -/
theorem janko_cover_not_sylow_local
    (F : BinaryField) (hF : F.degree = 2) (X M : Subgroup Janko4.Model)
    [Group.IsPerfect X] [IsQuasisimple (X ⧸ pCore 2 X)]
    (e : (X ⧸ pCore 2 X) ≃* SL(3,F.Carrier))
    (ho : Odd (Nat.card (centralizer (X : Set Janko4.Model))))
    (hXM : X ≤ M) (hM : IsMaximalTwoLocal M)
    (S : Sylow 2 Janko4.Model) (hSM : (S : Subgroup Janko4.Model) ≤ M) : False := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Janko4.Model S fixedSylow
  let f := MulAut.conj g
  have hS : (S : Subgroup Janko4.Model).map f.toMonoidHom =
      Janko4.OuterReduction.OddIndex.twoSubgroup := congrArg Sylow.toSubgroup hg
  let Y := X.map f.toMonoidHom
  let a := f.subgroupMap X
  let q := a.toMonoidHom.quotientPCoreEquivOfSurjective a.surjective
    (by rw [a.toMonoidHom.ker_eq_bot a.injective]; exact IsPGroup.of_subsingleton 2 _)
  let : Group.IsPerfect Y := Group.IsPerfect.map f.toMonoidHom
  let : IsQuasisimple (Y ⧸ pCore 2 Y) := IsQuasisimple.of_mulEquiv q
  have hc : (centralizer (X : Set Janko4.Model)).map f.toMonoidHom =
      centralizer (Y : Set Janko4.Model) := by
    simpa only [Y,coe_map,MulEquiv.coe_toMonoidHom] using map_centralizer_equiv (X : Set Janko4.Model) f
  have hy : Odd (Nat.card (centralizer (Y : Set Janko4.Model))) := by
    rw [←hc,card_map_of_injective f.injective]
    exact ho
  apply fixed_cover_not_sylow_local F hF Y (M.map f.toMonoidHom)
    (q.symm.trans e) hy (map_mono hXM) (Theory.Quasithin.isMaximalTwoLocal_map f hM)
  rw [←hS]
  exact map_mono hSM

/-- Every maximal two-local containing this residual has even index. -/
theorem janko_cover_local_even_index
    (F : BinaryField) (hF : F.degree = 2) (X M : Subgroup Janko4.Model)
    [Group.IsPerfect X] [IsQuasisimple (X ⧸ pCore 2 X)]
    (e : (X ⧸ pCore 2 X) ≃* SL(3,F.Carrier))
    (ho : Odd (Nat.card (centralizer (X : Set Janko4.Model))))
    (hXM : X ≤ M) (hM : IsMaximalTwoLocal M) : 2 ∣ M.index := by
  by_contra hi
  let R : Sylow 2 M := default
  have hRi : ¬ 2 ∣ ((R : Subgroup M).map M.subtype).index := by
    rw [index_map_subtype]
    exact Nat.Prime.not_dvd_mul Nat.prime_two R.not_dvd_index hi
  let S := (R.isPGroup'.map M.subtype).toSylow hRi
  exact janko_cover_not_sylow_local F hF X M e ho hXM hM S (map_subtype_le _)

open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal residual of the original moved component has normalizer of
even index in its J₄ central quotient. -/
theorem moved_janko_normalizer_even_index
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (hf : S.field.degree = 2) (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (ek : (K ⧸ center K) ≃* Janko4.Model) :
    let X := ((movedComponentSubgroup A (oddActorResidual L A) K).map
      (QuotientGroup.mk' (center K))).map ek.toMonoidHom
    2 ∣ (normalizer (X : Set Janko4.Model)).index := by
  let X := (movedComponentSubgroup A (oddActorResidual L A) K).map
    (QuotientGroup.mk' (center K))
  let Y := X.map ek.toMonoidHom
  obtain ⟨hperfect,⟨a⟩⟩ := moved_projected_cover D S hA hodd K hFK
  let : Group.IsPerfect X := hperfect
  let : Group.IsPerfect Y := Group.IsPerfect.map ek.toMonoidHom
  let t := ek.subgroupMap X
  let q := t.toMonoidHom.quotientPCoreEquivOfSurjective t.surjective
    (by rw [t.toMonoidHom.ker_eq_bot t.injective]; exact IsPGroup.of_subsingleton 2 _)
  let := S.source.toHypothesis1221.quasisimple
  let : IsQuasisimple (Y ⧸ pCore 2 Y) := IsQuasisimple.of_mulEquiv (a.symm.trans q)
  have ho := moved_janko_residual_centralizer_odd D S hA hodd hu K hFK hf e ek
  have hc : (centralizer (X : Set (K ⧸ center K))).map ek.toMonoidHom =
      centralizer (Y : Set Janko4.Model) := by
    simpa only [Y,coe_map,MulEquiv.coe_toMonoidHom] using
      map_centralizer_equiv (X : Set (K ⧸ center K)) ek
  have hy : Odd (Nat.card (centralizer (Y : Set Janko4.Model))) := by
    rw [←hc,card_map_of_injective ek.injective]
    exact ho
  obtain ⟨_,_,hmax⟩ := moved_projected_radical D S hA hodd hu K hFK
  have hmaxJ := Theory.Quasithin.isMaximalTwoLocal_map ek hmax
  rw [map_equiv_normalizer_eq] at hmaxJ
  exact janko_cover_local_even_index S.field hf Y _
    (q.symm.trans (a.trans e)) hy Y.le_normalizer hmaxJ

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
