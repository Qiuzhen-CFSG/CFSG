module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Rigidity
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.SectionCentralizers

/-!
# The complete noncyclic three-core branch

The contained-residual argument needs rigidity only for a normal three-group.
The direct cubic/Frattini argument in `Rigidity` proves that special case.
Combining it with the existing actual supercritical representation closes
F.6.16 without a universal F.6.13 assumption. Both the ambient isomorphisms
and their compatible marked residual lines are preserved.

Source: Aschbacher--Smith, F.6.16, printed pp.308--309,
combined manuscript of 1 March 2004.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.SourceAssembly
open Noncyclic
universe u
variable {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- The actual ternary representation and a contained local residual force
both residuals into a three-group. The original normal X is retained. -/
theorem residual_isThreeGroup_of_local_containment
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (X : Subgroup G) [X.Normal] (hX : IsPGroup 3 X) (hXP : X ≤ pCore 3 G)
    (h₁ : (pResidual 2 G₁).map G₁.subtype ≤ X)
    (f : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hc : ((pResidual 3 f.ker).map f.ker.subtype) ≤ centralizer (pCore 3 G : Set G)) :
    IsPGroup 3 (pResidual 2 G) := by
  let L₁ := (pResidual 2 G₁).map G₁.subtype
  let L₂ := (pResidual 2 G₂).map G₂.subtype
  have hQE := right_core_elementary_of_left_residual_le_threeGroup h hcore X hX h₁
  have hkill := right_residual_core_eq_bot_of_normal h hcore
  let Q := pCore 2 G₂
  let Qa := Q.map G₂.subtype
  let R := pResidual 2 G₂
  let J := (pCore 2 R).map R.subtype
  let Ka := J.map G₂.subtype
  let : IsElementaryAbelian 2 Qa := hQE
  have hJQ : J ≤ Q := le_sSup ⟨inferInstance, pCore_isPGroup.map R.subtype⟩
  have hKaQ : Ka ≤ Qa := map_mono hJQ
  let j : pCore 2 R →* Qa :=
    { toFun := fun x => ⟨x.val.val.val, hKaQ
        (mem_map_of_mem G₂.subtype (mem_map_of_mem R.subtype x.property))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hji : Function.Injective j := by
    intro x y he
    have hh : x.val.val.val = y.val.val.val := congrArg (fun z : Qa => z.val) he
    exact Subtype.ext (Subtype.ext (Subtype.ext hh))
  let : IsElementaryAbelian 2 (pCore 2 R) :=
    { toIsMulCommutative := ⟨⟨fun x y => hji (by simp only [map_mul]; exact IsMulCommutative.is_comm.comm _ _)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => hji (by
        rw [map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 Qa), map_one])) }
  let fR := f.comp (G₂.subtype.comp R.subtype)
  have hKker : pCore 2 R ≤ fR.ker :=
    Matrix.GeneralLinearGroup.three_kills_elementary_twoCore (isPPerfect_pResidual 2)
      (local_residual_quotient_card_three h.quotient_right) fR
  have hKaC : Ka ≤ centralizer (pCore 3 G : Set G) := by
    rintro _ ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    have hxker : x.val.val ∈ f.ker := hKker hx
    let z : f.ker := ⟨x.val.val, hxker⟩
    have hzres : z ∈ pResidual 3 f.ker := by
      apply mem_pResidual_of_orderOf_coprime
      obtain ⟨n, hn⟩ := pCore_isPGroup (p := 2) (G := R) ⟨x, hx⟩
      apply ((by decide : Nat.Coprime 3 2).pow_right n).of_dvd_right
      have he : z ^ (2 ^ n) = 1 := by
        apply Subtype.ext
        exact congrArg (fun w : pCore 2 R => w.val.val.val) hn
      exact orderOf_dvd_of_pow_eq_one he
    exact hc (mem_map_of_mem f.ker.subtype hzres)
  have hKaL : Ka ≤ L₂ := by
    apply map_mono
    exact map_subtype_le _
  have hKaG₂ : Ka ≤ G₂ := hKaL.trans (map_subtype_le _)
  have hKaN : G₂ ≤ normalizer (Ka : Set G) := by
    have hn := J.le_normalizer_map G₂.subtype
    simpa only [J, Ka, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hn
  have hL₁N : L₁ ≤ normalizer (Ka : Set G) :=
    (le_centralizer_iff.mpr (hKaC.trans (centralizer_le (h₁.trans hXP)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hKabot : Ka = ⊥ := by
    have hkill' : (Ka.subgroupOf (Qa ⊔ L₁)).Normal → Ka = ⊥ := by
      simpa only [Ka, J, Qa, Q, R, L₁, map_map] using hkill
    apply hkill'
    apply (normal_subgroupOf_iff_le_normalizer (hKaQ.trans le_sup_left)).mpr
    exact sup_le ((map_subtype_le Q).trans hKaN) hL₁N
  have hKR : pCore 2 R = ⊥ := by
    apply map_injective R.subtype_injective
    apply map_injective G₂.subtype_injective
    simpa only [Subgroup.map_bot] using hKabot
  have hR : IsPGroup 3 R := by
    have hq : IsPGroup 3 (R ⧸ pCore 2 R) :=
      IsPGroup.of_card (n := 1) (local_residual_quotient_card_three h.quotient_right)
    exact hq.of_equiv ((QuotientGroup.quotientMulEquivOfEq hKR).trans QuotientGroup.quotientBot)
  have hjoin : IsPGroup 3 (X ⊔ L₂ : Subgroup G) :=
    hX.to_sup_of_normal_left (hR.map G₂.subtype)
  apply hjoin.to_le
  rw [h.twoResidual_eq_sup]
  exact sup_le (h₁.trans le_sup_left) le_sup_right

/-- The original noncyclic three-core supplies its own supercritical witness;
both the contained and noncontained branches are now proved. -/
theorem residual_isThreeGroup_of_rank_two
    (h : IsGoldschmidtTriple G₁ G₂) (hprime : pPrimeCore 3 G = ⊥)
    (hr : primeRank 3 G ≤ 2) (hn : ¬ IsCyclic (pCore 3 G)) :
    IsPGroup 3 (pResidual 2 G) := by
  have hcore := twoCore_eq_bot_of_primeToThreeCore_eq_bot hprime
  obtain ⟨X, hX, _, hm⟩ := exists_three_core_supercritical hr hn
  let : X.Characteristic := hX.characteristic
  obtain ⟨j, hj, hc⟩ := supercritical_ternary_action hr X hX
  have hp : IsPGroup 3 (X.map (pCore 3 G).subtype) :=
    (pCore_isPGroup.to_subgroup X).map (pCore 3 G).subtype
  by_cases h₁ : (pResidual 2 G₁).map G₁.subtype ≤ X.map (pCore 3 G).subtype
  · exact residual_isThreeGroup_of_local_containment h hcore _ hp
      (map_subtype_le X) h₁ _ hc
  by_cases h₂ : (pResidual 2 G₂).map G₂.subtype ≤ X.map (pCore 3 G).subtype
  · exact residual_isThreeGroup_of_local_containment h.symm hcore _ hp
      (map_subtype_le X) h₂ _ hc
  exact residual_isThreeGroup_of_supercritical_noncontainments h hcore hprime hr X hX hm h₁ h₂

variable {Ghat : Type u} [Group Ghat] [Finite Ghat] {K : GroupClass.{u}}

/-- The genuine SQTK cover gives the rank and prime-to-three-core hypotheses. -/
theorem residual_isThreeGroup_of_cover
    (hhat : IsSQTK K Ghat) (e : G ≃* (Ghat ⧸ pPrimeCore 3 Ghat))
    (h : IsGoldschmidtTriple G₁ G₂) (hn : ¬ IsCyclic (pCore 3 G)) :
    IsPGroup 3 (pResidual 2 G) :=
  residual_isThreeGroup_of_rank_two h
    (primeToThreeCore_eq_bot_of_quotient e) (three_rank_le_two_of_cover hhat e) hn

/-- Full F.6.16 with all earlier universal source inputs discharged. -/
theorem source_lemma_F_6_16
    (hhat : IsSQTK K Ghat) (e : G ≃* (Ghat ⧸ pPrimeCore 3 Ghat))
    (h : IsGoldschmidtTriple G₁ G₂) (hn : ¬ IsCyclic (pCore 3 G)) :
    IsPGroup 3 (pResidual 2 G) ∧
      ((Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* Multiplicative (ZMod 2)) ∧
        (pCore 2 G₁).map G₁.subtype = ⊥ ∧ (pCore 2 G₂).map G₂.subtype = ⊥) ∨
      Nonempty (G ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      Nonempty (G ≃* MarkedCubicRecognition.HeisenbergExtension)) := by
  have hL := residual_isThreeGroup_of_cover hhat e h hn
  exact ⟨hL, MarkedRecognition.three_group_alternatives_of_cover
    sectionCentralizerInput hhat e h hL hn⟩

/-- The literal marked residual lines and ambient action in the four-group case. -/
theorem source_marked_models
    (hhat : IsSQTK K Ghat) (e : G ≃* (Ghat ⧸ pPrimeCore 3 Ghat))
    (h : IsGoldschmidtTriple G₁ G₂) (hn : ¬ IsCyclic (pCore 3 G))
    (hnot : ¬ Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* Multiplicative (ZMod 2))) :
    Nonempty (MarkedRecognition.MarkedModel G₁ G₂ MarkedCubicRecognition.Nine
      MarkedCubicRecognition.nineAction
      (MonoidHom.inl MarkedCubicRecognition.C3 MarkedCubicRecognition.C3).range
      (MonoidHom.inr MarkedCubicRecognition.C3 MarkedCubicRecognition.C3).range) ∨
    Nonempty (MarkedRecognition.MarkedModel G₁ G₂ (HeisenbergPrime 3)
      MarkedCubicRecognition.heisenbergAction
      MarkedCubicRecognition.leftAxis.range MarkedCubicRecognition.rightAxis.range) :=
  MarkedRecognition.marked_models_of_cover sectionCentralizerInput hhat e h
    (residual_isThreeGroup_of_cover hhat e h hn) hn hnot

end CFSG.Quasithin.ChapterF.SourceAssembly
