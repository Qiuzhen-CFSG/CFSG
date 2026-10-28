module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionCore
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalCompletion
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# Overcomponent cores in the block branches of 5.2.8

Let K = O²(H). In the L₃ and Sp₄ rows the original S lies in K, so
O₂(H) = O₂(K). If K ≤ J ∈ L(G,T), subnormality of J in JT and the
full ambient Sylow give O₂(J) ≤ O₂(JT) ≤ O₂(H). The concrete block
cores are abelian. Hence O₂(K) centralizes O₂(J), and characteristic
two in J forces equality. In particular J normalizes the actual O₂(K).
This avoids assuming either K normal in J or J normal in G.

Both compatible amalgam orientations give this equality. The original
PSL₂ quotient then embeds in J/O₂(J) through the literal inclusion;
its equation on quotient representatives retains the source convention.
The Chapter12 extension applies this to the prepared whole-residual pair.

These are the core and quotient steps of the linear/symplectic paragraph
of 5.2.8. The remaining overcomponent classification, exhaustive F.1.12
comparison and ambient completion recognition remain open. The other
concrete rows, including U₅(4) and general Ree, remain in the catalogue.
Source: Aschbacher–Smith 5.2.8, printed p.652 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Containment of the original S in K removes the possible extra two-core of H. -/
theorem residual_core_eq_of_sourceS_le
    {T : Sylow 2 G} {L H : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) (hS : sourceS L H ≤ residual H) :
    H.pCoreIn 2 = (residual H).pCoreIn 2 := by
  have hQ : H.pCoreIn 2 ≤ sourceS L H :=
    Chapter3.twoCore_le_of_sylow_le T (le_inf hTL hTH) inf_le_right
  exact le_antisymm
    ((le_inf (hQ.trans hS) le_rfl).trans (inf_pCoreIn_le_of_le 2 (map_subtype_le _)))
    (pCoreIn_mono_of_normalizes (map_subtype_le _) (le_normalizer_residual H))

/-- An abelian residual core is the exact core of every local overcomponent. -/
theorem abelian_residual_overcomponent_core
    {T : Sylow 2 G} {H J : Subgroup G}
    (hE : IsEvenCharacteristicAt T) (hTH : (T : Subgroup G) ≤ H)
    (hcore : H.pCoreIn 2 = (residual H).pCoreIn 2)
    (ha : IsMulCommutative (pCore 2 (residual H)))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : residual H ≤ J) :
    J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
      J ≤ normalizer ((residual H).pCoreIn 2 : Set G) := by
  have hHJ : H ≤ J ⊔ (T : Subgroup G) := by
    rw [← residual_sup_sylow T H hTH]
    exact sup_le_sup hKJ le_rfl
  have hle : J.pCoreIn 2 ≤ (residual H).pCoreIn 2 :=
    (pCoreAmbient_mono_of_isSubnormalIn J (J ⊔ (T : Subgroup G)) 2
      le_sup_left hJ.1.subnormal).trans
        ((Chapter3.twoCore_le_of_sylow_le T hTH hHJ).trans_eq hcore)
  let := ha
  let : IsMulCommutative ((residual H).pCoreIn 2) :=
    inferInstanceAs (IsMulCommutative ((pCore 2 (residual H)).map (residual H).subtype))
  have hchar := Chapter1.mem_He_iff.mpr
    (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T hE hJ)
  have he : J.pCoreIn 2 = (residual H).pCoreIn 2 := by
    apply le_antisymm hle
    intro x hx
    apply hchar
    refine ⟨hKJ (map_subtype_le _ hx), ?_⟩
    exact mem_centralizer_iff.mpr (fun y hy => setLike_mul_comm (hle hy) hx)
  refine ⟨he, ?_⟩
  rw [← he]
  exact J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))

private theorem core_commutative_of_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) [IsMulCommutative (pCore 2 Y)] : IsMulCommutative (pCore 2 X) := by
  let a := (e.subgroupMap (pCore 2 X)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  exact IsMulCommutative.of_comm (fun x y => a.injective (by
    simp only [map_mul, mul_comm' (a x) (a y)]))

private theorem linear_core_commutative
    (F : Type) [Field F] [Finite F] [CharP F 2] (j : Bool) :
    IsMulCommutative (pCore 2 (Matrix.PSL3.LinearThree.CoveredLocals.localProjective F j)) := by
  open Matrix.PSL3.LinearThree in
  have h (X : Type) [Group X] (e : X ≃* Matrix.SL2.Affine F) :
      IsMulCommutative (pCore 2 X) := by
    let a := ChapterC.SL2Affine.coreEquiv e
    exact IsMulCommutative.of_comm (fun x y => a.symm.injective (by simp only [map_mul, mul_comm]))
  cases j
  · exact h _ (Matrix.PSL3.LinearThree.lineLocalEquivAffine F)
  · exact h _ (Matrix.PSL3.LinearThree.pointLocalEquivAffine F)

private theorem symplectic_core_commutative
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2^m) (j : Bool) :
    IsMulCommutative (pCore 2 (if j then Theory.SpecificGroups.SymplecticFour.pointLocal (F := F)
      else Theory.SpecificGroups.SymplecticFour.planeLocal : Subgroup _)) := by
  open Theory.SpecificGroups.SymplecticFour in
  cases j
  · change IsMulCommutative (pCore 2 (planeLocal (F := F)))
    rw [planeLocal_core_eq hF hm]
    infer_instance
  · change IsMulCommutative (pCore 2 (pointLocal (F := F)))
    rw [pointLocal_core_eq hF hm]
    infer_instance

/-- The actual L₃ comparison supplies core equality and relative core normality
in every local overcomponent, in both orientations. -/
theorem Preparation.linear_overcomponent_core
    {T : Sylow 2 G} {L W H A B J : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : residual H ≤ J) :
    J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
      J ≤ normalizer ((residual H).pCoreIn 2 : Set G) := by
  have hS := d.linear_sourceS_le_factors h hTH hp F hm hF he 1
  apply abelian_residual_overcomponent_core (h.qtke.evenCharacteristic T) hTH
    (residual_core_eq_of_sourceS_le h.sylow_normalizes hTH hS) _ hJ hKJ
  rcases he with he | he <;> obtain ⟨e⟩ := he
  · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hTH hp F hm hF 1 false e.right).2.1
    let := linear_core_commutative F false
    exact core_commutative_of_equiv a
  · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hTH hp F hm hF 1 true e.right).2.1
    let := linear_core_commutative F true
    exact core_commutative_of_equiv a

/-- The actual Sp₄ comparison supplies the same overcomponent-core equality. -/
theorem Preparation.symplectic_overcomponent_core
    {T : Sylow 2 G} {L W H A B J : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : residual H ≤ J) :
    J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
      J ≤ normalizer ((residual H).pCoreIn 2 : Set G) := by
  have hS := d.symplectic_sourceS_le_factors h hTH hp F hm hF he 1
  apply abelian_residual_overcomponent_core (h.qtke.evenCharacteristic T) hTH
    (residual_core_eq_of_sourceS_le h.sylow_normalizes hTH hS) _ hJ hKJ
  rcases he with he | he <;> obtain ⟨e⟩ := he
  · obtain ⟨hm',⟨a⟩,_⟩ := BlockComparison.symplectic_parabolic_factor d h hTH hp F hm hF 1 false e.right
    let := symplectic_core_commutative F hm' hF false
    exact core_commutative_of_equiv a
  · obtain ⟨hm',⟨a⟩,_⟩ := BlockComparison.symplectic_parabolic_factor d h hTH hp F hm hF 1 true e.right
    let := symplectic_core_commutative F hm' hF true
    exact core_commutative_of_equiv a

omit [Finite G] in
/-- Equality of the embedded cores makes the literal inclusion injective on
intrinsic core quotients. The equation fixes the quotient-map convention. -/
private theorem core_quotient_embedding_of_core_eq {K J : Subgroup G}
    (hKJ : K ≤ J) (hc : J.pCoreIn 2 = K.pCoreIn 2) :
    ∃ f : (K ⧸ pCore 2 K) →* (J ⧸ pCore 2 J), Function.Injective f ∧
      ∀ x : K, f (QuotientGroup.mk' (pCore 2 K) x) =
        QuotientGroup.mk' (pCore 2 J) (inclusion hKJ x) := by
  have he : (pCore 2 J).comap (inclusion hKJ) = pCore 2 K := by
    ext x
    change inclusion hKJ x ∈ pCore 2 J ↔ x ∈ pCore 2 K
    rw [← mem_map_iff_mem J.subtype_injective, ← mem_map_iff_mem K.subtype_injective]
    change (x : G) ∈ J.pCoreIn 2 ↔ (x : G) ∈ K.pCoreIn 2
    rw [hc]
  let f := QuotientGroup.map (pCore 2 K) (pCore 2 J) (inclusion hKJ) he.ge
  refine ⟨f, ?_, fun _ => rfl⟩
  apply (MonoidHom.ker_eq_bot_iff f).mp
  rw [QuotientGroup.ker_map, he, QuotientGroup.map_mk'_self]

/-- The linear and symplectic branches of 5.2.8 have the same core in every
local overcomponent. Their original PSL₂ quotient embeds via the actual
inclusion, with no assumed core equality or right-maximality hypothesis. -/
theorem Preparation.block_overcomponent_quotient
    {T : Sylow 2 G} {L W H A B J : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he :
      (Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
       Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse)) ∨
      (Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
       Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : residual H ≤ J) :
    J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
      J ≤ normalizer ((residual H).pCoreIn 2 : Set G) ∧
      ClassicalGroup.IsPSL (residual H ⧸ pCore 2 (residual H)) 2 (2^n) ∧
      ∃ f : (residual H ⧸ pCore 2 (residual H)) →* (J ⧸ pCore 2 J),
        Function.Injective f ∧ ∀ x : residual H,
          f (QuotientGroup.mk' (pCore 2 (residual H)) x) =
            QuotientGroup.mk' (pCore 2 J) (inclusion hKJ x) := by
  have hc : J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
      J ≤ normalizer ((residual H).pCoreIn 2 : Set G) := by
    rcases he with he | he
    · exact d.linear_overcomponent_core h hTH hp F hm hF he hJ hKJ
    · exact d.symplectic_overcomponent_core h hTH hp F hm hF he hJ hKJ
  have hb : ChapterC.IsL2EvenBlock (residual H) n := by
    rcases he with he | he
    · exact (d.linear_amalgam_blocks h hTH hp F hm hF he).2.2
    · exact (d.symplectic_amalgam_blocks h hTH hp F hm hF he).2.2
  obtain ⟨_,_,_,_,_,_,hlin,_⟩ := hb
  exact ⟨hc.1,hc.2,hlin,core_quotient_embedding_of_core_eq hKJ hc.1⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
