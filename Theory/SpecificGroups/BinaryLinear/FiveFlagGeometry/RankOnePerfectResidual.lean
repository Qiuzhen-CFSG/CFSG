module
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.RankOneResidual
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Pairs
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The two-perfect residual of an escaping binary rank-one parabolic

A cover of a Sylow subgroup of GL₅(2) deletes one flag cut. Its diagonal
quotient has one two-dimensional block and only trivial binary blocks,
so its intrinsic two-core quotient is S₃. This calculation survives any
surjection with two-group kernel. The actual residual Y = O²(P) is
normalized by the prescribed Sylow S and satisfies YS = P; thus it still
escapes any Sylow overgroup escaped by P.

Source: Aschbacher--Smith, 15.2.23(a), printed p.1117. The original subgroup
application is in TerminalLinear.RepeatedNatural.MinimalParabolic.
-/

public noncomputable section
open Subgroup
namespace BinaryLinear.FiveFlagGeometry
open OuterCyclic SylowOvergroups SmallParabolicLevi SmallParabolicLevi.TwoNodes
private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective

private def singleLabel (i : Fin 4) : Fin 5 → Fin 5 := cutLabel ({i} : Set (Fin 4))ᶜ

private theorem singleLabel_eq (i : Fin 4) :
    singleLabel i = ![![0,0,1,2,3], ![0,1,1,2,3], ![0,1,2,2,3], ![0,1,2,3,3]] i := by
  fin_cases i <;> funext t <;> fin_cases t <;>
    simp [singleLabel, cutLabel,
      show (Finset.univ : Finset (Fin 4)) = {0,1,2,3} from by decide,
      Finset.filter_insert, Finset.filter_singleton]

private theorem singleBlock_card (i : Fin 4) :
    Fintype.card (Block (singleLabel i) i.castSucc) = 2 := by
  classical
  simp only [Block, Fintype.card_subtype]
  fin_cases i <;> simp [singleLabel_eq,
    show (Finset.univ : Finset (Fin 5)) = {0,1,2,3,4} from by decide,
    Finset.filter_insert, Finset.filter_singleton]

private theorem single_otherBlock_card (i : Fin 4) (k : Fin 5) (hk : k ≠ i.castSucc) :
    Fintype.card (Block (singleLabel i) k) ≤ 1 := by
  classical
  simp only [Block, Fintype.card_subtype]
  fin_cases i <;> fin_cases k <;> simp_all [singleLabel_eq,
    show (Finset.univ : Finset (Fin 5)) = {0,1,2,3,4} from by decide,
    Finset.filter_insert, Finset.filter_singleton]

private def singleCoordinates (i : Fin 4) :
    BlockSpace (singleLabel i) i.castSucc ≃ₗ[ZMod 2] Space 2 :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
    ((Fintype.equivFin (Block (singleLabel i) i.castSucc)).trans
      (finCongr (singleBlock_card i))).symm

private def singleProjection (i : Fin 4) :
    (∀ k : Fin 5, BinaryLinear.GL (BlockSpace (singleLabel i) k)) →*
      BinaryLinear.GL (BlockSpace (singleLabel i) i.castSucc) :=
  Pi.evalMonoidHom _ i.castSucc

private theorem singleProjection_bijective (i : Fin 4) :
    Function.Bijective (singleProjection i) := by
  constructor
  · intro a b he
    funext k
    by_cases hk : k = i.castSucc
    · subst k; exact he
    exact (linearBlock_eq_one_of_card_le_one _ _ (single_otherBlock_card i k hk) (a k)).trans
      (linearBlock_eq_one_of_card_le_one _ _ (single_otherBlock_card i k hk) (b k)).symm
  · intro a
    exact ⟨Function.update 1 i.castSucc a, by simp [singleProjection]⟩

/-- The actual rank-one flag quotient is the action of its unique two-dimensional block. -/
def rankOneQuotientEquiv (b : FiveBasis) (i : Fin 4) :
    (flagStabilizer b ({i} : Set (Fin 4))ᶜ ⧸
      pCore 2 (flagStabilizer b ({i} : Set (Fin 4))ᶜ)) ≃* Equiv.Perm (Fin 3) :=
  (flagDiagonalQuotientEquiv b _).trans
    ((MulEquiv.ofBijective (singleProjection i) (singleProjection_bijective i)).trans
      ((linearGroupCongr (singleCoordinates i)).trans linearTwoEquivSymmetricThree))

/-- Every cover of a prescribed Sylow has the literal S₃ two-core quotient. -/
theorem rankOne_quotient (S : Sylow 2 (LinearGroup 5))
    (P : Subgroup (LinearGroup 5)) (hP : (S : Subgroup _) ⋖ P) :
    Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨b,hb⟩ := sylow_eq_flagStabilizer S
  obtain ⟨i,rfl⟩ := (fullFlag_covBy_iff b P).mp (hb ▸ hP)
  exact ⟨rankOneQuotientEquiv b i⟩

/-- A two-group kernel preserves the quotient of each actual Sylow cover. -/
theorem rankOne_quotient_of_two_kernel {H : Type*} [Group H] [Finite H]
    (f : H →* LinearGroup 5) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (S : Sylow 2 H) (P : Subgroup H) (hP : (S : Subgroup H) ⋖ P) :
    Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) := by
  have hker := hk.le_sylow_of_normal S
  have hcov : (S : Subgroup H).map f ⋖ P.map f := by
    apply (comap_covBy_iff_of_surjective f hf _ _).mp
    rw [comap_map_eq_self hker,comap_map_eq_self (hker.trans hP.le)]
    exact hP
  obtain ⟨e⟩ := rankOne_quotient (S.mapSurjective hf) (P.map f) hcov
  have hkP : IsPGroup 2 (f.subgroupMap P).ker := by
    rw [Subgroup.ker_subgroupMap]
    exact hk.comap_subtype
  exact ⟨((f.subgroupMap P).pCoreQuotientEquiv (f.subgroupMap_surjective P) hkP).trans e⟩

/-- The escaping rank-one parabolic supplies its actual two-perfect residual.
Its join with the prescribed Sylow is exactly the chosen parabolic. -/
theorem exists_rankOne_residual_escaping_of_two_kernel
    {H : Type*} [Group H] [Finite H]
    (f : H →* LinearGroup 5) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (S : Sylow 2 H) (C D : Subgroup H)
    (hSC : (S : Subgroup H) ≤ C) (hSD : (S : Subgroup H) ≤ D) (hCD : ¬ C ≤ D) :
    ∃ P : Subgroup H, (S : Subgroup H) ⋖ P ∧ P ≤ C ∧
      let Y := (pResidual 2 P).map P.subtype
      IsPPerfect 2 Y ∧ Y ≤ C ∧ (S : Subgroup H) ≤ normalizer (Y : Set H) ∧
        Y ⊔ (S : Subgroup H) = P ∧ ¬ Y ≤ D ∧
        Nonempty (((Y ⊔ (S : Subgroup H) : Subgroup H) ⧸
          pCore 2 (Y ⊔ (S : Subgroup H) : Subgroup H)) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨P,hP,hPC,hPD⟩ := exists_rankOne_escaping_of_two_kernel f hf hk S C D hSC hSD hCD
  let Y := (pResidual 2 P).map P.subtype
  have hp : IsPPerfect 2 Y := (isPPerfect_pResidual 2).of_surjective
    ((pResidual 2 P).equivMapOfInjective P.subtype P.subtype_injective).toMonoidHom
    ((pResidual 2 P).equivMapOfInjective P.subtype P.subtype_injective).surjective
  have hn : (S : Subgroup H) ≤ normalizer (Y : Set H) :=
    hP.le.trans (P.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image P (pResidual 2 P)))
  have hs : Y ⊔ (S : Subgroup H) = P := by
    have he := congrArg (Subgroup.map P.subtype)
      (pResidual_sup_sylow_eq_top (S.subtype hP.le))
    simpa only [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hP.le,
      ← MonoidHom.range_eq_map, range_subtype] using he
  refine ⟨P,hP,hPC,hp,(map_subtype_le _).trans hPC,hn,hs,?_,?_⟩
  · exact fun hY => hPD (hs ▸ sup_le hY hSD)
  · rw [hs]
    exact rankOne_quotient_of_two_kernel f hf hk S P hP

end BinaryLinear.FiveFlagGeometry
