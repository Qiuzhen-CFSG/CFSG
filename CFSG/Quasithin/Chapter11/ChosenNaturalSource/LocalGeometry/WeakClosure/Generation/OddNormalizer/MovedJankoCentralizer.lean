module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedLocalGeometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.JankoPlacements
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Placement

/-!
# Odd centralizer of the actual moved J₄ residual

An involution centralizing the projected residual has a centralizer that
normalizes the residual, by its proved two-local normalizer control. In the
first native J₄ involution centralizer, every nonzero normal perfect subgroup
has order divisible by eleven, impossible for a full SL₃(4) quotient through
a two-core. The second involution centralizer has three-part only nine.
The two-class coverage therefore excludes every such involution.

The application uses the actual residual image under K → K/Z(K) and retains
the original module and full covering quotient. It excludes the even-centralizer
placement, not all weak cover images in J₄. The remaining moved J₄ local
inspection and its Source/Hall applications stay with this task.
Source: Aschbacher--Smith 4.4.6--12, pp.620--622; GLS3 Table5.3i.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- Local normalizer control, in addition to the full cover, excludes an even
centralizer. No universal exclusion of the weaker cover-image predicate is used. -/
theorem janko_cover_centralizer_odd
    (F : BinaryField) (hF : F.degree = 2) (X : Subgroup Janko4.Model)
    [Group.IsPerfect X] (e : (X ⧸ pCore 2 X) ≃* SL(3,F.Carrier))
    (hlocal : ∀ B : Subgroup Janko4.Model, IsPGroup 2 B → B ≠ ⊥ →
      X ≤ normalizer (B : Set Janko4.Model) →
      normalizer (B : Set Janko4.Model) ≤ normalizer (X : Set Janko4.Model)) :
    Odd (Nat.card (centralizer (X : Set Janko4.Model))) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
  have hz2 : orderOf (z : Janko4.Model) = 2 := (Subgroup.orderOf_coe z).trans hz
  let B := zpowers (z : Janko4.Model)
  have hB : IsPGroup 2 B := IsPGroup.of_card (n := 1) (by
    simpa only [B,Nat.card_zpowers,pow_one] using hz2)
  have hne : B ≠ ⊥ := by
    intro h
    have hz1 : (z : Janko4.Model) = 1 := mem_bot.mp (h ▸ mem_zpowers _)
    rw [hz1,orderOf_one] at hz2
    omega
  have hBX : B ≤ centralizer (X : Set Janko4.Model) := zpowers_le.mpr z.property
  have hXB : X ≤ normalizer (B : Set Janko4.Model) :=
    (le_centralizer_iff.mp hBX).trans (Subgroup.centralizer_le_normalizer _)
  let C := centralizer ({(z : Janko4.Model)} : Set Janko4.Model)
  have hXC : X ≤ C := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (z.property x hx)
  have hCN : C ≤ normalizer (X : Set Janko4.Model) := by
    apply le_trans ?_ (hlocal B hB hne hXB)
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro c hc b hb
    have hzC : (z : Janko4.Model) ∈ centralizer ({c} : Set Janko4.Model) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hc).symm
    exact mem_centralizer_singleton_iff.mp ((zpowers_le.mpr hzC) hb)
  let Y := X.subgroupOf C
  let a : Y ≃* X := subgroupOfEquivOfLe hXC
  let : Y.Normal := normal_subgroupOf_of_le_normalizer hCN
  let : Group.IsPerfect Y := Group.IsPerfect.ofSurjective
    (f := a.symm.toMonoidHom) a.symm.surjective
  rcases Janko4.InvolutionCentralizers.centralizer_equiv_first_or_second z hz2 with h | h
  · obtain ⟨t⟩ := h
    let Z := Y.map t.toMonoidHom
    let b : Z ≃* X := (t.subgroupMap Y).symm.trans a
    let : Z.Normal := (inferInstance : Y.Normal).map t.toMonoidHom t.surjective
    let : Group.IsPerfect Z := Group.IsPerfect.map t.toMonoidHom
    let q := b.toMonoidHom.quotientPCoreEquivOfSurjective b.surjective
      (by rw [b.toMonoidHom.ker_eq_bot b.injective]; exact IsPGroup.of_subsingleton 2 _)
    exact Normalizers.FixedSummand.Centralizer.janko_first_centralizer_no_normal_full_linear_three
      F hF Z (q.trans e)
  · obtain ⟨t⟩ := h
    have hd : 27 ∣ Nat.card X := by
      have hq : 27 ∣ Nat.card (X ⧸ pCore 2 X) := by
        rw [Nat.card_congr e.toEquiv,linear_three_order,F.card_eq,hF]
        decide
      exact hq.trans (card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 X))
        (QuotientGroup.mk'_surjective _))
    have hc := hd.trans (card_dvd_of_le hXC)
    rw [Nat.card_congr t.toEquiv,Janko4.InvolutionCentralizers.Second.ambient_card] at hc
    norm_num at hc

open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
/-- The original moved residual has odd centralizer in its actual J₄ quotient. -/
theorem moved_janko_residual_centralizer_odd
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (hf : S.field.degree = 2) (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (ek : (K ⧸ center K) ≃* Janko4.Model) :
    Odd (Nat.card (centralizer
      ((movedComponentSubgroup A (oddActorResidual L A) K).map
        (QuotientGroup.mk' (center K)) : Set (K ⧸ center K)))) := by
  let X := (movedComponentSubgroup A (oddActorResidual L A) K).map
    (QuotientGroup.mk' (center K))
  obtain ⟨hperfect,⟨a⟩⟩ := moved_projected_cover D S hA hodd K hFK
  let : Group.IsPerfect X := hperfect
  let Y := X.map ek.toMonoidHom
  let : Group.IsPerfect Y := Group.IsPerfect.map ek.toMonoidHom
  let t := ek.subgroupMap X
  let q := t.toMonoidHom.quotientPCoreEquivOfSurjective t.surjective
    (by rw [t.toMonoidHom.ker_eq_bot t.injective]; exact IsPGroup.of_subsingleton 2 _)
  have ei : ek.symm.toMonoidHom.comp ek.toMonoidHom = MonoidHom.id _ := by
    ext x
    exact ek.symm_apply_apply x
  have ei' : ek.toMonoidHom.comp ek.symm.toMonoidHom = MonoidHom.id _ := by
    ext x
    exact ek.apply_symm_apply x
  have hlocal : ∀ B : Subgroup Janko4.Model, IsPGroup 2 B → B ≠ ⊥ →
      Y ≤ normalizer (B : Set Janko4.Model) →
      normalizer (B : Set Janko4.Model) ≤ normalizer (Y : Set Janko4.Model) := by
    intro B hB hne hYB
    let B' := B.map ek.symm.toMonoidHom
    have hX : X ≤ normalizer (B' : Set (K ⧸ center K)) := by
      have hh := map_mono (f := ek.symm.toMonoidHom) hYB
      rw [map_equiv_normalizer_eq] at hh
      simpa only [Y,map_map,ei,Subgroup.map_id] using hh
    have hh := moved_projected_two_normalizer hu K hFK B' (hB.map ek.symm.toMonoidHom)
      (fun hz => hne ((map_eq_bot_iff_of_injective B ek.symm.injective).mp hz)) hX
    have hm := map_mono (f := ek.toMonoidHom) hh
    rw [map_equiv_normalizer_eq,map_equiv_normalizer_eq] at hm
    change normalizer (B'.map ek.toMonoidHom : Set Janko4.Model) ≤
      normalizer (Y : Set Janko4.Model) at hm
    simpa only [B',map_map,ei',Subgroup.map_id] using hm
  have ho := janko_cover_centralizer_odd S.field hf Y (q.symm.trans (a.trans e)) hlocal
  have hc : (centralizer (X : Set (K ⧸ center K))).map ek.toMonoidHom =
      centralizer (Y : Set Janko4.Model) := by
    simpa only [Y,coe_map,MulEquiv.coe_toMonoidHom] using map_centralizer_equiv (X : Set (K ⧸ center K)) ek
  rw [←hc,card_map_of_injective ek.injective] at ho
  exact ho

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
