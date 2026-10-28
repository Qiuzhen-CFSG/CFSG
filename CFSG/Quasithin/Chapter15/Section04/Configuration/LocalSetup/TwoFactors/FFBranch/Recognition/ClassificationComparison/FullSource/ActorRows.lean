module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FullSource.RankOne
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FullSource.LargeRows

/-!
# The small offender actors from every complete source row

When the ambient generalized Fitting subgroup is quasisimple, the original
thirteen rows and corrected field extensions split into the low Sylow rows
and the degree-three or Mathieu rows. Their numerical exclusions eliminate
the remaining bounded rank-one and large actors. The resulting small actor
is on the original offender subgroup, ready for the source module exclusions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
F.6.18, pp.309–310; B.5.1/B.5.6, pp.99–110; 15.4.18, p.1163.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FullSource
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open FFAlternatives QuasisimpleComparison QuasisimpleComparison.ActorPruning
universe u v
variable {D : Type u} [Group D] [Finite D] {K : GroupClass.{u}}
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}
attribute [local instance] offenderSubgroup_normal

private theorem quasisimple_not_solvable {A : Type*} [Group A]
    (h : IsQuasisimple A) : ¬ Group.IsSolvable A := by
  let := h
  let : IsSimpleGroup (A ⧸ center A) := h.simple
  let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
  exact Group.IsPerfect.not_isSolvable A

private theorem two_solvable (hm : Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
    ∃ N : Subgroup D, ∃ _ : N.Normal, IsExtraspecial 3 N ∧ Nat.card N = 27 ∧
      Monoid.exponent N = 3 ∧ Nonempty ((D ⧸ N) ≃* FSource.E4)) : Group.IsSolvable D := by
  rcases hm with hm | ⟨N,_,hN,_,_,⟨e⟩⟩
  · obtain ⟨e⟩ := hm
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · let : Group.IsNilpotent N := hN.isPGroup.isNilpotent
    let : Group.IsSolvable (D ⧸ N) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance,inferInstance⟩

private theorem early_or_large_of_alternative (hL : IsQuasisimple (generalizedFitting D))
    {A B : Subgroup D} {S : Sylow 2 D}
    (hc : pCore 2 A ≠ ⊥ ∨ pCore 2 B ≠ ⊥) (r : FSource.Alternative A B S) :
    (Nat.card S ≤ 16 ∧ RankOneRows.EarlyAlternative S) ∨ LargeRow D := by
  have eight (hs : Nonempty (S ≃* DihedralGroup 4)) : Nat.card S ≤ 8 := by
    rw [Nat.card_congr hs.some.toEquiv,DihedralGroup.nat_card]
  have sixteen (hs : Nonempty (S ≃* (FSource.C 2 × DihedralGroup 4))) : Nat.card S ≤ 16 := by
    rw [Nat.card_congr hs.some.toEquiv,Nat.card_prod,DihedralGroup.nat_card]
    norm_num [FSource.C]
  cases r with
  | one _ ha hb _ => exact (hc.elim (· ha) (· hb)).elim
  | two hm =>
    let := two_solvable hm
    exact (quasisimple_not_solvable hL inferInstance).elim
  | three r hs _ _ =>
    exact Or.inl ⟨(eight hs).trans (by decide),Or.inl ⟨r.field,r.degree,r.congruence,
      r.first.subtype.comp r.firstEquiv.symm.toMonoidHom,
      Subtype.val_injective.comp r.firstEquiv.symm.injective,eight hs⟩⟩
  | four F hd hm e ht hq hs _ _ =>
    have h4 : Nat.card S ≤ 8 := by
      rw [Nat.card_congr hs.some.toEquiv]; norm_num [FSource.E4,FSource.C,Nat.card_prod]
    exact Or.inl ⟨h4.trans (by decide),Or.inl ⟨F,hd,hm,e.symm.toMonoidHom,e.symm.injective,h4⟩⟩
  | five F hd hm e ec hq hs _ _ =>
    exact Or.inl ⟨(eight hs).trans (by decide),Or.inl ⟨F,hd,hm,
      (generalizedFitting D).subtype.comp ec.symm.toMonoidHom,
      Subtype.val_injective.comp ec.symm.injective,eight hs⟩⟩
  | six hm ht hq hs _ _ =>
    refine Or.inl ⟨(eight hs).trans (by decide),?_⟩
    rcases hm with hm | ⟨F,hd,hm,⟨e⟩⟩
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨⟨F,hd,hm,e,ht,hq,hs⟩⟩)))))))
  | seven hm _ hs _ _ =>
    refine Or.inl ⟨(eight hs).trans (by decide),?_⟩
    rcases hm with hm | hm
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm,(eight hs).trans (by decide)⟩)))))
    · exact Or.inr (Or.inr (Or.inl hm))
  | eight hm hq hs _ _ =>
    refine Or.inl ⟨sixteen hs,?_⟩
    rcases hm with hm | hr
    · exact Or.inr (Or.inr (Or.inr (Or.inl hm)))
    · obtain ⟨r⟩ := hr
      have hr : FSource.SquareFieldExtensionRow S :=
        { r with congruence := Or.inl r.congruence,quasisimple := hq,sylow := hs }
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hr⟩)))))))
  | nine hm _ hs _ _ =>
    refine Or.inl ⟨sixteen hs,?_⟩
    rcases hm with hm | hm
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm,sixteen hs⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))
  | ten p hp hm model _ _ _ _ _ => exact Or.inr (Or.inl ⟨p,hp,hm,model⟩)
  | eleven r _ _ _ _ => exact Or.inr (Or.inr (Or.inl ⟨r⟩))
  | twelve e _ _ _ _ => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))
  | thirteen e _ _ _ _ _ => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩)))

private theorem early_or_large_of_source (hL : IsQuasisimple (generalizedFitting D))
    {A B : Subgroup D} {S : Sylow 2 D}
    (hc : pCore 2 A ≠ ⊥ ∨ pCore 2 B ≠ ⊥) (r : FSource.SourceAlternative A B S) :
    (Nat.card S ≤ 16 ∧ RankOneRows.EarlyAlternative S) ∨ LargeRow D := by
  rcases r with (hr | hr) | hr
  · exact early_or_large_of_alternative hL hc hr
  · obtain ⟨r⟩ := hr
    have hs : Nat.card S ≤ 16 := by
      rw [Nat.card_congr r.sylow.some.toEquiv,DihedralGroup.nat_card]; decide
    exact Or.inl ⟨hs,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨r⟩)))))))⟩
  · obtain ⟨r⟩ := hr
    have hs : Nat.card S ≤ 16 := by
      rw [Nat.card_congr r.sylow.some.toEquiv,Nat.card_prod,DihedralGroup.nat_card]
      norm_num [FSource.C]
    exact Or.inl ⟨hs,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨r⟩)))))))⟩

private theorem largeActor_not_small_sylow (ha : LargeActorModel (offenderSubgroup ρ))
    (S : Sylow 2 D) (hs : Nat.card S ≤ 16) : False := by
  have hd := ha.sixtyFour_dvd.trans (offenderSubgroup ρ).card_subgroup_dvd_card
  have hd' := S.pow_dvd_card_of_pow_dvd_card (show 2^6 ∣ Nat.card D from hd)
  have hl := Nat.le_of_dvd (Nat.card_pos (α := S)) hd'
  omega

theorem ClassifiedAction.smallActor_of_quasisimple_ambient
    (h : ClassifiedAction K ρ G₁ G₂) (hL : IsQuasisimple (generalizedFitting D))
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype)) :
    SmallActorModel (offenderSubgroup ρ) := by
  have step {A B : Subgroup D} (hc : pCore 2 A ≠ ⊥ ∨ pCore 2 B ≠ ⊥)
      (r : FSource.SourceAlternative A B h.sylow) :
      ¬ RankOneActorModel (offenderSubgroup ρ) ∧ ¬ LargeActorModel (offenderSubgroup ρ) := by
    rcases early_or_large_of_source hL hc r with ⟨hs,hr⟩ | hr
    · exact ⟨fun ha => RankOneRows.not_earlyAlternative h ha hr,
        fun ha => largeActor_not_small_sylow ha h.sylow hs⟩
    · exact largeRow_not_remainingActors (offenderSubgroup ρ) h.quotient_twoGroup hr
  have hn : ¬ RankOneActorModel (offenderSubgroup ρ) ∧ ¬ LargeActorModel (offenderSubgroup ρ) := by
    rcases h.goldschmidt with hr | hr
    · exact step h.core_nontrivial hr
    · exact step h.core_nontrivial.symm hr
  rcases actor_split b with ha | ha | ha
  · exact ha
  · exact (hn.1 ha).elim
  · exact (hn.2 ha).elim
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FullSource
