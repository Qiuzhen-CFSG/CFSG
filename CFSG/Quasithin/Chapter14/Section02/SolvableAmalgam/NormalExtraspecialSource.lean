module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.NormalClosureCenter
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.GroupTheory.CommutatorPreimageFrattini

/-!
# Extraspecial closure in the original normal Bender row

The actual opposite parabolic removes the possible central radical. The
Frattini subgroup is the original central involution, so the closure is
extraspecial of order 32 or 512. This packages the local input used by the
normal-row recognition step without an extra core or classification premise.

Source: Aschbacher–Smith 14.2.16 and F.1.12, printed pp.985–986.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.LocalBinary
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open Chapter12.Section08
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
theorem source_normal_bender_closure_extraspecial
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hnH : 1 < generationParameter H)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) H))
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    (f : ℕ) (hm : BenderModel ((H ⊓ M).subgroupOf H) K f) :
    let U := conjugateSpanBy (localModule T M) H
    IsExtraspecial 2 U ∧ (center U).map U.subtype = centralInvolutions T ∧
      ((f = 2 ∧ Nat.card U = 32) ∨ (f = 3 ∧ Nat.card U = 512)) := by
  let D : ChapterG.Section02.Setup G :=
    { V := localModule T M, V₁ := centralInvolutions T, L := sourceResidual M Mc,
      T := T, H := H }
  obtain ⟨h,hphi,hphic,_⟩ := source_frattini_seed_orbit
    hG T hempty hM hu hmany hcard e H hH.1 hne
  obtain ⟨hc,ho⟩ := source_normal_bender_closure_extraspecial_orders
    hG T hempty hM hu hmany hcard e H hH hnH hne K hK hqK hgen f hm
  have hpc : frattini D.U ≤ center D.U :=
    central_of_normal_card_two _ hphic
  have heq : frattini D.U = center D.U :=
    eq_of_le_of_card_ge hpc (by rw [hphic];exact hc.le)
  have hx : IsExtraspecial 2 D.U := {
    center_order_p := hc
    quotient_elementary_abelian :=
      elementary_quotient_of_frattini_le h.U_isPGroup _ hpc
    quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr (by
      intro ht
      exact hne (center_eq_top_iff.mp ht)) }
  refine ⟨hx,?_,ho⟩
  change (center D.U).map D.U.subtype = D.V₁
  rw [←heq,hphi]
end CFSG.Quasithin.Chapter14.Section02.LocalBinary
