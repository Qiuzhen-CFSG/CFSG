module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.ComponentDiagram
public import Theory.SpecificGroups.BinaryLinear.SylowNormalizerCover

/-!
# The original component diagram exchange is outer

The proved source diagram action exchanges the two actual parabolics over
the quotient Sylow. An inner automorphism preserving that Sylow comes from
the Sylow itself, since the binary linear Sylow is self-normalizing, and
therefore preserves both parabolics. This contradiction constructs an outer
actor in the original component normalizer, through the same chosen quotient
isomorphism used by the support sections.

The source component model is retained; original 14.6.18 remains explicit
for qt-e-14625-source. SourceSections applies this theorem to both actual
components in the 14.6.24 exclusion.

Source: Aschbacher--Smith 14.6.20 and 14.6.24(3), pp.1037,1039--1041.
-/

public section
open Subgroup Theory.GroupTheory Subgroup.NormalSylowQuotientAction
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ComponentSupports.Classification.Sieve
variable {G : Type*} [Group G] [Finite G]

/-- An original diagram exchanger acts outerly on the prescribed component quotient. -/
theorem source_component_outer_actor
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL) :
    ∃ s : (Mc ⊓ normalizer (K : Set G) : Subgroup G),
      markedCoreAction 2 K eK ⟨s,s.property.2⟩ ∉ MulAut.innerSubgroup Matrix.PSL3Two.SL := by
  let b := eK.trans Matrix.PSL3Two.equiv
  obtain ⟨P,hP,J,L,_,_,hne,hJL,_,s,hs,_⟩ := source_l3_component_parabolic_swap
    hG T hempty hM hunique hmany hcard e hab hsolv Mc
    (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK b
  have hTH := (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e).1.2
  refine ⟨⟨s,hTH s.property.1,s.property.2⟩,?_⟩
  rintro ⟨g,hg⟩
  let a := markedCoreAction 2 K b ⟨s,s.property.2⟩
  have ha : a = MulAut.conj (Matrix.PSL3Two.equiv g) := by
    ext x
    obtain ⟨y,rfl⟩ := b.surjective x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) y
    change markedCoreAction 2 K b ⟨s,s.property.2⟩ (b (QuotientGroup.mk' _ y)) = _
    rw [markedCoreAction_mk]
    have hh := congrArg (fun a : MulAut Matrix.PSL3Two.SL => a (eK (QuotientGroup.mk' _ y))) hg
    rw [markedCoreAction_mk] at hh
    change g * eK (QuotientGroup.mk' _ y) * g⁻¹ = _ at hh
    change Matrix.PSL3Two.equiv (eK (QuotientGroup.mk' _ (K.normalizerMonoidHom _ y))) = _
    rw [←hh]
    simp only [map_mul,map_inv,MulAut.conj_apply]
    rfl
  let q := b.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := b.surjective.comp (QuotientGroup.mk'_surjective _)
  let Pq := P.mapSurjective hq
  have hpres : (Pq : Subgroup Matrix.PSL3Two.PSL).map a.toMonoidHom = Pq :=
    markedCoreAction_preserves_component_sylow 2 T K b P hP s
  rw [ha] at hpres
  have hgN : Matrix.PSL3Two.equiv g ∈ normalizer (Pq : Set Matrix.PSL3Two.PSL) :=
    mem_normalizer_iff_map_conj_eq.mpr hpres
  let E := Matrix.PSL3Two.equiv.symm.trans (BinaryLinear.OuterCyclic.slEquivLinear 3)
  have hker : IsPGroup 2 E.toMonoidHom.ker := by
    rw [MonoidHom.ker_eq_bot E.toMonoidHom E.injective]
    exact IsPGroup.of_bot
  have hnorm := BinaryLinear.SylowNormalizerCover.normalizer_sylow_eq_of_two_kernel
    E.toMonoidHom E.surjective hker Pq
  rw [hnorm] at hgN
  have hgJ : Matrix.PSL3Two.equiv g ∈ J := (show (Pq : Subgroup Matrix.PSL3Two.PSL) ≤ J from by
    change (P : Subgroup K).map q ≤ J
    rw [←hJL]
    exact inf_le_left) hgN
  have hfix : J.map (MulAut.conj (Matrix.PSL3Two.equiv g)).toMonoidHom = J :=
    mem_normalizer_iff_map_conj_eq.mp (J.le_normalizer hgJ)
  change J.map a.toMonoidHom = L at hs
  rw [ha,hfix] at hs
  exact hne hs
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
