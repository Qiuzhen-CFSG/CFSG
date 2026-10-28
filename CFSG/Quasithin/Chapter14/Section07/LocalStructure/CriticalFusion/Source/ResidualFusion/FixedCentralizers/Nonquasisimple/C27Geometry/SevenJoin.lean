module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.SevenOffenders

/-!
# The full fixed Sylow lies in the original component–radical join

The radical image has order two and its generator lies outside the A₇
component, so their intersection is trivial. The actual star stabilizer
contains both a full component Sylow and the perfect A₅ residual; its
order is divisible by 120. The original H → S₅ map on Lᵤ ∩ H therefore
surjects: its kernel maps trivially into the star stabilizer, and S₅ has
order 120. Lifting through this same map puts all of C_T(u) in LᵤRᵤ.

This permits C.1.24 to use the original star action, without extending
that representation to another overgroup. SevenSelection applies the
literal Sylow placement to reconstruct shortness of Lᵤ.
Source: Aschbacher–Smith C.2.7 and14.7.68(2), pp.145–147,1071–1072.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter1.RadicalExclusions.ModelReduction
open FullSieve FullSieve.SourceInterface Nonquasisimple
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem fixedComponent_C27_radical_inf_component (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) :
    starImage Lu (d.fixedCore u) (d.fixedCore u) ⊓ starImage Lu (d.fixedCore u) Lu = ⊥ := by
  obtain ⟨geo⟩ := d.fixedComponent_C27_seven_geometry u h
  let R := starImage Lu (d.fixedCore u) (d.fixedCore u)
  let A := starImage Lu (d.fixedCore u) Lu
  by_contra hn
  have hc : Nat.card (R ⊓ A : Subgroup _) = 2 := by
    have hd := card_dvd_of_le (show R ⊓ A ≤ R from inf_le_left)
    rw [geo.radical_card] at hd
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
      (fun hh => hn ((eq_bot_iff_card _).mpr hh))
  have he : R ⊓ A = R := eq_of_le_of_card_ge inf_le_left (by rw [hc,geo.radical_card])
  apply geo.generator_not_mem_component
  apply (show R ≤ A from he ▸ inf_le_right)
  rw [show R = closure {geo.generator} from geo.radical]
  exact subset_closure (Set.mem_singleton _)

theorem oneTwenty_dvd_fixedStarM_card (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) :
    120 ∣ Nat.card (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)) := by
  let A := starImage Lu (d.fixedCore u) Lu
  let M := starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)
  obtain ⟨e⟩ := d.fixedComponent_C27_star_alternatingSeven u h
  have hA : Nat.card A = 2520 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  obtain ⟨S,hS⟩ := d.fixedStarM_contains_sylow u h
  have h8 : 8 ∣ Nat.card M := by
    have hs : 8 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 3) (by rw [hA]; decide)
    have hd := hs.trans (card_dvd_of_le hS)
    rwa [Nat.card_congr (subgroupOfEquivOfLe (starM_le Lu (d.fixedCore u) _)).toEquiv] at hd
  have h60 : 60 ∣ Nat.card M := by
    obtain ⟨B,hB,hp,⟨b⟩,_⟩ := d.fixedStarM_hasA5TwoResidual_of_source u h
    have hc : Nat.card (B ⧸ pCore 2 B) = 60 := by
      rw [Nat.card_congr b.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      decide
    exact hc ▸ ((card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 B))
      (QuotientGroup.mk'_surjective _)).trans B.card_subgroup_dvd_card)
  exact (show Nat.lcm 8 60 = 120 by decide) ▸ Nat.lcm_dvd h8 h60

theorem fixedComponent_inter_H_qH_surjective (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) :
    Function.Surjective (d.qH.comp (inclusion (show Lu ⊓ F.H ≤ F.H from inf_le_right))) := by
  let N := Lu ⊓ F.H
  let J := Lu ⊔ d.fixedCore u
  let M := starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)
  let q := d.qH.comp (inclusion (show N ≤ F.H from inf_le_right))
  let f : N →* M := {
    toFun x := ⟨QuotientGroup.mk' (starKernel Lu (d.fixedCore u))
      ⟨x,mem_sup_left x.property.1⟩,
      mem_map_of_mem _ (show (x : G) ∈ (F.H ⊓ d.fixedCentralizer u) ⊓ Lu from
        ⟨⟨x.property.2,h.le_centralizer x.property.1⟩,x.property.1⟩)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨y,hy,he⟩ := x.property
    exact ⟨⟨y,hy.2,hy.1.1⟩,Subtype.ext he⟩
  have hk : q.ker ≤ f.ker := by
    intro x hx
    have hxQ : (x : G) ∈ F.H.pCoreIn 2 := by
      have hh : inclusion (show N ≤ F.H from inf_le_right) x ∈ d.qH.ker := hx
      rwa [d.qH_ker] at hh
    have hxR : (x : G) ∈ d.fixedCore u := by
      rw [d.fixedCore_eq_inter u h.member h.fixed]
      exact ⟨hxQ,x.property.2,h.le_centralizer x.property.1⟩
    have hi : (f x : StarQuotient Lu (d.fixedCore u)) ∈
        starImage Lu (d.fixedCore u) (d.fixedCore u) ⊓ starImage Lu (d.fixedCore u) Lu :=
      ⟨mem_map_of_mem _ hxR,mem_map_of_mem _ x.property.1⟩
    rw [d.fixedComponent_C27_radical_inf_component u h] at hi
    exact Subtype.ext hi
  let b : q.range →* M := q.rangeRestrict.liftOfSurjective q.rangeRestrict_surjective
    ⟨f,by simpa only [MonoidHom.ker_rangeRestrict] using hk⟩
  have hb : Function.Surjective b := by
    intro m
    obtain ⟨x,rfl⟩ := hf m
    exact ⟨q.rangeRestrict x,by simp [b]⟩
  have h120 : 120 ∣ Nat.card q.range :=
    (d.oneTwenty_dvd_fixedStarM_card u h).trans (card_dvd_of_surjective b hb)
  have he : q.range = ⊤ := eq_of_le_of_card_ge le_top (by
    rw [Nat.card_congr (topEquiv : (⊤ : Subgroup ChapterJ.S5) ≃* ChapterJ.S5).toEquiv]
    change Nat.card (Equiv.Perm (Fin 5)) ≤ Nat.card q.range
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    exact Nat.le_of_dvd Nat.card_pos h120)
  exact MonoidHom.range_eq_top.mp he

theorem fixedSylow_le_component_radical_join (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) : d.fixedSylow u ≤ Lu ⊔ d.fixedCore u := by
  intro t ht
  obtain ⟨x,hx⟩ := d.fixedComponent_inter_H_qH_surjective u h (d.qH ⟨t,F.invariant 1 ht.1⟩)
  have hcore : (x : G)⁻¹*t ∈ d.fixedCore u := by
    rw [d.fixedCore_eq_inter u h.member h.fixed]
    refine ⟨?_,F.H.mul_mem (F.H.inv_mem x.property.2) (F.invariant 1 ht.1),
      (d.fixedCentralizer u).mul_mem ((d.fixedCentralizer u).inv_mem
        (h.le_centralizer x.property.1)) ht.2⟩
    have he : (⟨(x : G)⁻¹*t,F.H.mul_mem (F.H.inv_mem x.property.2)
        (F.invariant 1 ht.1)⟩ : F.H) ∈ d.qH.ker := by
      change d.qH ((inclusion inf_le_right x)⁻¹ * ⟨t,F.invariant 1 ht.1⟩) = 1
      rw [map_mul,map_inv,show d.qH (inclusion inf_le_right x) = _ from hx,inv_mul_cancel]
    rwa [d.qH_ker] at he
  have hm := (Lu ⊔ d.fixedCore u).mul_mem (mem_sup_left x.property.1) (mem_sup_right hcore)
  simpa only [mul_inv_cancel_left] using hm


end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
