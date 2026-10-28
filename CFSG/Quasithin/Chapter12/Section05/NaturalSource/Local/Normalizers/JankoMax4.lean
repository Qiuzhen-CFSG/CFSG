module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoSpan
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.PointParabolic.Residual

/-!
# The native max4 branch of the original J₄ point parabolic

Suppose the image of the original point-component parabolic is contained
in the specified max4 subgroup. Its original full Sylow and relative index
63 then identify it with a point-stabilizer preimage under the actual
five-letter/linear projection. The same map sends the original perfect
point residual L₁* onto exactly the SL₃(2) factor. Its non-two-group
property is proved through the full original point-core quotient kernel.

The supplied equivalence `e` is retained throughout; in the source application
it is `(pointComponentCoreEquivImage ...).symm.trans hm`, followed by the
specified cover conjugator. Neither result chooses a different marking.
The max1/max2 branches, comparison with max4, original Y*/Pᵢ* markings and
escaping-actor exclusion remain with qt-d-1251-local. The elementary-normalizer
cover retains its existing producer; this module does not assume that it
selects max4. Final exterior assembly remains with qt-d-1251-source.

Source: Aschbacher–Smith, 12.5.3--4, printed pp.818--819/PDF pp.835--836.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The max4 cover branch identifies the original parabolic in the literal action. -/
theorem pointComponentParabolic_janko_max4
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model) :
    (s.pointComponentParabolic K).map e.toMonoidHom ≤
      Janko4.LocalStructure.SymmetricLinear.max4Subgroup →
    ∃ j : Fin 5, (s.pointComponentParabolic K).map e.toMonoidHom =
      Janko4.LocalStructure.SymmetricLinear.pointParabolic j := by
  intro hplace
  have hY := s.Y_le_point_component_of_large_model h hK hN
    (.inr (.inr ⟨(s.pointComponentCoreEquivImage hK.1 hN).trans e⟩))
  obtain ⟨S, hS, hi⟩ := s.pointComponentParabolic_sylow_index hK.1 hN hLK hY
  exact Janko4.LocalStructure.SymmetricLinear.parabolic_eq_point_of_equiv e S
    (s.pointComponentParabolic K) hS hplace hi


private theorem pointCoreImage_point_residual_not_two :
    ¬ IsPGroup 2 (s.pointCoreImage (s.marking.Li 1)) := by
  intro hp
  let B := s.pointCoreImage (s.marking.Li 1)
  let f := s.pointCoreImageHom (s.marking.Li 1) (s.marking.Li_le_Gi 1)
  let ebq : (B ⧸ pCore 2 B) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (f.pCoreQuotientEquiv (s.pointCoreImageHom_surjective _ _)
      (s.pointCoreImageHom_ker_isPGroup _ _)).symm.trans (s.marking.LiCoreEquiv 1 (.inl rfl))
  have ht := (hp.of_surjective (QuotientGroup.mk' (pCore 2 B))
    (QuotientGroup.mk'_surjective _)).of_equiv ebq
  obtain ⟨n, hn⟩ := ht.exists_card_eq
  rw [Atlas.Comparisons.Exceptional.sl3Two_card] at hn
  have hd : 3 ∣ 2 ^ n := hn ▸ (by decide : 3 ∣ 168)
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

/-- The original point residual has the entire linear-factor image under the
same native projection as the original parabolic. -/
theorem point_residual_janko_max4_marking
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model) :
    let H := (s.pointComponentParabolic K).map e.toMonoidHom
    let B := ((s.pointCoreImage (s.marking.Li 1)).subgroupOf
      (s.pointCoreImage K)).map e.toMonoidHom
    H ≤ Janko4.LocalStructure.SymmetricLinear.max4Subgroup →
    ∃ j : Fin 5, H = Janko4.LocalStructure.SymmetricLinear.pointParabolic j ∧
      (B.subgroupOf Janko4.LocalStructure.SymmetricLinear.max4Subgroup).map
        Janko4.LocalStructure.SymmetricLinear.max4Projection =
      (⊥ : Subgroup (Equiv.Perm (Fin 5))).prod ⊤ := by
  dsimp only
  intro hplace
  let C := s.pointCoreImage K
  let B0 := s.pointCoreImage (s.marking.Li 1)
  let B1 := B0.subgroupOf C
  let B := B1.map e.toMonoidHom
  let M := Janko4.LocalStructure.SymmetricLinear.max4Subgroup
  have hBC : B0 ≤ C := s.pointCoreImage_mono hLK
  have hBP : B1 ≤ s.pointComponentParabolic K :=
    comap_mono (s.pointCoreImage_mono (s.Li_le_Mi 1))
  have hBM : B ≤ M := (map_mono hBP).trans hplace
  let f := s.pointCoreImageHom (s.marking.Li 1) (s.marking.Li_le_Gi 1)
  let : Group.IsPerfect (s.marking.Li 1) := s.marking.Li_perfect 1
  let : Group.IsPerfect B0 := Group.IsPerfect.ofSurjective
    (f := f) (s.pointCoreImageHom_surjective _ _)
  let : Group.IsPerfect B1 := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hBC).symm.toMonoidHom) (subgroupOfEquivOfLe hBC).symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.map _
  let : Group.IsPerfect (B.subgroupOf M) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hBM).symm.toMonoidHom) (subgroupOfEquivOfLe hBM).symm.surjective
  have hnt : ¬ IsPGroup 2 (B.subgroupOf M) := by
    intro hp
    apply s.pointCoreImage_point_residual_not_two
    have hpB : IsPGroup 2 B := hp.of_equiv (subgroupOfEquivOfLe hBM)
    have hpB1 : IsPGroup 2 B1 := hpB.of_equiv (e.subgroupMap B1).symm
    exact hpB1.of_equiv (subgroupOfEquivOfLe hBC)
  obtain ⟨j, hj⟩ := s.pointComponentParabolic_janko_max4 h hK hLK hN e hplace
  refine ⟨j, hj, ?_⟩
  apply Janko4.LocalStructure.SymmetricLinear.perfect_native_marking j (B.subgroupOf M) hnt
  have hBpoint : B ≤ Janko4.LocalStructure.SymmetricLinear.pointParabolic j :=
    (map_mono hBP).trans_eq hj
  intro x hx
  have hh := hBpoint hx
  obtain ⟨y, hy, he⟩ := hh
  have heq : y = x := Subtype.ext he
  exact heq ▸ hy

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
