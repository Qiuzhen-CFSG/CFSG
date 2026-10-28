module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoMax2
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.PointLocalIntersection

/-!
# The original max2 projected actor

Two independent cubic matrices in the original SL5 parabolic intersection
force nine to divide its relative Sylow index. Transport through the actual
point-core quotient and intersection with the normal component preserves
that index. Together with the full component Sylow, this gives the lower
bound 2^21 * 9 on the original local intersection.

The scalar-kernel comparison preserves the cubic image of the original Y.
The native M22 solvable-normal-subgroup bound then gives the same upper
bound on the projected actor. The two subgroups are therefore equal, putting
the actor in the original point parabolic and proving G3,G6 <= N_G(L).
All maps, the full Sylow, and the original P/P_i marking are retained.
Source: Aschbacher--Smith 12.5.4, printed p.819/PDF p.836.
-/

public noncomputable section
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

theorem nine_dvd_sylow_relIndex_M₁_intersection
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    9 ∣ (T : Subgroup G).relIndex (s.marking.Mi 1 ⊓ s.marking.Mi i) := by
  let LT : Subgroup G := L ⊔ (T : Subgroup G)
  have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
  have hT : (T : Subgroup G) =
      (Representation.SL5ExteriorSquare.flagGroup.comap s.actor).map LT.subtype := by
    rw [s.actor_preimage_flag, map_subgroupOf_eq_of_le le_sup_right]
  have hM : s.marking.Mi 1 ⊓ s.marking.Mi i =
      ((Representation.SL5ExteriorSquare.parabolic 2 ⊓
        Representation.SL5ExteriorSquare.parabolic
          (localFlagDimension i)).comap s.actor).map LT.subtype := by
    rw [s.Mi_eq_actor_preimage 1 (.inl rfl), s.Mi_eq_actor_preimage i hidx,
      ←map_inf _ _ _ LT.subtype_injective, ←comap_inf]
    rfl
  rw [hT, hM, relIndex_map_map_of_injective _ _ LT.subtype_injective,
    relIndex_comap, map_comap_eq_self (by
      rw [MonoidHom.range_eq_top.mpr s.actor_surjective]
      exact le_top)]
  apply Representation.SL5ExteriorSquare.nine_dvd_flag_index_point_local_intersection
  rcases hi with rfl | rfl <;> simp [localFlagDimension]

theorem point_component_local_intersection_nine
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (i : ℕ) (hi : i = 3 ∨ i = 6) :
    2^21 * 9 ∣ Nat.card ((s.pointCoreImage (s.marking.Mi 1 ⊓ s.marking.Mi i)).subgroupOf
      (s.pointCoreImage K)) := by
  have hYK := s.Y_le_point_component_of_large_model h hK hN
    (.inr (.inr ⟨(s.pointComponentCoreEquivImage hK.1 hN).trans e⟩))
  let G₁ := s.marking.Gi 1
  let q := QuotientGroup.mk' (pCore 2 G₁)
  let C := s.pointCoreImage K
  let B := s.marking.Mi 1 ⊓ s.marking.Mi i
  let E := s.pointCoreImage B
  let I := E.subgroupOf C
  let R := (T.subtype s.sylow_le_G₁).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G₁))
  have hidx : LocalIndex i := by rcases hi with rfl | rfl <;> simp [LocalIndex]
  have hTB : (T : Subgroup G) ≤ B := le_inf
    (le_inf le_sup_right s.sylow_le_G₁) (le_inf le_sup_right (s.sylow_le_Gi i hidx))
  have hBG : B ≤ G₁ := inf_le_left.trans inf_le_right
  have hRE : (R : Subgroup _) ≤ E := s.pointCoreImage_mono hTB
  have hQT : pCore 2 G₁ ≤ (T : Subgroup G).subgroupOf G₁ :=
    pCore_isPGroup.le_sylow_of_normal (T.subtype s.sylow_le_G₁)
  have hQB : pCore 2 G₁ ≤ B.subgroupOf G₁ := hQT.trans (comap_mono hTB)
  let : (K.subgroupOf G₁).Normal := hN
  let : C.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hsupp : E ≤ C ⊔ (R : Subgroup _) := by
    have hM : s.marking.Mi 1 ≤ K ⊔ (T : Subgroup G) := by
      rw [s.M₁_eq_Y_sup_point_residual_sup_sylow]
      exact sup_le_sup (sup_le hYK hLK) le_rfl
    have he := s.pointCoreImage_mono ((show B ≤ s.marking.Mi 1 from inf_le_left).trans hM)
    have hsup : s.pointCoreImage (K ⊔ (T : Subgroup G)) = C ⊔ (R : Subgroup _) := by
      rw [pointCoreImage, subgroupOf_sup hK.1 s.sylow_le_G₁, Subgroup.map_sup]
      rfl
    exact he.trans_eq hsup
  obtain ⟨S,hS⟩ := R.exists_subgroupOf_eq_of_normal C
  have hSI : (S : Subgroup C) ≤ I := by
    rw [hS]
    exact comap_mono hRE
  have hrel : (S : Subgroup C).relIndex I = (T : Subgroup G).relIndex B := by
    calc
      _ = (R : Subgroup (G₁ ⧸ pCore 2 G₁)).relIndex E := by
        change (S : Subgroup C).relIndex (E.subgroupOf C) = _
        rw [hS]
        exact normal_intersection_relIndex (R : Subgroup (G₁ ⧸ pCore 2 G₁)) E C hRE hsupp
      _ = _ := by
        change ((T : Subgroup G).subgroupOf G₁ |>.map q).relIndex
          ((B.subgroupOf G₁).map q) = _
        rw [relIndex_map_map, show q.ker = pCore 2 G₁ from QuotientGroup.ker_mk' _,
          sup_eq_left.mpr hQT,
          sup_eq_left.mpr hQB, relIndex_subgroupOf hBG]
  have h9 : 9 ∣ Nat.card I :=
    (hrel.symm ▸ s.nine_dvd_sylow_relIndex_M₁_intersection i hi).trans
      ((S : Subgroup C).relIndex_dvd_card I)
  have htwo : 2^21 ∣ Nat.card I := (S.pow_dvd_card_of_pow_dvd_card (n := 21) (by
    rw [Nat.card_congr e.toEquiv, Janko4.Cardinality.model_card]
    decide)).trans (card_dvd_of_le hSI)
  exact (show Nat.Coprime (2^21) 9 by decide).mul_dvd_of_dvd_of_dvd htwo h9

theorem point_projection_le_parabolic_of_janko_max2
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (i : ℕ) (hi : i = 3 ∨ i = 6)
    (hactor : ((s.localPointProjection K i).subgroupOf (s.pointCoreImage K)).map
      e.toMonoidHom ≤ Janko4.InvolutionCentralizers.First.centralizer) :
    s.localPointProjection K i ≤ s.pointCoreImage (s.marking.Mi 1) := by
  let C := s.pointCoreImage K
  let A := (s.localPointProjection K i).subgroupOf C
  let I := (s.pointCoreImage (s.marking.Mi 1 ⊓ s.marking.Mi i)).subgroupOf C
  have hIA : I ≤ A := by
    intro x hx
    have hm : s.pointCoreImage (s.marking.Mi 1 ⊓ s.marking.Mi i) ≤
        s.pointCoreImage (s.marking.Gi i ⊓ s.marking.Gi 1) :=
      s.pointCoreImage_mono (le_inf (inf_le_right.trans inf_le_right)
        (inf_le_left.trans inf_le_right))
    exact ⟨x.property, (show s.pointCoreImage (s.marking.Gi i ⊓ s.marking.Gi 1) ≤
      s.pointCoreImage (s.marking.Gi i ⊓ s.marking.Gi 1) ⊔ centralizer (C : Set _) from
      le_sup_left) (hm hx)⟩
  have hcardA : Nat.card A ∣ 2^21 * 9 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show s.localPointProjection K i ≤ C from
      inf_le_left)).toEquiv]
    exact s.point_projection_janko_max2_card_dvd h hK hLK hN e i hi hactor
  have hcardI : 2^21 * 9 ∣ Nat.card I :=
    s.point_component_local_intersection_nine h hK hLK hN e i hi
  have he : I = A := eq_of_le_of_card_ge hIA
    ((Nat.le_of_dvd (by decide) hcardA).trans (Nat.le_of_dvd Nat.card_pos hcardI))
  intro x hx
  have hI : (⟨x,hx.1⟩ : C) ∈ I := he.symm ▸ (show (⟨x,hx.1⟩ : C) ∈ A from hx)
  exact s.pointCoreImage_mono inf_le_left hI

theorem local_normalizer_le_M_of_janko_max2
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (i : ℕ) (hi : i = 3 ∨ i = 6)
    (hactor : ((s.localPointProjection K i).subgroupOf (s.pointCoreImage K)).map
      e.toMonoidHom ≤ Janko4.InvolutionCentralizers.First.centralizer) :
    s.marking.Gi i ≤ s.marking.M := by
  apply (s.local_normalizer_iff_large_point_projection h hK hLK hN
    (.inr (.inr ⟨(s.pointComponentCoreEquivImage hK.1 hN).trans e⟩)) i hi).mpr
  exact (s.point_projection_le_parabolic_of_janko_max2 h hK hLK hN e i hi hactor).trans
    ((s.pointCoreImage_normalizes_point_iff (s.marking.Mi 1) inf_le_right).mpr
      (s.Mi_normalizes_Li 1))

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
