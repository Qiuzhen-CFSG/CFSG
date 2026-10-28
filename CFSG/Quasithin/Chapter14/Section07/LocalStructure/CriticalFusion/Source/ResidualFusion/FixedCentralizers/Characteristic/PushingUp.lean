module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Characteristic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.PushingUp.Source
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport

/-!
# The C.1.26 deduction on the fixed-element join

Apply the full earlier pushing-up implication to the literal group K C_T(u).
Its characteristic alternatives transport to subgroups characteristic in the
original C_T(u), with normality relative to that same join. In its third
alternative the commuting factors generate the actual two-residual K. A
C-component cannot be a central product of proper normal subgroups: each
would be solvable, making K solvable. Hence K is one of the blocks, contrary
to the source commutator obstruction proved in Characteristic.

Minimal parabolicity is still an explicit local premise; its proof belongs to
the five-point quotient bridge. The earlier identities are 14.7.48(2) and
14.5.21(2), owned by qt-14-07-components and qt-14-05-terminal-duality. The
full C.1.26 implication and distinguished characteristic choices remain with
qt-c-01. This is a conditional deduction, not the completed 14.7.68 witness.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
C.1.26, p.132; 14.7.68(2), pp.1071–1072. We reuse the full C.1.26 contract
already published for Chapter 15; no later Chapter 15 theorem is invoked.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem cComponent_mem_commuting_factors (K : Subgroup G) (hK : K.IsCComponent)
    (factors : Set (Subgroup G)) (hgen : sSup factors = K)
    (hcomm : factors.Pairwise fun A B => ⁅A, B⁆ = ⊥) : K ∈ factors := by
  classical
  have hle (A : Subgroup G) (hA : A ∈ factors) : A ≤ K := hgen ▸ le_sSup hA
  have hn (A : Subgroup G) (hA : A ∈ factors) : (A.subgroupOf K).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer (hle A hA)).mpr
    apply hgen.ge.trans
    apply sSup_le
    intro B hB
    by_cases he : A = B
    · subst B; exact A.le_normalizer
    · exact le_normalizer_iff_commutator_le_left.mpr (by
        rw [hcomm hA hB he]; exact bot_le)
  by_contra hnot
  have hr : K ≤ (solvableRadical K).map K.subtype := by
    apply hgen.ge.trans
    apply sSup_le
    intro A hA
    have hproper : A.subgroupOf K ≠ ⊤ := by
      intro he
      have hAK := le_antisymm (hle A hA) (subgroupOf_eq_top.mp he)
      exact hnot (hAK ▸ hA)
    have hs := hK.isSolvable_of_subnormal_lt_top (hn A hA).isSubnormal hproper
    have hm := map_mono (f := K.subtype) (le_solvableRadical _ (hn A hA) hs)
    rwa [map_subgroupOf_eq_of_le (hle A hA)] at hm
  have htop : solvableRadical K = ⊤ := by
    apply top_unique
    intro x _
    exact (mem_map_iff_mem K.subtype_injective).mp (hr x.property)
  apply hK.not_isSolvable
  have ht : Group.IsSolvable (⊤ : Subgroup K) := htop ▸ inferInstance
  exact Group.isSolvable_of_surjective (f := (topEquiv : (⊤ : Subgroup K) ≃* K).toMonoidHom)
    topEquiv.surjective

variable {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem fixedCharacteristic_of_C126
    (choices : DistinguishedPairs.{u})
    (source : C126Source KnownSimple.IsKnownSimple choices)
    (hUK : ⁅F.U, K F⁆ = F.U) (hUQ : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u) (hmax : IsMaximalTwoLocal F.H)
    (hpar : ∀ P : Sylow 2 (d.fixedJoin u),
      (P : Subgroup (d.fixedJoin u)).map (d.fixedJoin u).subtype = d.fixedSylow u →
        ChapterB.IsMinimalParabolicOver P ⊤) :
    Nonempty (d.FixedCharacteristicWitness u) := by
  have hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedJoin u) :=
    (d.K_mem_fixedLocalFamily u hu hfix).2.1
  obtain ⟨P, hP⟩ := hsyl
  let : Nontrivial P := sylow_nontrivial_of_minimalParabolic P (hpar P hP)
  let C := choices.pair P P.isPGroup'
  have hAlt := source (d.fixedJoin u) (d.fixedJoin_sqtk u hu hne)
    (d.fixedJoin_fitting u hu hfix hmax) P (hpar P hP)
  change C126Alternatives P C at hAlt
  have transport (A : Subgroup P) (hA : A.Characteristic) (hneA : A ≠ ⊥)
      (hn : (A.map (P : Subgroup (d.fixedJoin u)).subtype).Normal) :
      Nonempty (d.FixedCharacteristicWitness u) := by
    let e : P ≃* d.fixedSylow u :=
      ((P : Subgroup (d.fixedJoin u)).equivMapOfInjective (d.fixedJoin u).subtype
        (d.fixedJoin u).subtype_injective).trans (MulEquiv.subgroupCongr hP)
    let A' := A.map e.toMonoidHom
    have he : (A'.map (d.fixedSylow u).subtype).subgroupOf (d.fixedJoin u) =
        A.map (P : Subgroup (d.fixedJoin u)).subtype := by
      apply map_injective (d.fixedJoin u).subtype_injective
      rw [map_subgroupOf_eq_of_le (show A'.map (d.fixedSylow u).subtype ≤ d.fixedJoin u from
        (map_subtype_le A').trans le_sup_right), map_map, map_map]
      rfl
    refine ⟨⟨A', ?_, ?_, ?_⟩⟩
    · let := hA
      apply characteristic_iff_le_comap.mpr
      intro a x hx
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨(MulAut.congr e.symm a) y,
        characteristic_iff_le_comap.mp hA (MulAut.congr e.symm a) hy, ?_⟩
      exact e.apply_symm_apply _
    · exact fun hb => hneA ((A.map_eq_bot_iff_of_injective e.injective).mp hb)
    · exact he.symm ▸ hn
  rcases hAlt with hcentral | hnormal | hblocks
  · have hn : (C.first.map (P : Subgroup (d.fixedJoin u)).subtype).Normal := by
      constructor
      intro x hx g
      rw [mem_center_iff.mp (hcentral hx) g, mul_inv_cancel_right]
      exact hx
    exact transport C.first C.first_characteristic C.first_ne_bot hn
  · let : (ChapterB.baumann (⊤ : Subgroup P)).Characteristic := ChapterB.baumann_characteristic
    exact transport _ C.second_image_characteristic C.second_image_ne_bot hnormal
  · obtain ⟨b⟩ := hblocks
    have hres : (pResidual 2 (d.fixedJoin u)).map (d.fixedJoin u).subtype = K F :=
      embedded_pResidual_join_pGroup (K F) (d.fixedSylow u) (K_twoPerfect F)
        (T.isPGroup'.to_le inf_le_left)
        (inf_le_left.trans ((F.invariant 1).trans (H_normalizes_K F)))
    have hgen : sSup b.factors = (K F).subgroupOf (d.fixedJoin u) := by
      apply map_injective (d.fixedJoin u).subtype_injective
      rw [b.generate, hres, map_subgroupOf_eq_of_le
        (show K F ≤ d.fixedJoin u from le_sup_left)]
    have hcJ : ((K F).subgroupOf (d.fixedJoin u)).IsCComponent :=
      (d.K_mem_fixedLocalFamily u hu hfix).1
    have hmem := cComponent_mem_commuting_factors _
      hcJ b.factors hgen b.commute
    have hs := (b.block _ hmem).1.short.of_mulEquiv
      (subgroupOfEquivOfLe (show K F ≤ d.fixedJoin u from le_sup_left))
    exact (d.K_not_short_of_source_commutators hUK hUQ hs).elim

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
