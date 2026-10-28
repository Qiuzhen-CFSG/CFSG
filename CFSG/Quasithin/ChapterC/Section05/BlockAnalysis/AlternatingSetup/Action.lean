module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.NaturalAction
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.PairNormalizer
public import CFSG.Quasithin.ChapterB.Section02.Baumann.ActionQuotient
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The actual action of a normalized alternating-five block

Projectivity removes the fixed kernel inside U(K), while retaining the
central extension in O₂(K). The normalizer of the resulting A₅ module
constructs the full normalizing group's permutation action. B.3.2 then
excludes strong offenders on every elementary subgroup of its action image;
no elementary lift of an image subgroup is used.

Source: Aschbacher–Smith C.1.13(c), C.5.4(3), pp.125 and155, and B.3.2.
-/

public section
open Subgroup BinaryPermutation Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
open ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive
open ConjugateSource
variable {G : Type*} [Group G] {K H : Subgroup G}

theorem exists_action (hK : IsAlternatingBlock K 5) (hKH : K ≤ H)
    (hH : H ≤ normalizer (K : Set G)) :
    ∃ (q : H →* FivePerm) (e : sourceModule K ≃* Multiplicative (core (Fin 5))),
      q.ker = (centralizer (sourceModule K : Set G)).subgroupOf H ∧
      (K.subgroupOf H).map q = alternatingGroup (Fin 5) ∧
      ∀ (s : H) (u : sourceModule K),
        (e.symm (Multiplicative.ofAdd
          (coreRepresentation (Fin 5) (q s) (e u).toAdd)) : G) =
            (s : G) * (u : G) * (s : G)⁻¹ := by
  obtain ⟨a,en,ha,he⟩ := exists_lifted_block_action hK hK.blockFixed_eq_bot
  let e : sourceModule K ≃* Multiplicative (natural (Fin 5)) := en
  have hn : H ≤ normalizer (sourceModule K : Set G) :=
    hH.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  let ρ := transportedAction hn e
  have hi : (K.subgroupOf H).map ρ =
      (alternatingGroup (Fin 5)).map (naturalMulAction (Fin 5)) :=
    transportedAction_block_image hn hKH a ha e he
  let : (K.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hH
  have hr : ρ.range ≤ normalizer ((K.subgroupOf H).map ρ : Set _) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map] using
      (K.subgroupOf H).le_normalizer_map ρ
  rw [hi] at hr
  have hp (g : H) : ρ g ∈ (naturalMulAction (Fin 5)).range :=
    normalizer_alternatingFive_naturalMulAction_le_range (hr ⟨g,rfl⟩)
  have hj := naturalMulAction_injective_of_odd (Fin 5) (by decide)
  let q : H →* FivePerm :=
    (MonoidHom.ofInjective hj).symm.toMonoidHom.comp (ρ.codRestrict _ hp)
  have hq (g : H) : naturalMulAction (Fin 5) (q g) = ρ g :=
    MonoidHom.apply_ofInjective_symm hj ⟨ρ g,hp g⟩
  let c := coreEquivNatural (Fin 5) (by decide)
  let e' : sourceModule K ≃* Multiplicative (core (Fin 5)) :=
    e.trans c.symm.toAddEquiv.toMultiplicative
  refine ⟨q,e',?_,?_,?_⟩
  · calc
      q.ker = ρ.ker := by
        ext g
        change q g = 1 ↔ ρ g = 1
        rw [← hq,← (naturalMulAction (Fin 5)).map_one,hj.eq_iff]
      _ = _ := transportedAction_ker hn e
  · apply map_injective hj
    rw [map_map,show (naturalMulAction (Fin 5)).comp q = ρ from MonoidHom.ext hq,hi]
  · intro s u
    have hce : c (coreRepresentation (Fin 5) (q s) (e' u).toAdd) =
        naturalRepresentation (Fin 5) (q s) (e u).toAdd := by
      rw [coreEquivNatural_equivariant]
      change naturalRepresentation (Fin 5) (q s) (c (c.symm (e u).toAdd)) = _
      rw [c.apply_symm_apply]
    have hcoord : e'.symm (Multiplicative.ofAdd
        (coreRepresentation (Fin 5) (q s) (e' u).toAdd)) =
        e.symm (naturalMulAction (Fin 5) (q s) (e u)) := by
      apply e.injective
      change e (e.symm (Multiplicative.ofAdd (c (coreRepresentation (Fin 5) (q s) (e' u).toAdd)))) = _
      rw [e.apply_symm_apply,e.apply_symm_apply]
      exact congrArg Multiplicative.ofAdd hce
    rw [hcoord,hq]
    change (e.symm (e ⟨_,_⟩) : G) = _
    rw [e.symm_apply_apply]
    change (s : G) * (e.symm (e u) : G) * (s : G)⁻¹ = _
    rw [e.symm_apply_apply]

/-- B.3.2 applies to all elementary subgroups of the literal action quotient. -/
theorem noStrong_of_core_coordinates [Finite G]
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* FivePerm) (hker : q.ker = centralizer (V : Set G))
    (e : V ≃* Multiplicative (core (Fin 5)))
    (he : ∀ (s : G) (u : V),
      (e.symm (Multiplicative.ofAdd
        (coreRepresentation (Fin 5) (q s) (e u).toAdd)) : G) = s * (u : G) * s⁻¹)
    (R : Subgroup G) : ChapterB.BaumannArgument.NoStrongOffenders V R := by
  let π := QuotientGroup.mk' (centralizer (V : Set G))
  let f := QuotientGroup.lift _ q hker.symm.le
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_lift,hker]
    exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
  let ρ := NormalElementaryQuotient.representation V π
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let E : Additive V ≃ₗ[ZMod 2] core (Fin 5) :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) e.bijective
  have hE : ∀ g v, E (ρ g v) = coreRepresentation (Fin 5) (f g) (E v) := by
    intro g v
    obtain ⟨s,rfl⟩ := QuotientGroup.mk'_surjective _ g
    apply Multiplicative.ofAdd.injective
    apply e.symm.injective
    apply Subtype.ext
    change (e.symm (e (ρ (π s) v).toMul) : G) = _
    rw [e.symm_apply_apply]
    exact (NormalElementaryQuotient.representation_apply V π
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) s v).trans (he s v.toMul).symm
  apply ChapterB.BaumannArgument.noStrong_of_centralizer_quotient V π
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) _ R
  rintro ⟨A,hA⟩
  apply ChapterB.Offenders.Odd.not_isStrongOffender_core (Or.inl rfl) (A.map f)
  refine ⟨⟨?_,hA.1.2.map f⟩,?_⟩
  · intro hz
    exact hA.1.1 ((map_injective hf) (hz.trans (map_bot f).symm))
  · rw [← fixedCodim_map_equivariant ρ (coreRepresentation (Fin 5)) f E hE,
      rank_map_injective f hf]
    exact hA.2

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
