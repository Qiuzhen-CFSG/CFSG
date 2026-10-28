module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.PairedConfiguration
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.ActionRelabel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.SourceCompletion

/-!
Normalize the actual natural action in the end-node parabolic of [AS,
15.3.25]. Sylow conjugacy is applied inside the four-block stabilizer, so
all original ambient subgroups and all three star markings are retained.
Only the eight permutation labels and their compatible module coordinates
change. The resulting Sylow image is the fixed model used by the paired
quotient calculation.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterB.Offenders.Eight
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open RankOneConfiguration EightGeometry PairedQuotient
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

private theorem conjugate_sylow_inside {H : Type*} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (N : Subgroup H) (P Q : Sylow p H)
    (hp : (P : Subgroup H) ≤ N) (hq : (Q : Subgroup H) ≤ N) :
    ∃ g : N, (P : Subgroup H).map (MulAut.conj (g : H)).toMonoidHom = Q := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq N (P.subtype hp) (Q.subtype hq)
  refine ⟨g,?_⟩
  have he : ((P.subtype hp : Sylow p N) : Subgroup N).map
      (MulAut.conj g).toMonoidHom = (Q.subtype hq : Sylow p N) := by
    change ((g • P.subtype hp : Sylow p N) : Subgroup N) = _
    rw [hg]
  have hmap := congrArg (fun A : Subgroup N => A.map N.subtype) he
  rw [Sylow.coe_subtype,Sylow.coe_subtype,map_subgroupOf_eq_of_le hq] at hmap
  rw [← map_subgroupOf_eq_of_le hp, map_map]
  rw [map_map] at hmap
  exact hmap

namespace EndNodeData
/-- The original marked action can be normalized inside the end-node parabolic,
while every ambient group and source hypothesis remains the same. -/
theorem exists_normalized (e : EndNodeData d I c) :
    ∃ e' : EndNodeData d I c,
      (d.S.subgroupOf I).map e'.action.actor = canonicalSylow ∧
      (∀ i : I, e'.marking.equiv (d.starMap I i) = e'.action.actor i) := by
  let f : I →* Equiv.Perm (Fin 8) := e.marking.equiv.toMonoidHom.comp (d.starMap I)
  have hf : Function.Surjective f := e.marking.equiv.surjective.comp
    (QuotientGroup.mk'_surjective _)
  let P := e.source.sylow.mapSurjective hf
  have hPS : (P : Subgroup (Equiv.Perm (Fin 8))) = (d.S.subgroupOf I).map f := by
    change (e.source.sylow : Subgroup I).map f = _
    congr 1
    rw [←e.source.sylow_eq]
    exact (comap_map_eq_self_of_injective I.subtype_injective _).symm
  have hPF : (P : Subgroup (Equiv.Perm (Fin 8))) ≤ fourStabilizer := by
    rw [hPS,←e.extended_image]
    change (d.S.subgroupOf I).map f ≤
      ((((c.L ⊓ centralizer (d.ZS : Set G)) ⊔ d.S).subgroupOf I).map (d.starMap I)).map e.marking.equiv.toMonoidHom
    rw [map_map]
    exact map_mono (comap_mono le_sup_right)
  obtain ⟨g,hg⟩ := conjugate_sylow_inside fourStabilizer P canonicalSylow hPF sylow_le_parabolic
  let a := e.action.relabel ((g : Equiv.Perm (Fin 8)) * e.marking.relabel)
  let b : CompatibleStarMarking d I (d.componentModule I c.L) a := {
    equiv := e.marking.equiv.trans (MulAut.conj (g : Equiv.Perm (Fin 8)))
    relabel := 1
    compatible := by
      intro i
      change (g : Equiv.Perm (Fin 8)) * e.marking.equiv (d.starMap I i) * (g : Equiv.Perm (Fin 8))⁻¹ =
        1 * a.actor i * 1⁻¹
      rw [e.marking.compatible,one_mul,inv_one,mul_one]
      dsimp only [a]
      rw [NaturalEightAction.relabel_actor]
      group }
  have hfour : fourStabilizer.map (MulAut.conj (g : Equiv.Perm (Fin 8))).toMonoidHom = fourStabilizer :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer g.property)
  have halt : (alternatingGroup (Fin 8)).map (MulAut.conj (g : Equiv.Perm (Fin 8))).toMonoidHom = alternatingGroup (Fin 8) :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [Subgroup.normalizer_eq_top]; trivial)
  have hmap (A : Subgroup G) : (d.starImage I A).map b.equiv.toMonoidHom =
      ((d.starImage I A).map e.marking.equiv.toMonoidHom).map
        (MulAut.conj (g : Equiv.Perm (Fin 8))).toMonoidHom := by rw [map_map]; rfl
  let e' : EndNodeData d I c := { e with
    action := a
    marking := b
    component_image := by rw [hmap,e.component_image,halt]
    parabolic_image := by rw [hmap,e.parabolic_image,Subgroup.map_inf _ _ _ (MulAut.conj _).injective,hfour,halt]
    extended_image := by rw [hmap,e.extended_image,hfour] }
  have hb (i : I) : b.equiv (d.starMap I i) = a.actor i := by
    have hb := b.compatible i
    change b.equiv (d.starMap I i) = 1 * a.actor i * 1⁻¹ at hb
    simpa only [one_mul,inv_one,mul_one] using hb
  refine ⟨e',?_,hb⟩
  change (d.S.subgroupOf I).map a.actor = _
  have ha : a.actor = (MulAut.conj (g : Equiv.Perm (Fin 8))).toMonoidHom.comp f := by
    apply MonoidHom.ext
    intro i
    exact (hb i).symm
  rw [ha,←map_map,←hPS,hg]

end EndNodeData
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
