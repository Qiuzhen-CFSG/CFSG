module

public import CFSG.Quasithin.ChapterJ.Section05.SecondOrbit
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Outer.Normalizer

/-! The unchanged second source point has a semidihedral Sylow subgroup of
order sixteen. The checked outer actor supplies the model fact; the original
marked J.4.7 equivalence transports it without replacing either q or g.
Source: Aschbacher–Smith J.5.4, printed pp.445–446. -/

public section
noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05
open RuSubgroup Centralizers.Choices Tits.ExceptionalParabolics.FullRee

private theorem transport_sylow {H : Type*} [Group H]
    (e : H ≃* FiveOvergroups.candidateNormalizer) :
    ∃ S : Sylow 2 H, Nat.card S=16 ∧ Stellmacher.IsSemidihedralGroup S := by
  let P := Tits.Max4Outer.sylow
  let S := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hc : Nat.card P=16 := by
    change Nat.card (Tits.Max4Outer.sylow : Subgroup FiveOvergroups.candidateNormalizer)=16
    rw [Tits.Max4Outer.sylow_coe]
    exact Tits.Max4Outer.sixteen_spec.1
  refine ⟨S,?_,?_⟩
  · change Nat.card ((P : Subgroup FiveOvergroups.candidateNormalizer).map e.symm.toMonoidHom)=16
    rw [card_map_of_injective e.symm.injective]
    exact hc
  · change Stellmacher.IsSemidihedralGroup
      ((P : Subgroup FiveOvergroups.candidateNormalizer).map e.symm.toMonoidHom)
    exact Semidihedral.of_mulEquiv (e.symm.subgroupMap _) Tits.Max4Outer.sylow_semidihedral

variable {G : Type*} [Group G] [Finite G] (d : LocalSetup G)

theorem source_second_stabilizer_semidihedral (B5 : Sylow 5 d.toTypeRuSetup.H)
    (F : Subgroup G) (h5 : Q₅ d B5 ≤ F) (hB : B5Image B5 ≤ F)
    (e : F ≃* ReeF4.Model 0) (P : Sylow 5 F) {g : G} (hg : g ∉ F)
    (hP : (P : Subgroup F) ≤ stabilizer F (g • basePoint F))
    (hlarge : 15600 ≤ Nat.card (stabilizer F (g • basePoint F))) :
    ∃ S : Sylow 2 (stabilizer F (g • basePoint F)),
      Nat.card S=16 ∧ Stellmacher.IsSemidihedralGroup S := by
  obtain ⟨f⟩ := source_second_stabilizer_equiv d B5 F h5 hB e P hg hP hlarge
  exact transport_sylow f

theorem SourceChoice.source_second_orbit_semidihedral {d : LocalSetup G} (p : Plane d)
    (s : SourceChoice p) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hi : ∀ a ∈ B5Image B5, s.v * a * s.v⁻¹ = a⁻¹)
    (X : Sylow 3 p.parabolic) (e : p.F B5 X ≃* ReeF4.Model 0)
    (hmark : ((p.F₁ B5).subgroupOf (p.F B5 X)).map e.toMonoidHom = first)
    (P : Sylow 5 (p.F B5 X)) :
    ∃ q g : G, q ∈ d.toTypeRuSetup.Q ∧ q ∉ p.F B5 X ∧
      g ∈ normalizer (((P : Subgroup (p.F B5 X)).map (p.F B5 X).subtype) : Set G) ∧
      g ∉ p.F B5 X ∧ Nat.card (Cosets (p.F B5 X)) = 4060 ∧
      Nat.card (orbit (p.F B5 X) (q • basePoint (p.F B5 X))) = 1755 ∧
      Nat.card (stabilizer (p.F B5 X) (g • basePoint (p.F B5 X))) = 15600 ∧
      Nat.card (orbit (p.F B5 X) (g • basePoint (p.F B5 X))) = 2304 ∧
      orbit (p.F B5 X) (g • basePoint (p.F B5 X)) =
        (({basePoint (p.F B5 X)} : Set (Cosets (p.F B5 X))) ∪
          orbit (p.F B5 X) (q • basePoint (p.F B5 X)))ᶜ ∧
      ∃ S : Sylow 2 (stabilizer (p.F B5 X) (g • basePoint (p.F B5 X))),
        Nat.card S=16 ∧ Stellmacher.IsSemidihedralGroup S := by
  obtain ⟨q,g,hq,hqF,hg,hgF,hcos,hfirst,hstab,hsecond,hrem,⟨f⟩⟩ :=
    SourceChoice.source_second_orbit p s B5 hi X e hmark P
  exact ⟨q,g,hq,hqF,hg,hgF,hcos,hfirst,hstab,hsecond,hrem,transport_sylow f⟩

end CFSG.Quasithin.ChapterJ.Section05
