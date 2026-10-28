module

public import CFSG.Quasithin.ChapterJ.Section05.SemidihedralStabilizer
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Outer.Mixed.Comparison

/-! The same second source stabilizer is PSL₂(25)⁺, realized as the actual
mixed projective semilinear subgroup over the quadratic field of order 25.
The native outside square and generator actions discharge the model
identification; the order-16 semidihedral Sylow conclusion is also retained.
Only the preceding marked J.4.7 equivalence of the original subgroup F
remains an earlier-source input. Neither original source point is reselected.
Source: Aschbacher–Smith J.5.4–5, printed pp.445–446. -/

public section
noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05
open RuSubgroup Centralizers.Choices Tits.ExceptionalParabolics.FullRee
variable {G : Type*} [Group G] [Finite G] (d : LocalSetup G)

theorem source_second_stabilizer_plus (B5 : Sylow 5 d.toTypeRuSetup.H)
    (F : Subgroup G) (h5 : Q₅ d B5 ≤ F) (hB : B5Image B5 ≤ F)
    (e : F ≃* ReeF4.Model 0) (P : Sylow 5 F) {g : G} (hg : g ∉ F)
    (hP : (P : Subgroup F) ≤ stabilizer F (g • basePoint F))
    (hlarge : 15600 ≤ Nat.card (stabilizer F (g • basePoint F))) :
    Nonempty (stabilizer F (g • basePoint F) ≃* Tits.Max4Outer.Mixed.Plus) := by
  obtain ⟨f⟩ := source_second_stabilizer_equiv d B5 F h5 hB e P hg hP hlarge
  obtain ⟨j,_⟩ := Tits.Max4Outer.Mixed.exists_normalizer_equiv_plus
  exact ⟨f.trans j⟩

theorem SourceChoice.source_second_orbit_plus {d : LocalSetup G} (p : Plane d)
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
      Nonempty (stabilizer (p.F B5 X) (g • basePoint (p.F B5 X)) ≃*
        Tits.Max4Outer.Mixed.Plus) ∧
      ∃ S : Sylow 2 (stabilizer (p.F B5 X) (g • basePoint (p.F B5 X))),
        Nat.card S=16 ∧ Stellmacher.IsSemidihedralGroup S := by
  obtain ⟨q,g,hq,hqF,hg,hgF,hcos,hfirst,hstab,hsecond,hrem,hS⟩ :=
    SourceChoice.source_second_orbit_semidihedral p s B5 hi X e hmark P
  let F := p.F B5 X
  have hP : (P : Subgroup F) ≤ stabilizer F (g • basePoint F) := by
    intro x hx
    have he : ((P : Subgroup F).map F.subtype).map (MulAut.conj g).toMonoidHom =
        (P : Subgroup F).map F.subtype := mem_normalizer_iff_map_conj_eq.mp hg
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) (map_subtype_le (P : Subgroup F))
    rw [he] at hh
    have hx' := hh (mem_map_of_mem F.subtype hx)
    change (x : G) ∈ stabilizer G (g • basePoint F)
    rwa [stabilizer_smul_eq_stabilizer_map_conj,stabilizer_quotient]
  have hj := source_second_stabilizer_plus d B5 F
    (le_sup_right.trans (le_sup_left.trans le_sup_left))
    (le_sup_right.trans le_sup_left) e P hgF hP (by rw [hstab])
  exact ⟨q,g,hq,hqF,hg,hgF,hcos,hfirst,hstab,hsecond,hrem,hj,hS⟩

end CFSG.Quasithin.ChapterJ.Section05
