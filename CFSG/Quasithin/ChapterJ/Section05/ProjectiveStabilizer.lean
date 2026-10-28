module

public import CFSG.Quasithin.ChapterJ.Section05.DerivedStabilizer
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Equivalence

/-!
# The genuine PSL₂(25) core of the second source stabilizer

The paired-cover equivalence identifies the literal max4 core with the
actual PSL₂ group over a field of25 elements. The original second orbit
therefore has a stabilizer whose derived subgroup is PSL₂(25), of index two.
All coset points, Sylow-five maps, and the earlier marked J.4.7 equivalence
are retained. No new recognition or order premise is introduced.

The remaining J.5.4 model obligation is the outer-action marking and the
semidihedral Sylow-2 structure of this extension; that conclusion is not
inferred merely from its index or order.
Source: Aschbacher–Smith J.5.4, printed pp.445–446.
-/

public section
noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05
open RuSubgroup Centralizers.Choices Tits.ExceptionalParabolics.FullRee
variable {G : Type*} [Group G] [Finite G] (d : LocalSetup G)

theorem source_second_stabilizer_psl (B5 : Sylow 5 d.toTypeRuSetup.H)
    (F : Subgroup G) (h5 : Q₅ d B5 ≤ F) (hB : B5Image B5 ≤ F)
    (e : F ≃* ReeF4.Model 0) (P : Sylow 5 F) {g : G} (hg : g ∉ F)
    (hP : (P : Subgroup F) ≤ stabilizer F (g • basePoint F))
    (hlarge : 15600 ≤ Nat.card (stabilizer F (g • basePoint F))) :
    (commutator (stabilizer F (g • basePoint F))).index = 2 ∧
      Nonempty (commutator (stabilizer F (g • basePoint F)) ≃* Tits.Max4Projective.PSL) := by
  obtain ⟨hi,⟨f⟩⟩ := source_second_stabilizer_derived d B5 F h5 hB e P hg hP hlarge
  exact ⟨hi,⟨f.trans Tits.Max4Projective.nativeEquiv⟩⟩

/-- The same original second orbit retains its concrete index-two derived core. -/
theorem SourceChoice.source_second_orbit_psl {d : LocalSetup G} (p : Plane d)
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
      (commutator (stabilizer (p.F B5 X) (g • basePoint (p.F B5 X)))).index = 2 ∧
      Nonempty (commutator (stabilizer (p.F B5 X) (g • basePoint (p.F B5 X))) ≃*
        Tits.Max4Projective.PSL) := by
  obtain ⟨q,g,hq,hqF,hg,hgF,hcos,hfirst,hstab,hsecond,hrem,_⟩ :=
    SourceChoice.source_second_orbit p s B5 hi X e hmark P
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
  have hd := source_second_stabilizer_psl d B5 F
    (le_sup_right.trans (le_sup_left.trans le_sup_left))
    (le_sup_right.trans le_sup_left) e P hgF hP (by rw [hstab])
  exact ⟨q,g,hq,hqF,hg,hgF,hcos,hfirst,hstab,hsecond,hrem,hd⟩
end CFSG.Quasithin.ChapterJ.Section05
