module

public import CFSG.Quasithin.ChapterJ.Section05.SecondOrbit
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Core

/-!
# The actual second stabilizer has the marked perfect core

The second source orbit is now linked to the concrete max4 candidate. Its
stabilizer has index-two commutator, and that commutator is equivalent to the
literal max4 subgroup under the fixed Atlas embedding. This is the exact
normal-core information needed before an outer PSL₂(25)⁺ marking.

The preceding source theorem supplies the genuine J.4.7 equivalence and
Sylow-five normalizer point; no abstract full-Ree or maximal-subgroup
classification is used. The remaining model task is to prove the concrete
normalizer's outer action and semidihedral Sylow-2 structure.
-/

public section
noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05
open RuSubgroup Centralizers.Choices Tits.ExceptionalParabolics.FullRee
variable {G : Type*} [Group G] [Finite G] (d : LocalSetup G)

theorem source_second_stabilizer_derived (B5 : Sylow 5 d.toTypeRuSetup.H)
    (F : Subgroup G) (h5 : Q₅ d B5 ≤ F) (hB : B5Image B5 ≤ F)
    (e : F ≃* ReeF4.Model 0) (P : Sylow 5 F) {g : G} (hg : g ∉ F)
    (hP : (P : Subgroup F) ≤ stabilizer F (g • basePoint F))
    (hlarge : 15600 ≤ Nat.card (stabilizer F (g • basePoint F))) :
    (commutator (stabilizer F (g • basePoint F))).index = 2 ∧
      Nonempty (commutator (stabilizer F (g • basePoint F)) ≃* Tits.MinimumIndexCandidates.max4) := by
  let K := (stabilizer F (g • basePoint F)).map e.toMonoidHom
  let eK : stabilizer F (g • basePoint F) ≃* K := e.subgroupMap _
  have he : (commutator (stabilizer F (g • basePoint F))).map eK.toMonoidHom = commutator K := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr eK.surjective,← _root_.commutator_def]
  have hD : ¬ FiveOvergroups.D ≤ K :=
    source_stabilizer_not_contains_derived d B5 F h5 hB e hg
  have hc : Nat.card K = Nat.card (stabilizer F (g • basePoint F)) :=
    card_map_of_injective e.injective
  have h25 : 25 ∣ Nat.card K := by
    rw [hc,← recognized_sylow_five_card F e P]
    exact card_dvd_of_le hP
  have hi := FiveOvergroups.large_commutator_index K hD h25 (hc ▸ hlarge)
  have hi' : (commutator (stabilizer F (g • basePoint F))).index = 2 := by
    rw [← he,index_map_of_bijective eK.bijective] at hi
    exact hi
  obtain ⟨f⟩ := FiveOvergroups.large_commutator_equiv K hD h25 (hc ▸ hlarge)
  exact ⟨hi',⟨(eK.subgroupMap _).trans ((MulEquiv.subgroupCongr he).trans f)⟩⟩

/-- The same original second orbit retains its concrete index-two derived core. -/
theorem SourceChoice.source_second_orbit_derived {d : LocalSetup G} (p : Plane d)
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
        Tits.MinimumIndexCandidates.max4) := by
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
  have hd := source_second_stabilizer_derived d B5 F
    (le_sup_right.trans (le_sup_left.trans le_sup_left))
    (le_sup_right.trans le_sup_left) e P hgF hP (by rw [hstab])
  exact ⟨q,g,hq,hqF,hg,hgF,hcos,hfirst,hstab,hsecond,hrem,hd⟩
end CFSG.Quasithin.ChapterJ.Section05
