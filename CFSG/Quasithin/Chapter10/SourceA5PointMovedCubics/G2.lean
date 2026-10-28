module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.FullMovedProjection
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Irreducible
public import CFSG.Quasithin.Chapter10.SourceA5PointFFModels.G2Action

/-!
# G2 cubic movement on the actual moved section

The original component-nonfixed seed survives the literal central quotient.
Its full-Sylow fixedness is preserved there, so the natural G2 moving cubic
also moves the original seed. Source: Aschbacher–Smith 10.2.9, pp.751–752.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10
open ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G}

theorem source_a5_point_g2_section_moving_cubic
    (s : MovedSection ρ K) (hm : moved ρ K = ⊤)
    {F : BinaryField} (hlarge : 1 < F.degree)
    (e : ActionEquiv (s.central.quotientRepresentation.comp K.subtype) (binaryG2 F))
    (R : Sylow 2 K) (B : Subgroup K) (hB : B ∈ ChapterA.Section03.localCComponents R)
    (hproper : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (v : V) (hv : v ∉ fixedSpace ρ K)
    (hfix : ∀ r ∈ (R : Subgroup K), ρ (r : G) v = v) :
    ∃ x : K, orderOf x = 3 ∧ x ∈ Chapter4.sectionCentralizer B ∧ ρ (x : G) v ≠ v := by
  let w := s.fullProjection hm v
  have hw : w ≠ 0 := fun hz => hv ((s.fullProjection_eq_zero_iff hm v).mp hz)
  have hf : ∀ r ∈ (R : Subgroup K),
      (s.central.quotientRepresentation.comp K.subtype) r w = w := by
    intro r hr
    change s.central.quotientRepresentation (r : G) w = w
    rw [←s.fullProjection_intertwines hm, hfix r hr]
  obtain ⟨x,hx,hB,hmove⟩ := source_a5_point_g2_ff_moving_cubic
    hlarge e R B hB hproper eB w hw hf
  refine ⟨x,hx,hB,?_⟩
  intro he
  apply hmove
  change s.central.quotientRepresentation (x : G) w = w
  rw [←s.fullProjection_intertwines hm,he]

end CFSG.Quasithin.Chapter10
