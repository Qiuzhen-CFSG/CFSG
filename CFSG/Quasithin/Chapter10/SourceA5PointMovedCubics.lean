module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.FullMovedProjection
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Irreducible
public import CFSG.Quasithin.Chapter10.SourceA5PointFFModels.SymplecticAction
public import CFSG.Quasithin.Chapter10.SourceA5PointFFModels.LinearSource

/-!
# Cubic movement lifted from the actual moved section

A component-nonfixed seed survives the literal central quotient. Natural
SL3 and Sp4 model cubics therefore move that original seed; for Sp4 its
full-Sylow fixedness is retained. The repeated SL3 model acts directly on
the whole moved space. These are the three scalar-action consumers in
Aschbacher–Smith 10.2.9, printed pp.751–752.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10
open ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G}

theorem source_a5_point_symplectic_section_moving_cubic
    (s : MovedSection ρ K) (hm : moved ρ K = ⊤)
    {F : BinaryField} (hlarge : 1 < F.degree)
    (e : ActionEquiv (s.central.quotientRepresentation.comp K.subtype) (binarySymplectic F))
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
  obtain ⟨x,hx,hB,hmove⟩ := source_a5_point_symplectic_ff_moving_cubic
    hlarge e R B hB hproper eB w hw hf
  refine ⟨x,hx,hB,?_⟩
  intro he
  apply hmove
  change s.central.quotientRepresentation (x : G) w = w
  rw [←s.fullProjection_intertwines hm,he]

theorem source_a5_point_linear_section_moving_cubic
    (s : MovedSection ρ K) (hm : moved ρ K = ⊤)
    {F : BinaryField}
    (e : ActionEquiv (s.central.quotientRepresentation.comp K.subtype) (linearNatural F 3))
    (R : Sylow 2 K) (B : Subgroup K) (hB : B ∈ ChapterA.Section03.localCComponents R)
    (hproper : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (v : V) (hv : v ∉ fixedSpace ρ K) :
    ∃ x : K, orderOf x = 3 ∧ x ∈ Chapter4.sectionCentralizer B ∧ ρ (x : G) v ≠ v := by
  let w := s.fullProjection hm v
  have hw : w ≠ 0 := fun hz => hv ((s.fullProjection_eq_zero_iff hm v).mp hz)
  obtain ⟨x,hx,hB,hmove⟩ := source_a5_point_linear_ff_moving_cubic e R B hB hproper eB hw
  refine ⟨x,hx,hB,?_⟩
  intro he
  apply hmove
  change s.central.quotientRepresentation (x : G) w = w
  rw [←s.fullProjection_intertwines hm,he]
theorem source_a5_point_repeated_section_moving_cubic
    (s : MovedSection ρ K) (hm : moved ρ K = ⊤)
    {F : BinaryField} {r : ℕ}
    (e : ActionEquiv (s.space.toRepresentation.comp K.subtype) (repeated (linearNatural F 3) r))
    (R : Sylow 2 K) (B : Subgroup K) (hB : B ∈ ChapterA.Section03.localCComponents R)
    (hproper : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (v : V) (hv : v ∉ fixedSpace ρ K) :
    ∃ x : K, orderOf x = 3 ∧ x ∈ Chapter4.sectionCentralizer B ∧ ρ (x : G) v ≠ v := by
  let w : s.space.toSubmodule := ⟨v,by rw [s.space_eq,hm]; trivial⟩
  have hw : w ≠ 0 := by
    intro hz
    have hv0 : v = 0 := congrArg Subtype.val hz
    exact hv (hv0 ▸ (fixedSpace ρ K).zero_mem)
  obtain ⟨x,hx,hB,hmove⟩ := source_a5_point_repeated_linear_ff_moving_cubic e R B hB hproper eB hw
  refine ⟨x,hx,hB,?_⟩
  intro he
  apply hmove
  exact Subtype.ext he
end CFSG.Quasithin.Chapter10
