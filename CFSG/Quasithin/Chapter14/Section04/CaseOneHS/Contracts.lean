module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Geometry
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Type
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.FiveLines

/-!
# Independent source interfaces for the nonextraspecial branch

`LocalStructure` contains the intermediate conclusions of 14.3.31--32.
The natural action is on the literal U/Z(U), through H/O₂(H), and has
coordinates in F₄² for SL₂(4) extended by field Frobenius. Indecomposability
means no two nonzero invariant subgroups complement one another in the
original elementary tilded module. The component and commutator use their
original embeddings in H and G.

`OvergroupStructure` contains the terminal normalizer and core conclusions
of 14.3.33. Its producer may take `LocalStructure` as an earlier premise;
the parent CaseOneHS assembly must construct both. These are specifications,
not assertions of either book lemma. The independent universal I.4.8
recognition input is defined in HigmanSims/Type.

Source: Aschbacher--Smith, printed pp.1002--1005, 14.3.31--33 and the
application of I.4.8. Only the facts consumed by that application are retained
in `OvergroupStructure`; its proof still requires the original transfer.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Indecomposability on the literal quotient image, for the indicated actors. -/
def TildeIndecomposable (F : InvariantFlag T V 3) (K : Subgroup G) : Prop :=
  ∀ A B : Subgroup (F.tilde F.U),
    (∀ k : F.H, (k : G) ∈ K →
      A.map ((F.localTildeAction F.H le_rfl) k).toMonoidHom = A) →
    (∀ k : F.H, (k : G) ∈ K →
      B.map ((F.localTildeAction F.H le_rfl) k).toMonoidHom = B) →
    IsCompl A B → A = ⊥ ∨ B = ⊥

/-- The precise local output of 14.3.31--32, before 14.3.33. -/
structure LocalStructure (L : Subgroup G) (F : InvariantFlag T V 3) : Prop where
  centerless : Chapter12.Section08.centerIn (F.I₂ L) = ⊥
  core_shape : HigmanSims.CoreShape F.U
  natural : ∃
    (e : (F.H ⧸ pCore 2 F.H) ≃* Representation.SL2FourNatural.SemilinearNormalizer.specialField)
    (c : F.Uhat ≃* Multiplicative Representation.SL2FourNatural.V),
    ∀ (h : F.H) (x : F.Uhat),
      (c (F.uhatAction h x)).toAdd =
        (e (QuotientGroup.mk' (pCore 2 F.H) h)).val (c x).toAdd
  kernel : F.uhatAction.ker = pCore 2 F.H
  component : ∃ K : Subgroup G, K ≤ F.H ∧ (K.subgroupOf F.H).IsCComponent ∧
    F.H = K ⊔ (T : Subgroup G) ∧ F.U = ⁅K.pCoreIn 2, K⁆ ∧
    TildeIndecomposable F K

/-- Consequences of the natural coordinates; the S₅ quotient is the same
literal quotient used in the equivariance assertion. -/
theorem LocalStructure.quotient (F : InvariantFlag T V 3) (s : LocalStructure L F) :
    Nonempty ((F.H ⧸ pCore 2 F.H) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨e, _, _⟩ := s.natural
  exact ⟨e.trans Representation.SL2FourNatural.SemilinearNormalizer.symmetricFiveEquiv⟩

/-- Indecomposability for the component implies it for the full H-action. -/
theorem LocalStructure.indecomposable (F : InvariantFlag T V 3)
    (s : LocalStructure L F) : TildeIndecomposable F F.H := by
  obtain ⟨K, _, _, _, _, hi⟩ := s.component
  intro A B hA hB hcompl
  exact hi A B (fun k _ => hA k k.property) (fun k _ => hB k k.property) hcompl

/-- The terminal source output. The normalizers are actual ambient subgroups,
and the homocyclic core is the intrinsic core of the original L. -/
structure OvergroupStructure (L : Subgroup G) (F : InvariantFlag T V 3) : Prop where
  closure_core : F.U = F.H.pCoreIn 2
  seed_normalizer : normalizer (V : Set G) = L
  actor_normalizer : normalizer (L : Set G) = L
  homocyclic : Nonempty (pCore 2 L ≃* (Fin 3 → Multiplicative (ZMod 4)))

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
