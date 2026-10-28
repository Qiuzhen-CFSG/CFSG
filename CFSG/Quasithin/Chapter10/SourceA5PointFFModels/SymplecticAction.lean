module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SymplecticActionTransport
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SymplecticImage
public import CFSG.Quasithin.Chapter4.Defs
public import Theory.GroupTheory.CommutatorPreimage.Membership

/-!
# The symplectic moving cubic from the actual local A₅ section

The local-section sieve forces field order four using the specified actor
marking. The natural-module theorem then moves the given nonzero full-Sylow
fixed vector. Its normalizer and core commutator conclusions put the cubic
in the literal section centralizer of the original model subgroup.

This discharges model movement in the symplectic row of Aschbacher–Smith
10.2.9, pp.751–752; original-group lifting remains with the source assembly.
-/

public section
open Subgroup Representation Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter10
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings.FiveLocalFF
open ChapterB.QuasisimpleSource Chapter4
noncomputable section
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V}

theorem source_a5_point_symplectic_ff_moving_cubic
    {F : BinaryField} (hlarge : 1 < F.degree)
    (e : ActionEquiv ρ (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2)))
    (S : Sylow 2 D) (B : Subgroup D) (hB : B ∈ localCComponents S)
    (hproper : B ≠ ⊤) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (v : V) (hv : v ≠ 0) (hfix : ∀ s ∈ (S : Subgroup D), ρ s v = v) :
    ∃ x : D, orderOf x = 3 ∧ x ∈ sectionCentralizer B ∧ ρ x v ≠ v := by
  let a := e.groupEquiv
  have hks : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  have hi : Function.Injective (a.toMonoidHom.subgroupMap B) := by
    intro x y h
    exact Subtype.ext (a.injective (congrArg Subtype.val h))
  have hk : IsPGroup 2 (a.toMonoidHom.subgroupMap B).ker := by
    rw [(a.toMonoidHom.subgroupMap B).ker_eq_bot_iff.mpr hi]
    exact IsPGroup.of_subsingleton 2 _
  have hp : B.map a.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hproper
    apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
    rw [ht,map_top_of_surjective _ a.surjective]
  have hF : Nat.card F.Carrier = 4 :=
    (symplectic_five_section_image F.card_eq hlarge a.toMonoidHom a.surjective
      hks S B hB hk hp eB).1
  obtain ⟨x,ho,hn,hc,hm⟩ := marked_symplectic_local_moving_cubic ρ hF e S B hB hproper v hv hfix
  exact ⟨x,ho,(mem_commutatorPreimage_iff _ _ _
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B)) x).mpr ⟨hn,hc⟩,hm⟩
end
end CFSG.Quasithin.Chapter10
