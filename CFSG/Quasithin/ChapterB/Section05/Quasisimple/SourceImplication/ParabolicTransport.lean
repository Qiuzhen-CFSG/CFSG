module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCentralizer
public import Theory.Representation.BinaryOffender.SectionLinear

/-!
# Transport of the B.5.1 Sylow-fixed centralizer

Equivariant group and linear isomorphisms identify the literal pointwise
centralizers, intrinsic two-cores, ambient core images, and core quotients.
Adding a globally fixed supplement preserves the centralizer. Restricting an
offender to the invariant summand does not increase fixed codimension; best
replacement then transfers the concrete model's exclusion of best offenders.

These identities are consumed by `ParabolicConclusion`, which derives its
fixed supplement by cohomology and proves B.5.1(6) on the original module.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(6),
printed pp.99 and 103.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
universe u v w z
variable {G : Type u} {H : Type v} [Group G] [Group H]
  {V : Type w} {W : Type z} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) H W}

/-- Both actor and module maps preserve the actual fixed-space centralizer. -/
theorem ActionEquiv.fixedCentralizer_map (e : ActionEquiv ρ σ)
    (A L : Subgroup G) :
    (subspaceKernel ρ (fixedSpace ρ A) L).map e.groupEquiv.toMonoidHom =
      subspaceKernel σ (fixedSpace σ (A.map e.groupEquiv.toMonoidHom))
        (L.map e.groupEquiv.toMonoidHom) := by
  rw [← fixedSpace_map_equivariant ρ σ e.groupEquiv.toMonoidHom
    e.linearEquiv e.intertwines A]
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem _ hg.1, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact (e.intertwines g v).symm.trans (congrArg e.linearEquiv (hg.2 v hv))
  · rintro ⟨⟨g, hg, rfl⟩, hfix⟩
    refine ⟨g, ⟨hg, ?_⟩, rfl⟩
    intro v hv
    apply e.linearEquiv.injective
    rw [e.intertwines]
    exact hfix _ ⟨v, hv, rfl⟩

/-- The centralizer equivalence restricts the specified ambient group map. -/
noncomputable def ActionEquiv.fixedCentralizerEquiv (e : ActionEquiv ρ σ)
    (A L : Subgroup G) :
    subspaceKernel ρ (fixedSpace ρ A) L ≃*
      subspaceKernel σ (fixedSpace σ (A.map e.groupEquiv.toMonoidHom))
        (L.map e.groupEquiv.toMonoidHom) :=
  (e.groupEquiv.subgroupMap _).trans (MulEquiv.subgroupCongr (e.fixedCentralizer_map A L))

/-- Transport every parabolic clause, including exclusion from the ambient core. -/
theorem sylowFixedCentralizer_transport [Finite G] [Finite H]
    [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]
    (e : ActionEquiv ρ σ) (L : Subgroup G) (d : ℕ) (T : Sylow 2 G)
    (h : SylowFixedCentralizer σ (L.map e.groupEquiv.toMonoidHom) d
      (T.mapSurjective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.surjective)) :
    Nonempty (SylowFixedCentralizer ρ L d T) := by
  let c := e.fixedCentralizerEquiv T L
  let ec := (c.subgroupMap (pCore 2 _)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 c))
  refine ⟨{ extraspecial := h.extraspecial.of_mulEquiv ec.symm
            core_order := (Nat.card_congr ec.toEquiv).trans h.core_order
            quotientEquiv := (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
              h.quotientEquiv
            no_offenders := ?_ }⟩
  intro A hA hle
  have hAo := (hA.isOffender ρ).map_equivariant ρ σ e.groupEquiv.toMonoidHom
    e.groupEquiv.injective e.linearEquiv e.intertwines
  obtain ⟨B, hBA, hB⟩ := hAo.exists_bestOffender σ
  apply h.no_offenders B hB
  have hm := Subgroup.map_mono (f := e.groupEquiv.toMonoidHom) hle
  change A.map e.groupEquiv.toMonoidHom ≤
    ((subspaceKernel ρ (fixedSpace ρ T) ⊤).pCoreIn 2).map e.groupEquiv.toMonoidHom at hm
  rw [map_pCoreIn_of_injective 2 _ _ e.groupEquiv.injective,
    e.fixedCentralizer_map, Subgroup.map_top_of_surjective _ e.groupEquiv.surjective] at hm
  exact hBA.trans hm

variable (ρ)

/-- A globally fixed supplement does not change any fixed-space centralizer. -/
theorem fixedCentralizer_eq_of_fixed_supplement (U : Subrepresentation ρ)
    (hsum : U.toSubmodule ⊔ ρ.invariants = ⊤) (A L : Subgroup G) :
    subspaceKernel ρ (fixedSpace ρ A) L =
      subspaceKernel U.toRepresentation (fixedSpace U.toRepresentation A) L := by
  ext g
  constructor
  · rintro ⟨hg, hfix⟩
    refine ⟨hg, ?_⟩
    intro u hu
    exact Subtype.ext (hfix u (fun a => congrArg Subtype.val (hu a)))
  · rintro ⟨hg, hfix⟩
    refine ⟨hg, ?_⟩
    intro v hv
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.mp (show v ∈ U.toSubmodule ⊔ ρ.invariants by rw [hsum]; trivial)
    have huA : (⟨u, hu⟩ : U) ∈ fixedSpace U.toRepresentation A := by
      intro a
      apply Subtype.ext
      have hh := hv a
      change ρ a (u + c) = u + c at hh
      rw [map_add, hc a] at hh
      exact add_right_cancel hh
    have hgu : ρ g u = u := congrArg Subtype.val (hfix ⟨u, hu⟩ huA)
    rw [map_add, hgu, hc g]

/-- Lift the concrete parabolic conclusion through an actual fixed supplement. -/
theorem sylowFixedCentralizer_of_fixed_supplement [Finite G]
    [FiniteDimensional (ZMod 2) V]
    (U : Subrepresentation ρ) (hsum : U.toSubmodule ⊔ ρ.invariants = ⊤)
    (L : Subgroup G) (d : ℕ) (T : Sylow 2 G)
    (h : SylowFixedCentralizer U.toRepresentation L d T) :
    Nonempty (SylowFixedCentralizer ρ L d T) := by
  have he := fixedCentralizer_eq_of_fixed_supplement ρ U hsum T L
  let c := MulEquiv.subgroupCongr he
  let ec := (c.subgroupMap (pCore 2 _)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 c))
  refine ⟨{ extraspecial := h.extraspecial.of_mulEquiv ec.symm
            core_order := (Nat.card_congr ec.toEquiv).trans h.core_order
            quotientEquiv := ?_, no_offenders := ?_ }⟩
  · exact (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr he)
      (pCore_map_iso 2 _)).trans h.quotientEquiv
  · intro A hA hle
    have hAo : IsOffender U.toRepresentation A :=
      ⟨hA.1, (fixedCodim_subrepresentation_le ρ U A).trans (hA.isOffender ρ).2⟩
    obtain ⟨B, hBA, hB⟩ := hAo.exists_bestOffender U.toRepresentation
    apply h.no_offenders B hB
    rw [fixedCentralizer_eq_of_fixed_supplement ρ U hsum T ⊤] at hle
    exact hBA.trans hle

end CFSG.Quasithin.ChapterB.QuasisimpleSource
