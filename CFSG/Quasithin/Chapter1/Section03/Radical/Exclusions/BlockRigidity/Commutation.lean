module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.SourceContracts
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ResidualFactors
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport

/-!
# Commutation of the actual conjugate blocks in 1.3.8

For a binary block embedding and t ∈ T outside N_G(K), conjugation by t
inside H₀ preserves the complete short-group structure and subnormality of K.
The two internal blocks are distinct, since equality would put t in N_G(K).
The genuine global He bridge supplies the O₂,₃ fitting condition, so the full
C.1.9 theorem parameter applies. Mapping through H₀'s inclusion gives
[K,Kᵗ] = 1 in G. The subgroup T need not itself be supplied as a Sylow object.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, C.1.7–9,
printed p.123, and proof of 1.3.8, printed p.514. C.1.9 remains an explicit
earlier-source input; no conjugate-block or commutation premise is added.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.BlockRigidity

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Apply the full C.1.9 parameter inside H₀ to K and its actual moving conjugate.
The He bridge discharges the A₃ fitting premise, even when an A₃-block is present. -/
theorem conjugate_commute (h19 : SourceC19.{u})
    {p : ℕ} {T X P H₀ K : Subgroup G} (h : BinaryBlockEmbedding p T X P H₀ K)
    (h114 : HOver G (T : Set G) ⊆ He G) (hH : H₀ ∈ HOver G (T : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer K) : ⁅K, K.conjBy t⁆ = ⊥ := by
  let t₀ : H₀ := ⟨t, h.local_input.overgroup (mem_sup_right ht)⟩
  have hKmap : (K.subgroupOf H₀).map H₀.subtype = K :=
    map_subgroupOf_eq_of_le h.component.1
  have hKtmap : ((K.subgroupOf H₀).conjBy t₀).map H₀.subtype = K.conjBy t := by
    unfold Subgroup.conjBy
    rw [map_map]
    have hcomp : H₀.subtype.comp (MulAut.conj t₀).toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp H₀.subtype := by
      ext a
      rfl
    rw [hcomp, ← map_map, hKmap]
  have hKtblock : IsBlock ((K.subgroupOf H₀).conjBy t₀) :=
    h.block.map_equiv (MulAut.conj t₀)
  have hne : K.subgroupOf H₀ ≠ (K.subgroupOf H₀).conjBy t₀ := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hm := congrArg (Subgroup.map H₀.subtype) he
    rw [hKmap, hKtmap] at hm
    exact hm.symm
  have hc := h19 H₀ (fun _ => twoThreeCore_fitting_of_global_He h114 hH)
    (K.subgroupOf H₀) ((K.subgroupOf H₀).conjBy t₀) h.block hKtblock hne
  have hm := congrArg (Subgroup.map H₀.subtype) hc
  rwa [map_commutator, hKmap, hKtmap, Subgroup.map_bot] at hm

end CFSG.Quasithin.Chapter1.RadicalExclusions.BlockRigidity
