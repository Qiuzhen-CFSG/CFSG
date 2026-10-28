module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.Configurations
public import Theory.GroupTheory.Commutator.NilpotentSaturation

/-!
# The core inside the marked parabolic

The source center containment V₂ ≤ Z(Q) puts Q inside N_L(V₂) = M ∩ L.
Characteristicity of O^{3′}(M ∩ L) then puts [Q,Y₊] in O₂(Y₊).
For an actual binary section model, generation of its coinvariants lifts to
Q = [Q,Y₊] Z(Q). If Z(Q) lies in [Q,Q], nilpotence removes this supplement.
The model calculations supplying these premises are separate from this
reduction; generation only on Q/Z(Q) is not asserted to suffice by itself.

Source: Aschbacher–Smith, proof of 15.3.31, printed p.1132 (PDF p.1149).
-/

@[expose] public section

open Subgroup Representation
open scoped commutatorElement
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
open CentralCover
namespace ContainedCoreModels

variable {G : Type*} [Group G]

/-- The actual commutator core is a two-subgroup of the component. -/
theorem core_le_core (L : Subgroup G) : extensionCore L ≤ L.pCoreIn 2 :=
  le_normalizer_iff_commutator_le_left.mp
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))

/-- Centrality of the source V₂ forces containment in its relative normalizer. -/
theorem core_le_parabolic [Finite G] {κ : GroupClass} {d : LocalData G}
    {I : Subgroup G} {c : ComponentWitness d I} (s : SourceData κ d c) :
    extensionCore c.L ≤ d.M ⊓ c.L := by
  rw [s.component_parabolic]
  refine le_inf ((core_le_core c.L).trans (pCoreIn_le 2 c.L)) ?_
  exact ((le_centralizer_iff.mp (s.plane_le_coreCenter.trans inf_le_right))).trans
    (Subgroup.centralizer_le_normalizer _)

/-- Characteristicity of the source residual gives the required normalization. -/
theorem core_normalizes_yplus [Finite G] {κ : GroupClass} {d : LocalData G}
    {I : Subgroup G} {c : ComponentWitness d I} (s : SourceData κ d c) :
    extensionCore c.L ≤ normalizer (d.Yplus : Set G) := by
  rw [s.component_residual]
  exact (core_le_parabolic s).trans ((d.M ⊓ c.L).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (d.M ⊓ c.L)
      (primeToResidual 3 (d.M ⊓ c.L : Subgroup G))))

/-- The entire core commutator, before any model calculation, lies in O₂(Y₊). -/
theorem core_commutator_le_yplus_core [Finite G] {κ : GroupClass} {d : LocalData G}
    {I : Subgroup G} {c : ComponentWitness d I} (s : SourceData κ d c) :
    ⁅extensionCore c.L, d.Yplus⁆ ≤ d.Yplus.pCoreIn 2 := by
  apply le_pCoreIn_of_normalizes
  · exact (isPGroup_pCoreIn 2 c.L).to_le
      ((le_normalizer_iff_commutator_le_left.mp
        (s.contains.trans (normalizes_extensionCore c.L.le_normalizer))).trans
          (core_le_core c.L))
  · exact le_normalizer_iff_commutator_le_right.mp (core_normalizes_yplus s)
  · exact normalizer_commutator_ge_right _ _

/-- Full marked coinvariants on the literal section give generation modulo its kernel. -/
theorem section_le_sup_commutator
    {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    {L Q Z Y : Subgroup G} {actor : L →* A} {ρ : Representation (ZMod 2) A V}
    (h : HasSectionModel L Q Z actor ρ)
    (hgen : Coinvariants.ker (ρ.comp ((Y.subgroupOf L).map actor).subtype) = ⊤) :
    Q ≤ ⁅Q,Y⁆ ⊔ Z := by
  obtain ⟨_, hLQ, _, hn, e, he⟩ := h
  let := hn
  let f : Q →* Multiplicative V := e.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf Q))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let N : Subgroup (Multiplicative V) := (⁅Q,Y⁆.subgroupOf Q).map f
  let U : Submodule (ZMod 2) V := AddSubgroup.toZModSubmodule 2 (AddSubgroup.toSubgroup.symm N)
  have hspan : Coinvariants.ker (ρ.comp ((Y.subgroupOf L).map actor).subtype) ≤ U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩, rfl⟩
    obtain ⟨l,hl,hal⟩ := a.property
    obtain ⟨q,hq⟩ := hf (Multiplicative.ofAdd v)
    let q' : Q := ⟨(l : G) * (q : G) * (l : G)⁻¹,
      ((mem_normalizer_iff.mp (hLQ l.property)) q).mp q.property⟩
    change Multiplicative.ofAdd (ρ a.val v - v) ∈ N
    refine mem_map.mpr ⟨q' * q⁻¹, ?_, ?_⟩
    · change (l : G) * (q : G) * (l : G)⁻¹ * (q : G)⁻¹ ∈ ⁅Q,Y⁆
      rw [commutator_comm Q Y]
      exact commutator_mem_commutator hl q.property
    · rw [map_mul, map_inv]
      have hq' : f q' = Multiplicative.ofAdd (ρ (actor l) v) := by
        have hh := he l q q' rfl
        change (f q').toAdd = ρ (actor l) (f q).toAdd at hh
        rw [hq] at hh
        exact congrArg Multiplicative.ofAdd hh
      rw [hq', hq, hal]
      exact congrArg Multiplicative.ofAdd (sub_eq_add_neg _ _).symm
  have hN : N = ⊤ := by
    apply top_unique
    intro v _
    exact hspan (hgen ▸ (show v.toAdd ∈ (⊤ : Submodule (ZMod 2) V) from trivial))
  intro q hq
  obtain ⟨n,hn,hfn⟩ := (show f ⟨q,hq⟩ ∈ N from hN ▸ mem_top _)
  have hz : q * (n : G)⁻¹ ∈ Z := by
    have hk : f ((⟨q,hq⟩ : Q) * n⁻¹) = 1 := by
      rw [map_mul, map_inv, hfn, mul_inv_cancel]
    have hk' : QuotientGroup.mk' (Z.subgroupOf Q) ((⟨q,hq⟩ : Q) * n⁻¹) = 1 :=
      e.injective (hk.trans e.map_one.symm)
    exact (QuotientGroup.eq_one_iff ((⟨q,hq⟩ : Q) * n⁻¹)).mp hk'
  have hh := (⁅Q,Y⁆ ⊔ Z).mul_mem (mem_sup_right hz) (mem_sup_left hn)
  change q * (n : G)⁻¹ * (n : G) ∈ ⁅Q,Y⁆ ⊔ Z at hh
  simpa only [inv_mul_cancel_right] using hh

/-- Nilpotence lifts section generation when the central kernel lies in the derived group. -/
theorem core_eq_commutator_of_section [Finite G]
    {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    {κ : GroupClass} {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
    (s : SourceData κ d c) {actor : c.L →* A} {ρ : Representation (ZMod 2) A V}
    (h : HasSectionModel c.L (extensionCore c.L) (coreCenter c.L) actor ρ)
    (hZ : coreCenter c.L ≤ ⁅extensionCore c.L, extensionCore c.L⁆)
    (hgen : Coinvariants.ker
      (ρ.comp ((d.Yplus.subgroupOf c.L).map actor).subtype) = ⊤) :
    extensionCore c.L = ⁅extensionCore c.L, d.Yplus⁆ := by
  have hN : ⁅extensionCore c.L, d.Yplus⁆ ≤ extensionCore c.L :=
    le_normalizer_iff_commutator_le_left.mp
      (s.contains.trans (normalizes_extensionCore c.L.le_normalizer))
  apply le_antisymm _ hN
  have hp := (isPGroup_pCoreIn 2 c.L).to_le (core_le_core c.L)
  apply le_of_le_sup_commutator_of_isPGroup (extensionCore c.L)
    ⁅extensionCore c.L,d.Yplus⁆ (extensionCore c.L) hp hp hN
    (extensionCore c.L).le_normalizer (normalizer_commutator_ge_left _ _)
  exact (section_le_sup_commutator h hgen).trans (sup_le_sup_left hZ _)

end ContainedCoreModels
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
