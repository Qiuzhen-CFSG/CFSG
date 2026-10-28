module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.Component
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.Products
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# Completing the marked root-five witness

The dihedral factor has order ten, so every cubic subgroup of the normalizer
lies in its A₅ factor. A single member of the prescribed seed orbit generates
that factor under its own conjugations, by simplicity. Inside the centralizer
of the marked inverter, this simple subgroup meets the normal extraspecial
core trivially; their orders multiply to the full centralizer order.

These deductions leave only the marked product construction as an intermediate
premise. Source: Aschbacher, *Sporadic Groups* (1994), 47.2(2), p.261.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem centralizer_map_equiv (e : G ≃* G) (t : G) :
    (involutionCentralizer t).map e.toMonoidHom = involutionCentralizer (e t) := by
  apply le_antisymm
  · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
      map_centralizer_le_centralizer_image ({t} : Set G) e.toMonoidHom
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hx

private theorem centralizer_core_cards {D : Seed G} {u : G} (hu : IsConj D.z u) :
    Nat.card (involutionCentralizer u) = 1920 ∧ Nat.card (localCore u) = 32 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hu
  let e := MulAut.conj g
  let c : involutionCentralizer D.z ≃* involutionCentralizer (e D.z) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (centralizer_map_equiv e D.z))
  refine ⟨(Nat.card_congr c.symm.toEquiv).trans D.localType.centralizer_card, ?_⟩
  change Nat.card (generalizedFitting (involutionCentralizer (e D.z))) = 32
  rw [← map_generalizedFitting_equiv c, card_map_of_injective c.injective]
  exact D.localType.core_card

namespace ProductData
variable {D : Seed G} {E : Subgroup G} (W : ProductData D E)

include W in
/-- The intrinsic component is an actual subgroup of the normalizer. -/
theorem component_le_normalizer : fiveComponent E ≤ normalizer (E : Set G) := by
  rw [← W.component_factor]
  rintro _ ⟨a, _, rfl⟩
  exact (W.equiv.symm a).property

include W in
/-- Simplicity turns one prescribed cubic vertex into the exact source generation
statement; the orbit throughout is the orbit of the original `D.X`. -/
theorem generation (hE : Nat.card E = 5)
    (e : Quotient E ≃* alternatingGroup (Fin 5))
    (A : Subgroup G) (hAo : A ∈ MulAction.orbit (ConjAct G) D.X)
    (hAN : A ≤ normalizer (E : Set G)) : fiveComponent E = orbitGenerated D E := by
  let L := fiveComponent E
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup L := (fiveComponent_equiv E hE e).some.isSimpleGroup
  have hAc : Nat.card A = 3 := D.vertex_card ⟨A, hAo⟩
  have hAL : A ≤ L := W.three_le_component A hAc hAN
  have hoL : orbitGenerated D E ≤ L := by
    apply sSup_le
    intro B hB
    exact W.three_le_component B (D.vertex_card ⟨B, hB.1⟩) hB.2
  let K : Subgroup L := normalClosure (A.subgroupOf L : Set L)
  have hKtop : K = ⊤ := by
    rcases (inferInstance : K.Normal).eq_bot_or_eq_top with hb | ht
    · have hbA : A.subgroupOf L = ⊥ := bot_unique (by
        have hh := le_normalClosure (H := A.subgroupOf L)
        exact hb ▸ hh)
      have hc : Nat.card (A.subgroupOf L) = 3 :=
        (Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv).trans hAc
      rw [hbA, card_bot] at hc
      omega
    · exact ht
  have hm : K.map L.subtype ≤ orbitGenerated D E := by
    apply map_le_iff_le_comap.mpr
    change closure (Group.conjugatesOfSet (A.subgroupOf L : Set L)) ≤ _
    rw [closure_le]
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hax
    have hgo : ConjAct.toConjAct (g : G) • A ∈ MulAction.orbit (ConjAct G) D.X :=
      MulAction.mem_orbit_of_mem_orbit _ hAo
    have hgn : ConjAct.toConjAct (g : G) • A ≤ normalizer (E : Set G) :=
      conj_smul_le_of_le hAN (⟨g, W.component_le_normalizer g.property⟩ : normalizer (E : Set G))
    exact (le_sSup (s := {B : Subgroup G | B ∈ MulAction.orbit (ConjAct G) D.X ∧
      B ≤ normalizer (E : Set G)}) ⟨hgo, hgn⟩)
        (mem_map_of_mem (MulAut.conj (g : G)).toMonoidHom ha)
  apply le_antisymm _ hoL
  simpa only [hKtop, ← MonoidHom.range_eq_map, range_subtype] using hm

/-- The component is an actual internal complement to the specified ambient
extraspecial core in the inverter's full centralizer. -/
theorem complement (hE : Nat.card E = 5)
    (e : Quotient E ≃* alternatingGroup (Fin 5)) :
    ((fiveComponent E).subgroupOf (involutionCentralizer W.inverter)).IsComplement'
      ((ambientCore W.inverter).subgroupOf (involutionCentralizer W.inverter)) := by
  let H := involutionCentralizer W.inverter
  let B := (fiveComponent E).subgroupOf H
  let K := localCore W.inverter
  obtain ⟨hH, hK⟩ := centralizer_core_cards W.inverter_conj
  have hB : Nat.card B = 60 :=
    (Nat.card_congr (subgroupOfEquivOfLe W.component_le).toEquiv).trans
      (fiveComponent_card E hE e)
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (fiveComponent E) := (fiveComponent_equiv E hE e).some.isSimpleGroup
  let : IsSimpleGroup B := (subgroupOfEquivOfLe W.component_le).isSimpleGroup
  have hd : Disjoint B K := by
    rcases (inferInstance : (K.subgroupOf B).Normal).eq_bot_or_eq_top with hb | ht
    · rw [disjoint_def]
      intro x hxB hxK
      have hx : (⟨x, hxB⟩ : B) ∈ K.subgroupOf B := hxK
      rw [hb, mem_bot] at hx
      exact congrArg Subtype.val hx
    · have hd := card_dvd_of_le (subgroupOf_eq_top.mp ht)
      rw [hB, hK] at hd
      norm_num at hd
  rw [ambientCore_subgroupOf]
  exact isComplement'_of_card_mul_and_disjoint (by rw [hB, hK, hH]) hd

/-- All remaining fields of the source witness follow from the marked product,
recognized quotient and one member of the original seed orbit. -/
noncomputable def toRootFiveWitness (hE : Nat.card E = 5)
    (e : Quotient E ≃* alternatingGroup (Fin 5))
    (A : Subgroup G) (hAo : A ∈ MulAction.orbit (ConjAct G) D.X)
    (hAN : A ≤ normalizer (E : Set G)) : RootFiveWitness D E where
  equiv := W.equiv
  component_factor := W.component_factor
  generation := W.generation hE e A hAo hAN
  inverter := W.inverter
  inverter_conj := W.inverter_conj
  inverts := W.inverts
  dihedral_factor := W.dihedral_factor
  component_le := W.component_le
  complement := W.complement hE e

end ProductData
/-- Every root-five normalizer contains a conjugate of the fixed selected seed.
The transport uses Sylow conjugacy in the marked centralizer, not a new seed. -/
theorem exists_vertex_in_normalizer {D : Seed G}
    (S : InvolutionGeometry.SelectedGeometry D) (E : Subgroup G)
    (hE : FiveCentralizing S.t E) :
    ∃ A : Subgroup G, A ∈ MulAction.orbit (ConjAct G) D.X ∧ A ≤ normalizer (E : Set G) := by
  have ht : 5 ^ (Nat.card (involutionCentralizer S.t)).factorization 5 = 5 := by
    rw [S.model.centralizer_card]
    decide +kernel
  obtain ⟨F, hF, hFt⟩ := exists_fiveCentralizing S.t ht
  obtain ⟨g, rfl⟩ := (fiveCentralizing_iff_mem_orbit S.t ht F hF hFt E).mp hE
  refine ⟨g • D.X, MulAction.mem_orbit _ _, ?_⟩
  have hFN : D.X ≤ normalizer (F : Set G) :=
    (seed_le_centralizer S F hF hFt).trans (centralizer_le_normalizer (F : Set G))
  change D.X.map (MulAut.conj (ConjAct.ofConjAct g)).toMonoidHom ≤
    normalizer (F.map (MulAut.conj (ConjAct.ofConjAct g)).toMonoidHom : Set G)
  rw [← map_equiv_normalizer_eq]
  exact map_mono hFN

/-- Assembly of the source root-five family from its still-explicit marked
product step. The parent must construct this step, as well as the quotients. -/
theorem rootFiveFamily_of_products {D : Seed G}
    (S : InvolutionGeometry.SelectedGeometry D)
    (Q : ∀ E : Subgroup G, FiveCentralizing S.t E →
      Nonempty (Quotient E ≃* alternatingGroup (Fin 5)))
    (P : ∀ E : Subgroup G, FiveCentralizing S.t E → Nonempty (ProductData D E)) :
    RootFiveFamily D S.t := by
  intro E hE
  obtain ⟨e⟩ := Q E hE
  obtain ⟨W⟩ := P E hE
  obtain ⟨A, hAo, hAN⟩ := exists_vertex_in_normalizer S E hE
  exact ⟨W.toRootFiveWitness hE.1 e A hAo hAN⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer
