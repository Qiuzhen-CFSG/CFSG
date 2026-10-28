module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SwappingFixedRank.Basic
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.ParabolicWings
public import Theory.Representation.SymplecticConjugatePair.Ambient.Transport
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvariantLocalPair
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction.Graph
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction.Transport
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.CenterAction

/-!
# Central placement for swapping Sylow involutions

A diagram-moving automorphism carries each fixed square-one element of an arbitrary
symplectic Sylow into the embedded Sylow center. The proof aligns the Sylow with
the standard unipotent group, uses the inner-field-graph normal form, and transports
the two standard radical planes through the graph swap.

Source: Aschbacher--Smith E.1.14(1), printed p.214, with the Sp₄ root geometry
of H.7, printed pp.209--214.
-/

@[expose] public section
open Subgroup
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SwappingFixedRank
set_option linter.style.haveILetI false
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

omit [CharP F 2] [Finite F] in
private theorem map_embedded_core {P : Subgroup (Sp F)} (τ : MulAut (Sp F)) :
    ((pCore 2 P).map P.subtype).map τ.toMonoidHom =
      (pCore 2 (P.map τ.toMonoidHom)).map (P.map τ.toMonoidHom).subtype := by
  let e := P.equivMapOfInjective τ.toMonoidHom τ.injective
  rw [← pCore_map_iso 2 e, Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem field_point {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (σ : F ≃+* F) :
    (Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient (F := F)).map
      (fieldAutomorphism σ).toMonoidHom =
      Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient := by
  rw [show Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient =
      (pCore 2 pointParabolic).map pointParabolic.subtype from
      (pointParabolic_core_map_eq_radical hF hn).symm]
  rw [map_embedded_core]
  rw [field_map_pointParabolic]

private theorem graph_point {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    (Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient (F := F)).map
      graphAut.toMonoidHom =
      Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient := by
  rw [show Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient =
      (pCore 2 pointParabolic).map pointParabolic.subtype from
      (pointParabolic_core_map_eq_radical hF hn).symm]
  rw [map_embedded_core]
  rw [graphAut_map_point]
  exact planeParabolic_core_map_eq_radical hF hn

private theorem graph_plane {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    (Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient (F := F)).map
      graphAut.toMonoidHom =
      Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient := by
  rw [show Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient =
      (pCore 2 planeParabolic).map planeParabolic.subtype from
      (planeParabolic_core_map_eq_radical hF hn).symm]
  rw [map_embedded_core]
  rw [graphAut_map_plane]
  exact pointParabolic_core_map_eq_radical hF hn

private theorem field_plane {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (σ : F ≃+* F) :
    (Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient (F := F)).map
      (fieldAutomorphism σ).toMonoidHom =
      Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient := by
  rw [show Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient =
      (pCore 2 planeParabolic).map planeParabolic.subtype from
      (planeParabolic_core_map_eq_radical hF hn).symm]
  rw [map_embedded_core]
  rw [field_map_planeParabolic]

private theorem conj_point {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    {g : Sp F} (hg : g ∈ borel) :
    (Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient (F := F)).map
      (MulAut.conj g).toMonoidHom =
      Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient := by
  apply mem_normalizer_iff_map_conj_eq.mp
  rw [pointRadicalAmbient_normalizer hF hn]
  exact (show g ∈ pointParabolic from hg.1)

private theorem conj_plane {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    {g : Sp F} (hg : g ∈ borel) :
    (Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient (F := F)).map
      (MulAut.conj g).toMonoidHom =
      Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient := by
  apply mem_normalizer_iff_map_conj_eq.mp
  rw [planeRadicalAmbient_normalizer hF hn]
  exact (show g ∈ planeParabolic from hg.2)

private theorem standard_wing_mem {f : ℕ} (_hF : Nat.card F = 2 ^ f) (_hf : 1 < f)
    {u : Sp F} (hu : u ∈ unipotent) (hu2 : u ^ 2 = 1) :
    u ∈ Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient ∨
      u ∈ Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let x : unipotent (F := F) := ⟨u, hu⟩
  obtain hx | hx := SymplecticConjugatePair.square_one_mem_wing x (by
    exact Subtype.ext hu2)
  · left
    change u ∈ SymplecticConjugatePair.pointRadical
    rw [SymplecticConjugatePair.pointRadical_eq_wing]
    exact ⟨x, hx, rfl⟩
  · right
    change u ∈ SymplecticConjugatePair.planeRadical
    rw [SymplecticConjugatePair.planeRadical_eq_wing]
    exact ⟨x, hx, rfl⟩

private theorem standard_fixed {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (a : MulAut (Sp F)) (hU : unipotent.map a.toMonoidHom = unipotent)
    (ha : ¬ PreservesDiagram a) {u : Sp F} (hu : u ∈ unipotent)
    (hu2 : u ^ 2 = 1) (hfix : a u = u) :
    u ∈ (center (unipotent (F := F))).map (unipotent (F := F)).subtype := by
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨g, σ, hnorm⟩ := SymplecticConjugatePair.Ambient.moving_eq_inner_field_graph a ha
  let φ : MulAut (Sp F) := fieldAutomorphism σ * graphAut
  have hfieldU : unipotent.map (fieldAutomorphism σ).toMonoidHom = unipotent := by
    rw [unipotent, map_inf _ _ _ (fieldAutomorphism σ).injective,
      pointLocal_map hF hf (fieldAutomorphism σ) (field_map_pointParabolic σ),
      planeLocal_map hF hf (fieldAutomorphism σ) (field_map_planeParabolic σ)]
  have hphiU : unipotent.map φ.toMonoidHom = unipotent := by
    change unipotent.map ((fieldAutomorphism σ).toMonoidHom.comp graphAut.toMonoidHom) = unipotent
    rw [← Subgroup.map_map]
    rw [Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.graph_map_unipotent, hfieldU]
  have hdecomp : MulAut.conj g * φ = a := by
    simpa [φ, mul_assoc] using hnorm.symm
  have hcomp : (MulAut.conj g * φ).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp φ.toMonoidHom := by
    ext x
    rfl
  have hconjU : unipotent.map (MulAut.conj g).toMonoidHom = unipotent := by
    calc
      _ = (unipotent.map φ.toMonoidHom).map (MulAut.conj g).toMonoidHom := by rw [hphiU]
      _ = unipotent.map (MulAut.conj g * φ).toMonoidHom := by
        rw [hcomp, ← Subgroup.map_map]
      _ = unipotent := by rw [hdecomp, hU]
  have hgB : g ∈ borel := by
    rw [borel_eq_normalizer_unipotent, mem_normalizer_iff_map_conj_eq]
    exact hconjU
  have hfix' : ((MulAut.conj g * fieldAutomorphism σ * graphAut : MulAut (Sp F)) u) = u := by
    rw [← hnorm]
    exact hfix
  obtain hpr | hqr := standard_wing_mem hF hf hu hu2
  · have h1 : graphAut u ∈ Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient := by
      rw [← graph_point hF hf]
      exact ⟨u, hpr, rfl⟩
    have h2 : fieldAutomorphism σ (graphAut u) ∈
        Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient := by
      rw [← field_plane hF hf σ]
      exact ⟨graphAut u, h1, rfl⟩
    have h3 : (MulAut.conj g) (fieldAutomorphism σ (graphAut u)) ∈
        Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient := by
      rw [← conj_plane hF hf hgB]
      exact ⟨fieldAutomorphism σ (graphAut u), h2, rfl⟩
    have hq : u ∈ Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient := by
      change ((MulAut.conj g * fieldAutomorphism σ * graphAut : MulAut (Sp F)) u) ∈
        Theory.SpecificGroups.SymplecticFour.planeRadicalAmbient at h3
      rw [hfix'] at h3
      exact h3
    have hs : u ∈ SymplecticConjugatePair.sylowCenter := by
      rw [SymplecticConjugatePair.sylowCenter_eq_radical_inf]
      exact ⟨hpr, hq⟩
    simpa only [SymplecticConjugatePair.sylowCenter] using hs
  · have h1 : graphAut u ∈ Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient := by
      rw [← graph_plane hF hf]
      exact ⟨u, hqr, rfl⟩
    have h2 : fieldAutomorphism σ (graphAut u) ∈
        Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient := by
      rw [← field_point hF hf σ]
      exact ⟨graphAut u, h1, rfl⟩
    have h3 : (MulAut.conj g) (fieldAutomorphism σ (graphAut u)) ∈
        Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient := by
      rw [← conj_point hF hf hgB]
      exact ⟨fieldAutomorphism σ (graphAut u), h2, rfl⟩
    have hp : u ∈ Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient := by
      change ((MulAut.conj g * fieldAutomorphism σ * graphAut : MulAut (Sp F)) u) ∈
        Theory.SpecificGroups.SymplecticFour.pointRadicalAmbient at h3
      rw [hfix'] at h3
      exact h3
    have hs : u ∈ SymplecticConjugatePair.sylowCenter := by
      rw [SymplecticConjugatePair.sylowCenter_eq_radical_inf]
      exact ⟨hp, hqr⟩
    simpa only [SymplecticConjugatePair.sylowCenter] using hs

private theorem subgroup_map_aut_mul {G : Type*} [Group G] (P : Subgroup G)
    (a b : MulAut G) :
    P.map (a * b).toMonoidHom = (P.map b.toMonoidHom).map a.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem subgroup_map_conj_aut {G : Type*} [Group G] (P : Subgroup G)
    (a : MulAut G) (x : G) :
    (P.map (MulAut.conj x).toMonoidHom).map a.toMonoidHom =
      (P.map a.toMonoidHom).map (MulAut.conj (a x)).toMonoidHom := by
  simp only [Subgroup.map_map]
  congr 1
  ext y
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

omit [CharP F 2] [Finite F] in
private theorem preservesParabolicClass_mul (a b : MulAut (Sp F)) (P : Subgroup (Sp F))
    (ha : PreservesParabolicClass a P) (hb : PreservesParabolicClass b P) :
    PreservesParabolicClass (a * b) P := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  refine ⟨a y * x, ?_⟩
  rw [subgroup_map_aut_mul, hy, subgroup_map_conj_aut, hx,
    ← subgroup_map_aut_mul, ← map_mul]

omit [CharP F 2] [Finite F] in
private theorem preservesDiagram_mul (a b : MulAut (Sp F))
    (ha : PreservesDiagram a) (hb : PreservesDiagram b) : PreservesDiagram (a * b) :=
  ⟨preservesParabolicClass_mul a b _ ha.1 hb.1,
    preservesParabolicClass_mul a b _ ha.2 hb.2⟩

theorem central_placement {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (S : Sylow 2 (Sp F)) (a : MulAut (Sp F))
    (hS : (S : Subgroup (Sp F)).map a.toMonoidHom = S)
    (ha : ¬ PreservesDiagram a) {u : Sp F} (hu : u ∈ S)
    (hu2 : u ^ 2 = 1) (hfix : a u = u) :
    u ∈ (center (S : Subgroup (Sp F))).map (S : Subgroup (Sp F)).subtype := by
  let e : MulAut (Sp F) :=
    Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction.alignment hF hf.le S
  have hUS : unipotent.map e.toMonoidHom = (S : Subgroup (Sp F)) := by
    exact Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction.alignment_unipotent
      hF hf.le S
  let b : MulAut (Sp F) := MulAut.congr e.symm a
  have hbU : unipotent.map b.toMonoidHom = unipotent := by
    exact Theory.GroupAction.OddCommutatorImage.congr_symm_stabilizes e a unipotent S hUS hS
  have he : PreservesDiagram e := by
    dsimp [e, Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction.alignment]
    exact inner_preservesDiagram _
  have hes : PreservesDiagram e.symm := by
    have heq : e = MulAut.conj (Classical.choose
        (Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.residualAt_conjugate
          hF hf.le S)) := by
      rfl
    rw [heq]
    have hi : (MulAut.conj (Classical.choose
        (Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.residualAt_conjugate
          hF hf.le S))).symm = MulAut.conj (Classical.choose
        (Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.residualAt_conjugate
          hF hf.le S))⁻¹ := by
      ext x
      simp
    rw [hi]
    exact inner_preservesDiagram _
  have hconj : e * b * e.symm = a := by
    ext x
    simp [b, MulAut.congr_apply, mul_assoc]
  have hb : ¬ PreservesDiagram b := by
    intro hb
    have h' := preservesDiagram_mul e b he hb
    have h'' := preservesDiagram_mul (e * b) e.symm h' hes
    rw [hconj] at h''
    exact ha h''
  let v : Sp F := e.symm u
  have hv : v ∈ unipotent := by
    apply (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp
    rw [hUS]
    change e (e.symm u) ∈ (S : Subgroup (Sp F))
    rw [e.apply_symm_apply]
    exact hu
  have hv2 : v ^ 2 = 1 := by
    simpa [v] using congrArg (fun z : Sp F => e.symm z) hu2
  have hvfix : b v = v := by
    have h := congrArg (fun z : Sp F => e.symm z) hfix
    simpa [b, v, MulAut.congr_apply] using h
  have hvc := standard_fixed hF hf b hbU hb hv hv2 hvfix
  have hcm := Subgroup.map_subgroup_center_eq e.toMonoidHom e.injective unipotent
  have hu' : u ∈ ((center (unipotent (F := F))).map unipotent.subtype).map e.toMonoidHom := by
    refine ⟨v, hvc, ?_⟩
    simp [v]
  rw [hcm, hUS] at hu'
  exact hu'

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SwappingFixedRank
