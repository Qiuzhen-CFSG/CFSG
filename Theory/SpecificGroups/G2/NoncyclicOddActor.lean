module
public import Theory.AtlasPort.LinearGroups.G2.OddSubgroupPlacement
public import Theory.AtlasPort.LinearGroups.G2.EvenBorelTorus
public import Theory.SpecificGroups.G2.SolvableSylowNormalizer
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.SylowNormalizerOvergroup
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.PCoreFromTwoNormalizers

/-!
# The unipotent core forced by a noncyclic odd actor in G₂

Each positive root character of the split torus has cyclic kernel. A noncyclic
odd-primary actor therefore moves every positive root group. Scalar commutators,
after Borel conjugacy, put the full unipotent Sylow in the normalized subgroup.
Solvable Sylow control identifies its actual two-core, and the abelian torus
quotient bounds the commutators of its normalizer.

The source application is Aschbacher–Smith, 13.1.12(3), printed pp.874–875,
in Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.
CharacteristicTwo.G2. Root groups and torus identities are supplied by the
licensed ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Atlas.G2.NoncyclicOddActor
open LieParabolicSetup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private def root (i : Fin 6) (t : F) : Model F :=
  ![rootA t,rootB t,rootC t,rootD t,rootE t,rootF t] i
private def weight (i : Fin 6) (a : Fˣ × Fˣ) : Fˣ :=
  ![a.1*a.2,a.1^2/a.2,a.1,a.2,a.2^2/a.1,a.1/a.2] i

omit [CharP F 2] in
private theorem weight_moves (B : Subgroup (Fˣ × Fˣ)) (hnc : ¬ IsCyclic B)
    (i : Fin 6) : ∃ a ∈ B, weight i a ≠ 1 := by
  by_contra! h
  have first (he : ∀ a : B, a.val.1 = 1) : False := by
    apply hnc
    apply isCyclic_of_injective ((MonoidHom.snd Fˣ Fˣ).comp B.subtype)
    intro a b hab
    exact Subtype.ext (Prod.ext ((he a).trans (he b).symm) hab)
  have second (he : ∀ a : B, a.val.2 = 1) : False := by
    apply hnc
    apply isCyclic_of_injective ((MonoidHom.fst Fˣ Fˣ).comp B.subtype)
    intro a b hab
    exact Subtype.ext (Prod.ext hab ((he a).trans (he b).symm))
  fin_cases i
  · apply hnc
    apply isCyclic_of_injective ((MonoidHom.fst Fˣ Fˣ).comp B.subtype)
    intro a b hab
    apply Subtype.ext
    apply Prod.ext hab
    have ha : a.val.1 * a.val.2 = 1 := h a a.property
    have hb : b.val.1 * b.val.2 = 1 := h b b.property
    exact mul_left_cancel ((congrArg (fun t => t*a.val.2) hab).symm.trans (ha.trans hb.symm))
  · apply hnc
    apply isCyclic_of_injective ((MonoidHom.fst Fˣ Fˣ).comp B.subtype)
    intro a b hab
    apply Subtype.ext
    apply Prod.ext hab
    have ha : a.val.1^2 = a.val.2 := div_eq_one.mp (h a a.property)
    have hb : b.val.1^2 = b.val.2 := div_eq_one.mp (h b b.property)
    exact ha.symm.trans ((congrArg (fun t => t^2) hab).trans hb)
  · exact first (fun a => h a a.property)
  · exact second (fun a => h a a.property)
  · apply hnc
    apply isCyclic_of_injective ((MonoidHom.snd Fˣ Fˣ).comp B.subtype)
    intro a b hab
    apply Subtype.ext
    apply Prod.ext _ hab
    have ha : a.val.2^2 = a.val.1 := div_eq_one.mp (h a a.property)
    have hb : b.val.2^2 = b.val.1 := div_eq_one.mp (h b b.property)
    exact ha.symm.trans ((congrArg (fun t => t^2) hab).trans hb)
  · apply hnc
    apply isCyclic_of_injective ((MonoidHom.fst Fˣ Fˣ).comp B.subtype)
    intro a b hab
    apply Subtype.ext
    apply Prod.ext hab
    have ha : a.val.1 = a.val.2 := div_eq_one.mp (h a a.property)
    have hb : b.val.1 = b.val.2 := div_eq_one.mp (h b b.property)
    exact ha.symm.trans (hab.trans hb)

omit [Finite F] [CharP F 2] in
private theorem root_add (i : Fin 6) (a b : F) : root i a * root i b = root i (a+b) := by
  fin_cases i <;> dsimp [root]
  all_goals first | exact rootA_add a b | exact rootB_add a b | exact rootC_add a b |
    exact rootD_add a b | exact rootE_add a b | exact rootF_add a b

omit [Finite F] [CharP F 2] in
private theorem root_zero (i : Fin 6) : root i (0 : F) = 1 := by
  fin_cases i <;> simp [root]

omit [Finite F] [CharP F 2] in
private theorem root_mem (i : Fin 6) (a : F) : root i a ∈ unipotent (K := F) := by
  apply Subgroup.subset_closure
  fin_cases i <;> simp [root]

omit [Finite F] [CharP F 2] in
private theorem torus_conjugate (i : Fin 6) (a : Fˣ × Fˣ) (t : F) :
    torusHom a * root i t * (torusHom a)⁻¹ = root i ((weight i a : F)*t) := by
  fin_cases i
  · simpa [root, weight, torusHom] using (torus_rootA a.1 a.2 t)
  · simpa [root, weight, torusHom] using (torus_rootB a.1 a.2 t)
  · simpa [root, weight, torusHom] using (torus_rootC a.1 a.2 t)
  · simpa [root, weight, torusHom] using (torus_rootD a.1 a.2 t)
  · simpa [root, weight, torusHom] using (torus_rootE a.1 a.2 t)
  · simpa [root, weight, torusHom] using (torus_rootF a.1 a.2 t)

omit [Finite F] [CharP F 2] in
private theorem scalar_root_mem (X : Subgroup (Model F)) (i : Fin 6)
    (hn : unipotent (K := F) ≤ normalizer (X : Set (Model F)))
    (a : Fˣ × Fˣ) (ha : torusHom a ∈ X) (hw : weight i a ≠ 1) (t : F) : root i t ∈ X := by
  let c : F := weight i a
  have hc : c ≠ 1 := fun h => hw (Units.ext h)
  let v := t/(c-1)
  have hh := (mem_normalizer_iff.mp (hn (root_mem i v)) (torusHom a)⁻¹).mp (X.inv_mem ha)
  have hmem := X.mul_mem ha hh
  have he : torusHom a * (root i v * (torusHom a)⁻¹ * (root i v)⁻¹) = root i t := by
    rw [← mul_assoc, ← mul_assoc, torus_conjugate]
    have hinv : (root i v)⁻¹ = root i (-v) := by
      apply inv_eq_of_mul_eq_one_right
      rw [root_add, add_neg_cancel, root_zero]
    rw [hinv, root_add]
    congr 1
    change c*v + -v = t
    dsimp [v]
    field_simp [sub_ne_zero.mpr hc]
    ring
  rwa [he] at hmem

omit [CharP F 2] in
/-- A noncyclic split-torus actor forces every positive root into the subgroup. -/
theorem unipotent_le_of_noncyclic_torus (X P : Subgroup (Model F))
    (hPX : P ≤ X) (hPT : P ≤ splitTorus) (hnc : ¬ IsCyclic P)
    (hn : unipotent (K := F) ≤ normalizer (X : Set (Model F))) : unipotent (K := F) ≤ X := by
  let B := P.comap torusHom
  let f : B →* P := (torusHom.comp B.subtype).codRestrict P (fun a => a.property)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a,ha⟩ := hPT x.property
    refine ⟨⟨a,?_⟩,Subtype.ext ha⟩
    change torusHom a ∈ P
    rw [ha]
    exact x.property
  have hB : ¬ IsCyclic B := fun hc => hnc (by
    let := hc
    exact isCyclic_of_surjective f hf)
  have hr (i : Fin 6) (t : F) : root i t ∈ X := by
    obtain ⟨a,ha,hw⟩ := weight_moves B hB i
    exact scalar_root_mem X i hn a (hPX ha) hw t
  apply (closure_le X).mpr
  rintro x (((((hx|hx)|hx)|hx)|hx)|hx)
  all_goals obtain ⟨t,rfl⟩ := hx
  · exact hr 0 t
  · exact hr 1 t
  · exact hr 2 t
  · exact hr 3 t
  · exact hr 4 t
  · exact hr 5 t

/-- Odd-primary Borel conjugacy preserves the actual unipotent Sylow. -/
theorem unipotent_le_of_noncyclic_odd {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (X P : Subgroup (Model F)) (hXB : X ≤ borel) (hPX : P ≤ X)
    (hP : IsPGroup p P) (hnc : ¬ IsCyclic P)
    (hn : unipotent (K := F) ≤ normalizer (X : Set (Model F))) : unipotent (K := F) ≤ X := by
  obtain ⟨g,hg,hgP⟩ := OddSubgroupPlacement.conjugate_borel_pSubgroup_into_torus P hP
    (by intro he; rw [he] at hp; exact (by decide : ¬ Odd 2) hp) (hPX.trans hXB)
  let c := MulAut.conj g
  have hU : (unipotent (K := F)).map c.toMonoidHom = unipotent :=
    mem_normalizer_iff_map_conj_eq.mp ((SylowNormalizer.normalizer_unipotent.symm.le) hg)
  have hn' : unipotent (K := F) ≤ normalizer (X.map c.toMonoidHom : Set (Model F)) := by
    rw [← hU,← map_equiv_normalizer_eq X c]
    exact map_mono hn
  have hc : ¬ IsCyclic (P.map c.toMonoidHom) :=
    fun hc => hnc ((P.equivMapOfInjective c.toMonoidHom c.injective).isCyclic.mpr hc)
  have hle := unipotent_le_of_noncyclic_torus (X.map c.toMonoidHom)
    (P.map c.toMonoidHom) (map_mono hPX) hgP hc hn'
  rw [← hU] at hle
  exact (map_le_map_iff_of_injective c.injective).mp hle

/-- The two-core is the full positive-root Sylow, rather than an assumed marking. -/
theorem twoCore_eq_unipotent {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (X P : Subgroup (Model F)) (hXB : X ≤ borel) (hPX : P ≤ X)
    (hP : IsPGroup p P) (hnc : ¬ IsCyclic P)
    (hn : unipotent (K := F) ≤ normalizer (X : Set (Model F))) :
    X.pCoreIn 2 = unipotent (K := F) := by
  have hUX := unipotent_le_of_noncyclic_odd hp X P hXB hPX hP hnc hn
  apply le_antisymm
  · exact (isPGroup_pCoreIn 2 X).le_sylow_of_normalized sylow
      (hn.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  · exact le_pCoreIn_of_normalizes sylow.isPGroup' hUX
      (hXB.trans SylowNormalizer.normalizer_unipotent.symm.le)

/-- A soluble subgroup normalized by a specified Sylow has that Sylow as its two-core
when it contains a noncyclic odd-primary subgroup. -/
theorem twoCore_eq_sylow {p : ℕ} [Fact p.Prime] (hq : 2 < Nat.card F) (hp : Odd p)
    (X P : Subgroup (Model F)) [Group.IsSolvable X] (hPX : P ≤ X)
    (hP : IsPGroup p P) (hnc : ¬ IsCyclic P) (S : Sylow 2 (Model F))
    (hn : (S : Subgroup (Model F)) ≤ normalizer (X : Set (Model F))) :
    X.pCoreIn 2 = (S : Subgroup (Model F)) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model F) S (sylow (F := F))
  let c := MulAut.conj g
  have hS : (S : Subgroup (Model F)).map c.toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hg
  let Y := X.map c.toMonoidHom
  let B := P.map c.toMonoidHom
  have hUY : unipotent (K := F) ≤ normalizer (Y : Set (Model F)) := by
    rw [← hS,← map_equiv_normalizer_eq X c]
    exact map_mono hn
  let : Group.IsSolvable Y := Group.isSolvable_of_surjective
    (c.toMonoidHom.subgroupMap_surjective X)
  let : Group.IsNilpotent (unipotent (K := F)) := unipotent_isTwoGroup.isNilpotent
  let : Group.IsSolvable (Y ⊔ unipotent (K := F) : Subgroup (Model F)) :=
    Group.isSolvable_sup_of_normalizes Y unipotent hUY
  have hYB : Y ≤ borel := by
    rw [← SylowNormalizer.normalizer_unipotent]
    exact le_sup_left.trans (solvable_sylow_overgroup_normalizes hq sylow
      (Y ⊔ unipotent) le_sup_right inferInstance)
  have hc : ¬ IsCyclic B :=
    fun hc => hnc ((P.equivMapOfInjective c.toMonoidHom c.injective).isCyclic.mpr hc)
  have he := twoCore_eq_unipotent hp Y B hYB (map_mono hPX)
    (hP.map c.toMonoidHom) hc hUY
  apply (Subgroup.map_injective (f := c.toMonoidHom) c.injective)
  rw [map_pCoreIn_of_injective 2 X c.toMonoidHom c.injective,hS]
  exact he

omit [Finite F] [CharP F 2] in
/-- The split torus quotient kills the derived subgroup of the actual Borel. -/
theorem commutator_borel_le_unipotent :
    ⁅borel (K := F),borel (K := F)⁆ ≤ unipotent (K := F) := by
  apply commutator_le.mpr
  intro a ha b hb
  let x : borel (K := F) := ⟨a,ha⟩
  let y : borel (K := F) := ⟨b,hb⟩
  have he : EvenBorelTorus.projection ⁅x,y⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hm : ⁅x,y⁆ ∈ EvenBorelTorus.radical := by
    rw [← EvenBorelTorus.projection_ker]
    exact he
  exact hm

/-- The derived subgroup of a Sylow normalizer lies in the specified Sylow. -/
theorem commutator_sylow_normalizer_le (S : Sylow 2 (Model F)) :
    ⁅normalizer (S : Set (Model F)),normalizer (S : Set (Model F))⁆ ≤ (S : Subgroup (Model F)) := by
  obtain ⟨g,hU,hB⟩ := EvenBorelTorus.sylow_normalizer_conjugate S
  rw [← hB, ← map_commutator, ← hU]
  exact map_mono commutator_borel_le_unipotent

/-- Inner normalizers act trivially on the actual odd quotient. -/
theorem normalizer_commutator_le_twoCore {p : ℕ} [Fact p.Prime] (hq : 2 < Nat.card F) (hp : Odd p)
    (X P : Subgroup (Model F)) [Group.IsSolvable X] (hPX : P ≤ X)
    (hP : IsPGroup p P) (hnc : ¬ IsCyclic P) (S : Sylow 2 (Model F))
    (hn : (S : Subgroup (Model F)) ≤ normalizer (X : Set (Model F))) :
    ⁅normalizer (X : Set (Model F)),X⁆ ≤ X.pCoreIn 2 := by
  have he := twoCore_eq_sylow hq hp X P hPX hP hnc S hn
  have hnX := normalizer_le_normalizer_characteristic_image X (pCore 2 X)
  change normalizer (X : Set (Model F)) ≤ normalizer (X.pCoreIn 2 : Set (Model F)) at hnX
  rw [he] at hnX ⊢
  exact (commutator_mono hnX (X.le_normalizer.trans hnX)).trans
    (commutator_sylow_normalizer_le S)
end Atlas.G2.NoncyclicOddActor
