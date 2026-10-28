module
public import Theory.LinearAlgebra.BinaryMultiplicityGroups
public import Theory.Representation.FiniteFieldSemilinearDisplacement.TwoKernel
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.FieldComplement
public import Theory.Representation.BinaryOffender.Homogeneous.Embedding

/-!
# An invariant copy from the original semilinear multiplicity action

Every odd prime in a two-dimensional multiplicity group occurs in the actual
SL₂ component order. The source odd-rank bound excludes these primes from
[M:L₀]. A faithful multiplicity quotient of N_M(L) killing L₀ therefore has
a two-group coefficient kernel. Semilinear descent fixes a nonzero coefficient
vector, even when the full normalizer has odd field automorphisms.

The resulting copy is an actual L-Irr⁺ subspace of R₂(L₀T), lies in
[V_M,L], and is invariant under N_M(L). The original seed reconstruction
then supplies both orientations, stability, and full/local equality, with the
literal Hall-exponent application. Minimality also rules out an actual
embedding of two such copies: one invariant copy would already fill [V_M,L].

Source separation and construction of the displayed semilinear coordinates
remain with qt-d-10-nona5-central-hall-orders. These theorems do not assert
SeedAnalysisAt or the unconditional central Hall conclusion.
Source: Aschbacher--Smith D.3.21(3), 3.2.6, and 10.2.3,
printed pp.204--207,581,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- The faithful multiplicity image inherits the actual orbit index bound. -/
theorem multiplicity_card_dvd_orbit_index
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {A : Type*} [Group A] [Finite A]
    (q : ↥(D.maximalLocal ⊓ normalizer (L : Set G)) →* A)
    (hq : Function.Surjective q)
    (hkill : (localOrbit T L).subgroupOf (D.maximalLocal ⊓ normalizer (L : Set G)) ≤ q.ker) :
    Nat.card A ∣ ((localOrbit T L).subgroupOf D.maximalLocal).index := by
  have he : Nat.card A = q.ker.index := by
    rw [index_ker,MonoidHom.range_eq_top.mpr hq,Nat.card_congr (Subgroup.topEquiv.toEquiv)]
  rw [he]
  apply (index_dvd_of_le hkill).trans
  change (localOrbit T L).relIndex (D.maximalLocal ⊓ normalizer (L : Set G)) ∣ _
  rw [←relIndex_subgroupOf (H := localOrbit T L) (L := D.maximalLocal) inf_le_left]
  exact relIndex_dvd_index_of_le (subgroupOf_mono D.maximalLocal
    (le_inf (localOrbit T L).le_normalizer
      (source_nonnormal_orbit_le_normalizer D hn)))

/-- The original odd-rank restriction supplies the kernel needed by descent. -/
theorem multiplicity_fixed_vector
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    {A : Type*} [Group A] [Finite A]
    (q : ↥(D.maximalLocal ⊓ normalizer (L : Set G)) →* A)
    (hq : Function.Surjective q)
    (hkill : (localOrbit T L).subgroupOf (D.maximalLocal ⊓ normalizer (L : Set G)) ≤ q.ker)
    (μ : Representation (ZMod 2) A (Fin 2 → F)) (hμ : Function.Injective μ)
    (τ : A →* (F ≃+* F))
    (hsemi : ∀ a c v, μ a (c • v) = τ a c • μ a v) :
    ∃ c : Fin 2 → F, c ≠ 0 ∧ ∀ a, μ a c = c := by
  have hindex := multiplicity_card_dvd_orbit_index D hn q hq hkill
  let ν : Representation F τ.ker (Fin 2 → F) := {
    toFun a := {
      toFun := μ a
      map_add' := (μ a).map_add
      map_smul' := by
        intro c v
        rw [hsemi,MonoidHom.mem_ker.mp a.property]
        rfl }
    map_one' := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun μ.map_one v
    map_mul' a b := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun (μ.map_mul a b) v }
  have hν : Function.Injective ν.asGroupHom := by
    intro a b hh
    apply Subtype.ext
    apply hμ
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun (congrArg Units.val hh) v
  have hker : IsPGroup 2 τ.ker :=
    Theory.LinearAlgebra.BinaryMultiplicity.isPGroup_two_of_linearAut_embedding ν.asGroupHom hν
      (fun p hp hp2 hd => by
        let : Fact p.Prime := ⟨hp⟩
        have hL : p ∣ Nat.card (L ⧸ pCore 2 L) := by rwa [Nat.card_congr e.toEquiv]
        exact (HallGeometry.hall_component_orbit_index_coprime D hn e p hp2 hL).of_dvd_right
          (τ.ker.card_subgroup_dvd_card.trans hindex))
  exact Representation.FiniteFieldSemilinearDisplacement.exists_fixed_vector_of_two_kernel μ τ hsemi hker


/-- The semilinear multiplicity action constructs an invariant constituent
inside the literal moved module. The normalizer formula may include odd field
automorphisms; only its actual linear coefficient kernel is shown to be a two-group. -/
theorem exists_invariant_constituent_of_semilinear_multiplicity
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    {A E : Type*} [Group A] [Finite A] [AddCommGroup E]
    [Module (ZMod 2) E] [Module F E] [IsScalarTower (ZMod 2) F E]
    (q : ↥(D.maximalLocal ⊓ normalizer (L : Set G)) →* A)
    (hq : Function.Surjective q)
    (hkill : (localOrbit T L).subgroupOf (D.maximalLocal ⊓ normalizer (L : Set G)) ≤ q.ker)
    (μ : Representation (ZMod 2) A (Fin 2 → F)) (hμ : Function.Injective μ)
    (τ : A →* (F ≃+* F))
    (hsemi : ∀ a c v, μ a (c • v) = τ a c • μ a v)
    (σ : Representation (ZMod 2) L E) (hσ : IsIrrPlus σ ⊤ ⊤)
    (j : (Fin 2 → E) →ₗ[ZMod 2]
      Additive (ReducedNormal.ModuleGroup (localJoin T L)))
    (hj : Function.Injective j)
    (hjW : ReducedNormal.subspaceImage (localJoin T L) j.range ≤ ⁅D.fullModule,L⁆)
    (hL : ∀ (l : L) (c : Fin 2 → F) (v : E),
      j (fun i => c i • σ l v) =
        ReducedNormal.representation (localJoin T L)
          (inclusion ((le_componentOrbit L T).trans le_sup_left) l)
          (j (fun i => c i • v)))
    (β : ↥(D.maximalLocal ⊓ normalizer (L : Set G)) → E → E)
    (hN : ∀ (n : ↥(D.maximalLocal ⊓ normalizer (L : Set G))) (c : Fin 2 → F) (v : E),
      ((j (fun i => μ (q n) c i • β n v)).toMul.val : G) =
        (n : G) * ((j (fun i => c i • v)).toMul.val : G) * (n : G)⁻¹) :
    ∃ I : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup (localJoin T L))),
      IsIrrPlus (ReducedNormal.representation (localJoin T L))
        (L.subgroupOf (localJoin T L)) I ∧
      ReducedNormal.subspaceImage (localJoin T L) I ≤ ⁅D.fullModule,L⁆ ∧
      D.maximalLocal ⊓ normalizer (L : Set G) ≤
        normalizer (ReducedNormal.subspaceImage (localJoin T L) I : Set G) ∧
      Nat.card I = Nat.card E := by
  obtain ⟨c,hc,hcfix⟩ := multiplicity_fixed_vector D hn e q hq hkill μ hμ τ hsemi
  let f : E →ₗ[ZMod 2] (Fin 2 → E) := {
    toFun v i := c i • v
    map_add' v w := by ext i; exact smul_add _ _ _
    map_smul' a v := by ext i; exact smul_comm _ _ _ }
  have hf : Function.Injective f := by
    have hex : ∃ i, c i ≠ 0 := by
      by_contra! hh
      exact hc (funext hh)
    obtain ⟨i,hi⟩ := hex
    intro v w hh
    exact (smul_right_injective E hi) (congrFun hh i)
  let k := j.comp f
  let I := k.range
  have hk : Function.Injective k := hj.comp hf
  have hI : IsIrrPlus (ReducedNormal.representation (localJoin T L))
      (L.subgroupOf (localJoin T L)) I := by
    have hh := IsIrrPlus.map_equivariant_embedding σ
      (ReducedNormal.representation (localJoin T L))
      (inclusion ((le_componentOrbit L T).trans le_sup_left)) k
      (fun l v => hL l c v) hk hσ
    simpa only [←MonoidHom.range_eq_map,inclusion_range,Submodule.map_top] using hh
  have hIW : ReducedNormal.subspaceImage (localJoin T L) I ≤ ⁅D.fullModule,L⁆ := by
    apply (ReducedNormal.subspaceImage_mono _ ?_).trans hjW
    rintro x ⟨v,rfl⟩
    exact ⟨f v,rfl⟩
  have hmem (x : G) : x ∈ ReducedNormal.subspaceImage (localJoin T L) I ↔
      ∃ v : E, ((k v).toMul.val : G) = x := by
    constructor
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      obtain ⟨v,hv⟩ := hz
      exact ⟨v,congrArg (fun w => (w.toMul.val : G)) hv⟩
    · rintro ⟨v,rfl⟩
      exact ⟨(k v).toMul.val,⟨(k v).toMul,⟨v,rfl⟩,rfl⟩,rfl⟩
  refine ⟨I,hI,hIW,le_normalizer_iff.mpr ?_,?_⟩
  · intro n hn x hx
    obtain ⟨v,rfl⟩ := (hmem x).mp hx
    apply (hmem _).mpr
    refine ⟨β ⟨n,hn⟩ v,?_⟩
    have hh := hN ⟨n,hn⟩ c v
    rw [hcfix] at hh
    exact hh
  · exact (Nat.card_congr (LinearEquiv.ofInjective k hk).toEquiv).symm


/-- Actual coordinates for two copies of an L-Irr⁺ module. The quotient kills
L₀ inside the full component stabilizer; its faithful action on the coefficient
plane is semilinear. The last field is the literal ambient conjugation formula.
Existence of these coordinates is the two-copy source-analysis obligation. -/
structure SemilinearTwoCopyCoordinates (A E : Type*) [Group A] [Finite A]
    [AddCommGroup E] [Module (ZMod 2) E] [Module F E]
    [IsScalarTower (ZMod 2) F E] where
  quotient : ↥(D.maximalLocal ⊓ normalizer (L : Set G)) →* A
  onto : Function.Surjective quotient
  orbit_killed : (localOrbit T L).subgroupOf
    (D.maximalLocal ⊓ normalizer (L : Set G)) ≤ quotient.ker
  multiplicity : Representation (ZMod 2) A (Fin 2 → F)
  faithful : Function.Injective multiplicity
  coefficients : A →* (F ≃+* F)
  semilinear : ∀ a c v, multiplicity a (c • v) = coefficients a c • multiplicity a v
  model : Representation (ZMod 2) L E
  model_irrPlus : IsIrrPlus model ⊤ ⊤
  embedding : (Fin 2 → E) →ₗ[ZMod 2]
    Additive (ReducedNormal.ModuleGroup (localJoin T L))
  injective : Function.Injective embedding
  moved : ReducedNormal.subspaceImage (localJoin T L) embedding.range ≤ ⁅D.fullModule,L⁆
  component_action : ∀ (l : L) (c : Fin 2 → F) (v : E),
    embedding (fun i => c i • model l v) =
      ReducedNormal.representation (localJoin T L)
        (inclusion ((le_componentOrbit L T).trans le_sup_left) l)
        (embedding (fun i => c i • v))
  model_normalizer : ↥(D.maximalLocal ⊓ normalizer (L : Set G)) → E → E
  normalizer_action : ∀ (n : ↥(D.maximalLocal ⊓ normalizer (L : Set G)))
      (c : Fin 2 → F) (v : E),
    ((embedding (fun i => multiplicity (quotient n) c i • model_normalizer n v)).toMul.val : G) =
      (n : G) * ((embedding (fun i => c i • v)).toMul.val : G) * (n : G)⁻¹

/-- Semilinear descent and the actual odd-rank bound reconstruct the original
seed in the separated two-copy branch, retaining either seed orientation. -/
theorem separatedSeed_of_semilinear_two_copies
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    {A E : Type*} [Group A] [Finite A] [AddCommGroup E]
    [Module (ZMod 2) E] [Module F E] [IsScalarTower (ZMod 2) F E]
    (C : SemilinearTwoCopyCoordinates D (F := F) A E) : SeparatedSeed D t := by
  obtain ⟨I,hI,hIW,hstable,_⟩ := exists_invariant_constituent_of_semilinear_multiplicity
    D c.nonnormal e C.quotient C.onto C.orbit_killed C.multiplicity C.faithful
    C.coefficients C.semilinear C.model C.model_irrPlus C.embedding C.injective
    C.moved C.component_action C.model_normalizer C.normalizer_action
  exact separatedSeed_of_stabilizer_invariant_constituent D c ht htn hsep I hI hIW hstable

/-- The constructed invariant copy supplies the literal Hall exponent consumer.
Separation and source two-copy coordinates remain with this task's final assembly. -/
theorem hall_exponent_of_semilinear_two_copies
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    {A E : Type*} [Group A] [Finite A] [AddCommGroup E]
    [Module (ZMod 2) E] [Module F E] [IsScalarTower (ZMod 2) F E]
    (C : SemilinearTwoCopyCoordinates D (F := F) A E) :
    ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2 ^ n + 1 := by
  have hs := separatedSeed_of_semilinear_two_copies D c ht htn hsep e C
  obtain ⟨hmin,hcross⟩ :=
    (separatedSeed_iff_moved_minimal_and_crossed D c ht htn).mp hs
  exact hall_exponent_of_moved_minimal_and_crossed T D c hnot ht htn hmin hcross



/-- Two actual semilinearly mixed copies cannot occur in the original minimal
separated setup. Descent gives an invariant copy; minimality makes it the whole
moved subgroup, contradicting the embedding of two nonzero copies. -/
theorem no_semilinear_two_copies_of_separated
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    {A E : Type*} [Group A] [Finite A] [AddCommGroup E]
    [Module (ZMod 2) E] [Module F E] [IsScalarTower (ZMod 2) F E]
    (C : SemilinearTwoCopyCoordinates D (F := F) A E) : False := by
  obtain ⟨I,hI,hIW,hstable,hcard⟩ := exists_invariant_constituent_of_semilinear_multiplicity
    D c.nonnormal e C.quotient C.onto C.orbit_killed C.multiplicity C.faithful
    C.coefficients C.semilinear C.model C.model_irrPlus C.embedding C.injective
    C.moved C.component_action C.model_normalizer C.normalizer_action
  have he : ReducedNormal.subspaceImage (localJoin T L) I = ⁅D.fullModule,L⁆ :=
    (moved_minimal_under_component_stabilizer_of_seed_separated D c ht htn hsep
      _ hIW hstable).resolve_right
      (ReducedNormal.subspaceImage_ne_bot _ _ (hI.ne_bot _))
  have hle := Nat.card_le_card_of_injective
    (inclusion (C.moved.trans_eq he.symm)) (inclusion_injective _)
  have hi : Nat.card (ReducedNormal.subspaceImage (localJoin T L) I) = Nat.card I :=
    (Nat.card_congr (ReducedNormal.subspaceEquiv (localJoin T L) I).toEquiv).symm
  have hj : Nat.card (ReducedNormal.subspaceImage (localJoin T L) C.embedding.range) =
      Nat.card (Fin 2 → E) := by
    exact (Nat.card_congr
      (ReducedNormal.subspaceEquiv (localJoin T L) C.embedding.range).toEquiv).symm.trans
      (Nat.card_congr (LinearEquiv.ofInjective C.embedding C.injective).toEquiv).symm
  rw [hi,hj,hcard,Nat.card_fun,Nat.card_fin] at hle
  have hdiag : Function.Injective (fun v : E => C.embedding (fun _ : Fin 2 => v)) := by
    intro v w hh
    exact congrFun (C.injective hh) 0
  let : Finite E := Finite.of_injective _ hdiag
  obtain ⟨v,_,hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (C.model_irrPlus.ne_bot _)
  let : Nontrivial E := ⟨⟨v,0,hv⟩⟩
  have hcE : 1 < Nat.card E := Finite.one_lt_card
  nlinarith

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
