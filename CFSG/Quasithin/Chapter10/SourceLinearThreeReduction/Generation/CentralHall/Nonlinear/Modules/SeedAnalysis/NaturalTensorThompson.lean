module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalTensorCorank
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson.KnownSimple
public import CFSG.Quasithin.ChapterB.Section02.RankLifting
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Embedding
public import Theory.GroupAction.NormalPChiefSeries.FixedCodimension

/-!
# Higher Thompson actors on the original nonseparated tensor module

The genuine ambient corank bound allows E.6.26 on the original H-star group.
If its generation parameter is at most j < n, J_j(T) moves the full module.
A member of the actual higher Thompson family therefore has a nontrivial
image in Aut_G(V_M). B.2.4 bounds its common fixed codimension by its image
rank plus j, while the full-module displacement estimate bounds it below by n.

A budget below 4n makes this actor preserve the unchanged seed. A budget below
2n makes its induced coefficient-field action trivial: a nontrivial field
twist moves at least half of the 4n-dimensional seed. Both estimates use the
actual full-module action and retain its pointwise kernel. The field-action
witness retains the exact O₂ quotient, both factor restrictions and twist.

The literal central Hall alternative consumes these results. They do not yet
prove that the seed equals the full module, that J_(n-2)(T) centralizes it,
or that the field action of every element of M is trivial. Those ambient
steps and the Cartan comparison remain required for the final exclusion.
Source: Aschbacher--Smith 9.2.1--5, printed pp.730--731, using B.2.4 and E.6.26;
10.1.1--2 and10.2.3, pp.741--742,745, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 ChapterE
open Representation.BinaryOffender.NaturalTensor
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary
local instance (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The actual action map from M to the full automizer. -/
@[expose] def originalFullAutomizerHom : D.maximalLocal →* Automizer D.fullModule :=
  D.fullModule.normalizerMonoidHom.rangeRestrict.comp
    (inclusion D.maximalLocal_normalizes_fullModule)

/-- M supplies every element of the actual full automizer. -/
theorem originalFullAutomizerHom_surjective : Function.Surjective (originalFullAutomizerHom D) := by
  intro a
  obtain ⟨m,hm⟩ := D.fullModule.normalizerMonoidHom.rangeRestrict_surjective a
  exact ⟨⟨m,(source_fullModule_normalizer D).le m.property⟩,hm⟩

private theorem full_le_maximal : D.fullModule ≤ D.maximalLocal :=
  D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer

/-- Its kernel is the pointwise centralizer of the literal full module in M. -/
theorem originalFullAutomizerHom_ker :
    (originalFullAutomizerHom D).ker =
      centralizer (D.fullModule.subgroupOf D.maximalLocal : Set D.maximalLocal) := by
  ext m
  constructor
  · intro hm v hv
    have he := congrArg (fun a : Automizer D.fullModule => a.val ⟨v,hv⟩) hm
    have hh := congrArg Subtype.val he
    change (m:G)*(v:G)*(m:G)⁻¹ = (v:G) at hh
    apply Subtype.ext
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hm
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    have he := congrArg Subtype.val (hm ⟨v,full_le_maximal D v.property⟩ v.property)
    change (v:G)*(m:G) = (m:G)*(v:G) at he
    change (m:G)*(v:G)*(m:G)⁻¹ = (v:G)
    rw [←he,mul_inv_cancel_right]

/-- Identity coordinates retain the original ambient action. -/
theorem originalFullAutomizerHom_action (m : D.maximalLocal) (v : Additive D.fullModule) :
    automizerRepresentation D.fullModule (originalFullAutomizerHom D m) v =
      originalFullAction D m v := rfl

/-- B.2.4 on the original full-module action, with the rank of its actual image. -/
theorem original_full_thompson_fixedCodim_bound
    (j : ℕ) (A : Subgroup D.maximalLocal)
    (hA : A ∈ ChapterB.thompsonFamily ((T : Subgroup G).subgroupOf D.maximalLocal) j)
    (hne : A.map (originalFullAutomizerHom D) ≠ ⊥) :
    fixedCodim (automizerRepresentation D.fullModule) (A.map (originalFullAutomizerHom D)) ≤
      rank (A.map (originalFullAutomizerHom D)) + j := by
  let U := D.fullModule.subgroupOf D.maximalLocal
  let : U.Normal := normal_subgroupOf_of_le_normalizer D.maximalLocal_normalizes_fullModule
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf (full_le_maximal D)
  let : IsElementaryAbelian 2 A := hA.2.1
  let e := subgroupOfEquivOfLe (full_le_maximal D)
  let E : Additive U ≃ₗ[ZMod 2] Additive D.fullModule :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
  let ρ := NoncentralChiefRefinement.normalRepresentation U
  have hE (m : D.maximalLocal) (v : Additive U) :
      E (ρ m v) = automizerRepresentation D.fullModule (originalFullAutomizerHom D m) (E v) := by
    rfl
  have hb := ChapterB.lemma_B_2_4_1 ((T : Subgroup G).subgroupOf D.maximalLocal)
    U A (fun _ hx => D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D) hx)
    hA.1 j (by rw [hA.2.2.2,Nat.log_pow (by decide : 1 < 2)]; rfl)
    (originalFullAutomizerHom D) (originalFullAutomizerHom_ker D) hne
  rw [←NoncentralChiefRefinement.normalRepresentation_fixedCodim_eq_rank_difference U A] at hb
  have he := fixedCodim_map_equivariant ρ (automizerRepresentation D.fullModule)
    (originalFullAutomizerHom D) E hE A
  change fixedCodim ρ A - j ≤ rank (A.map (originalFullAutomizerHom D)) at hb
  rw [he] at hb
  omega

/-- An H-star group generated below the field degree forces movement by the corresponding
higher Thompson subgroup of the prescribed Sylow group. -/
theorem original_even_thompson_moves_of_generation_le
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (j : ℕ) (hj : 0 < j) (hjn : j < n) (hgen : generationParameter H ≤ j) :
    ¬ ChapterB.thompsonJ (T : Subgroup G) j ≤ centralizer (D.fullModule : Set G) := by
  intro hJ
  have hTH : (T : Subgroup G) ≤ H := c.hstar.1.1.2
  have hs : ((T.subtype hTH : Sylow 2 H) : Subgroup H).map H.subtype = T :=
    map_subgroupOf_eq_of_le hTH
  have hr : (j : ℕ∞) < globalR D.fullModule :=
    (ENat.natCast_lt_natCast.mpr hjn).trans_le
      (original_even_full_globalR_ge D c n hn e ht htn hsep)
  have hh := Section06.FixedPointBounds.SylowThompson.source_E_6_26_knownSimple
    (original_full_hypothesisE61 D) hj H (T.subtype hTH)
    (Chapter3.sqtk_of_mem_H D.simpleQTKE c.hstar.1.1.1) hgen
    (by rw [hs]; exact inf_le_left) (by rw [hs]) hr (by rwa [hs])
  exact c.hstar.1.2 hh.1

/-- A low-generation original H-star group supplies a genuine nonzero elementary image
of a higher Thompson family in the full automizer, with both displacement bounds. -/
theorem original_even_exists_thompson_actor
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (j : ℕ) (hj : 0 < j) (hjn : j < n) (hgen : generationParameter H ≤ j) :
    ∃ A : Subgroup D.maximalLocal,
      A ∈ ChapterB.thompsonFamily ((T : Subgroup G).subgroupOf D.maximalLocal) j ∧
      IsElementaryTwo (A.map (originalFullAutomizerHom D)) ∧
      n ≤ fixedCodim (automizerRepresentation D.fullModule) (A.map (originalFullAutomizerHom D)) ∧
      fixedCodim (automizerRepresentation D.fullModule) (A.map (originalFullAutomizerHom D)) ≤
        rank (A.map (originalFullAutomizerHom D)) + j ∧
      n - j ≤ rank (A.map (originalFullAutomizerHom D)) := by
  have hm := original_even_thompson_moves_of_generation_le D c n hn e ht htn hsep j hj hjn hgen
  obtain ⟨C,hC,hmove⟩ : ∃ C ∈ ChapterB.thompsonFamily (T : Subgroup G) j,
      ¬ C ≤ centralizer (D.fullModule : Set G) := by
    by_contra! h
    exact hm (sSup_le h)
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_normalizer_componentOrbit L T
  have hCM := hC.1.trans hTM
  let A := C.subgroupOf D.maximalLocal
  have hA : A ∈ ChapterB.thompsonFamily ((T : Subgroup G).subgroupOf D.maximalLocal) j := by
    apply (ChapterB.thompsonFamily_map_iff_of_injective D.maximalLocal.subtype
      D.maximalLocal.subtype_injective _ A j).mp
    simpa only [A,map_subgroupOf_eq_of_le hCM,map_subgroupOf_eq_of_le hTM] using hC
  let : IsElementaryAbelian 2 A := hA.2.1
  have hne : A.map (originalFullAutomizerHom D) ≠ ⊥ := by
    intro hz
    apply hmove
    intro a ha v hv
    have hc : (⟨a,hCM ha⟩ : D.maximalLocal) ∈
        centralizer (D.fullModule.subgroupOf D.maximalLocal : Set D.maximalLocal) := by
      rw [←originalFullAutomizerHom_ker D]
      exact ((Subgroup.map_eq_bot_iff A).mp hz) ha
    exact congrArg Subtype.val (hc ⟨v,full_le_maximal D hv⟩ hv)
  have he : IsElementaryTwo (A.map (originalFullAutomizerHom D)) :=
    ⟨hne,IsElementaryAbelian.map _⟩
  have hb := original_full_thompson_fixedCodim_bound D j A hA hne
  let : FiniteDimensional (ZMod 2) (Additive D.fullModule) := Module.Finite.of_finite
  have hl := (original_even_full_localM_ge D c n hn e ht htn hsep).trans
    (moduleM_le_fixedCodim (automizerRepresentation D.fullModule) he)
  exact ⟨A,hA,he,hl,hb,by omega⟩


/-- A higher-Thompson actor whose full image budget is below the seed dimension
preserves the unchanged seed. No stability under all of M is inferred. -/
theorem original_even_thompson_actor_preserves_seed
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (j : ℕ) (A : Subgroup D.maximalLocal)
    (hA : A ∈ ChapterB.thompsonFamily ((T : Subgroup G).subgroupOf D.maximalLocal) j)
    (hne : A.map (originalFullAutomizerHom D) ≠ ⊥)
    (hsmall : rank (A.map (originalFullAutomizerHom D)) + j < 4*n) :
    A.map D.maximalLocal.subtype ≤ normalizer (D.seed : Set G) := by
  rintro _ ⟨a,ha,rfl⟩
  have hd := original_nonseparated_even_seed_finrank_eq D c n hn e ht htn hsep
  have hb := original_full_thompson_fixedCodim_bound D j A hA hne
  have hm := operatorFixedCodim_le_fixedCodim (automizerRepresentation D.fullModule)
    (A.map (originalFullAutomizerHom D)) (mem_map_of_mem _ ha)
  apply original_seed_stable_of_full_displacement_lt D c a
  have he : automizerRepresentation D.fullModule (originalFullAutomizerHom D a) =
      originalFullAction D a := rfl
  rw [he] at hm
  omega

/-- A seed-preserving element moving fewer than 2n full-module dimensions acts
trivially on the actual coefficient field in any of the marked determinant coordinates. -/
theorem original_even_seed_field_eq_one_of_small_full_displacement
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (f : Additive D.seed ≃ₗ[ZMod 2] ClassicalOrthogonal.FourPlusMatrix.Mat (F := GaloisField 2 n))
    (m : D.maximalLocal) (hs : (m:G) ∈ normalizer (D.seed : Set G))
    (ψ : GaloisField 2 n ≃+* GaloisField 2 n)
    (hψ : ∀ a v, f (originalSeedNormalizerAction D ⟨m,hs⟩ (f.symm (a • f v))) =
      ψ a • f (originalSeedNormalizerAction D ⟨m,hs⟩ v))
    (hsmall : operatorFixedCodim (originalFullAction D m) < 2*n) : ψ = 1 := by
  let R := originalSeedNormalizerAction D ⟨m,hs⟩
  let u := f.toLinearMap.comp (R.comp f.symm.toLinearMap)
  have hu (a : GaloisField 2 n)
      (v : ClassicalOrthogonal.FourPlusMatrix.Mat (F := GaloisField 2 n)) :
      u (a • v) = ψ a • u v := by
    have hh := hψ a (f.symm v)
    simpa only [u, R, LinearMap.comp_apply, LinearEquiv.coe_coe, f.apply_symm_apply] using hh
  have hd : Module.finrank (ZMod 2)
      (ClassicalOrthogonal.FourPlusMatrix.Mat (F := GaloisField 2 n)) = 4*n :=
    f.finrank_eq.symm.trans (original_nonseparated_even_seed_finrank_eq D c n hn e ht htn hsep)
  have he : operatorFixedCodim R = operatorFixedCodim u :=
    operatorFixedCodim_eq_of_equiv R u f (fun v => by
      change f (R v) = f (R (f.symm (f v)))
      rw [f.symm_apply_apply])
  have hb := original_seed_displacement_le_full D m hs
  apply RingEquiv.ext
  intro a
  by_contra ha
  have h := finrank_le_twice_operatorFixedCodim u ψ.toRingHom ⟨a,ha⟩ hu
  rw [hd,←he] at h
  change operatorFixedCodim R ≤ operatorFixedCodim (originalFullAction D m) at hb
  omega

/-- The same quotient and two factor markings with a field action of the entire
seed stabilizer whose restriction to the specified original actor is trivial. -/
@[expose] def OriginalEvenThompsonFieldKernel {t : G} (ht : t ∈ (T : Subgroup G))
    (n : ℕ) (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    (A : Subgroup D.maximalLocal) : Prop :=
    ∃ q : localOrbit T L →* SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n),
      Function.Surjective q ∧ q.ker = pCore 2 (localOrbit T L) ∧
      (∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ = (e (QuotientGroup.mk' _ l),1)) ∧
      (∀ l : L, q (originalConjugateOrbitInclusion ht l) = (1,e (QuotientGroup.mk' _ l))) ∧
      ∃ α : MulAut SL(2,GaloisField 2 n),
        ∃ f : Additive D.seed ≃ₗ[ZMod 2] ClassicalOrthogonal.FourPlusMatrix.Mat (F := GaloisField 2 n),
          (∀ g v, f (originalSeedAction D g v) =
            ClassicalOrthogonal.FourPlusMatrix.representation
              (ClassicalOrthogonal.FourPlusMatrix.NaturalTensor.marking α (q g)) (f v)) ∧
          ∃ φ : (D.maximalLocal ⊓ normalizer (D.seed : Set G) : Subgroup G) →*
              (GaloisField 2 n ≃+* GaloisField 2 n),
            (∀ (m : (D.maximalLocal ⊓ normalizer (D.seed : Set G) : Subgroup G)) a v,
              f (originalSeedNormalizerAction D ⟨m,m.property.2⟩ (f.symm (a • f v))) =
                φ m a • f (originalSeedNormalizerAction D ⟨m,m.property.2⟩ v)) ∧
            (∀ (a : D.maximalLocal) (_ha : a ∈ A),
              ∃ hs : (a:G) ∈ normalizer (D.seed : Set G), φ ⟨a,a.property,hs⟩ = 1)

/-- For a low-budget original Thompson actor, construct the marked determinant
coordinates and the full stabilizer field action, and prove that this actor lies in
its kernel. The homomorphism on the rest of the stabilizer is retained. -/
theorem original_even_thompson_actor_field_kernel
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (j : ℕ) (A : Subgroup D.maximalLocal)
    (hA : A ∈ ChapterB.thompsonFamily ((T : Subgroup G).subgroupOf D.maximalLocal) j)
    (hne : A.map (originalFullAutomizerHom D) ≠ ⊥)
    (hsmall : rank (A.map (originalFullAutomizerHom D)) + j < 2*n) :
    OriginalEvenThompsonFieldKernel D ht n e A := by
  obtain ⟨q,hq,hker,hl,hr,α,f,hf,φ,hφ⟩ :=
    original_even_seed_ambient_semilinear D c n hn e ht htn hsep
  refine ⟨q,hq,hker,hl,hr,α,f,hf,φ,hφ,?_⟩
  intro a ha
  have hs := original_even_thompson_actor_preserves_seed D c n hn e ht htn hsep
    j A hA hne (by omega) (mem_map_of_mem D.maximalLocal.subtype ha)
  refine ⟨hs,?_⟩
  apply original_even_seed_field_eq_one_of_small_full_displacement D c n hn e ht htn hsep
    f a hs (φ ⟨a,a.property,hs⟩) (hφ ⟨a,a.property,hs⟩)
  have hb := original_full_thompson_fixedCodim_bound D j A hA hne
  have hm := operatorFixedCodim_le_fixedCodim (automizerRepresentation D.fullModule)
    (A.map (originalFullAutomizerHom D)) (mem_map_of_mem _ ha)
  have he : automizerRepresentation D.fullModule (originalFullAutomizerHom D a) =
      originalFullAction D a := rfl
  rw [he] at hm
  omega

/-- The literal original H-star action forced by a generation parameter below n.
All ranks refer to its full automizer image; the original Sylow subgroup is retained. -/
@[expose] def OriginalEvenThompsonAnalysis (H : Subgroup G) {t : G}
    (ht : t ∈ (T : Subgroup G)) (n : ℕ)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)) : Prop :=
  ∀ j : ℕ, 0 < j → j < n → generationParameter H ≤ j →
    ∃ A : Subgroup D.maximalLocal,
      A ∈ ChapterB.thompsonFamily ((T : Subgroup G).subgroupOf D.maximalLocal) j ∧
      IsElementaryTwo (A.map (originalFullAutomizerHom D)) ∧
      n ≤ fixedCodim (automizerRepresentation D.fullModule) (A.map (originalFullAutomizerHom D)) ∧
      fixedCodim (automizerRepresentation D.fullModule) (A.map (originalFullAutomizerHom D)) ≤
        rank (A.map (originalFullAutomizerHom D)) + j ∧
      n - j ≤ rank (A.map (originalFullAutomizerHom D)) ∧
      (rank (A.map (originalFullAutomizerHom D)) + j < 4*n →
        A.map D.maximalLocal.subtype ≤ normalizer (D.seed : Set G)) ∧
      (rank (A.map (originalFullAutomizerHom D)) + j < 2*n →
        OriginalEvenThompsonFieldKernel D ht n e A)

/-- Construction of the original higher-Thompson actor, including its seed-stability
criterion, from the central Hall context alone. -/
theorem original_even_thompson_analysis
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) : OriginalEvenThompsonAnalysis D H ht n e := by
  intro j hj hjn hgen
  obtain ⟨A,hA,he,hl,hb,hr⟩ :=
    original_even_exists_thompson_actor D c n hn e ht htn hsep j hj hjn hgen
  exact ⟨A,hA,he,hl,hb,hr,
    original_even_thompson_actor_preserves_seed D c n hn e ht htn hsep j A hA he.1,
    original_even_thompson_actor_field_kernel D c n hn e ht htn hsep j A hA he.1⟩

/-- The original Hall alternative with the actual higher-Thompson actors.
The exact quotient, both factor markings, determinant field action and ambient bounds
are retained. The higher-Thompson centralization and Cartan exclusion remain to be proved. -/
theorem original_hall_conclusion_or_natural_tensor_thompson
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    (IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2^n+1) ∨
      ∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
        ∃ n : ℕ, 3 ≤ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n),
          ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
            D.seed ≤ centralizer (L : Set G)) ∧
          OriginalEvenNaturalTensorAnalysis D ht n e ∧
          OriginalEvenSeedDeterminantCoordinates D ht n e ∧
          n ≤ moduleM (normalizerRepresentation (originalSeedAction D)) ∧
          (∀ a : linearNormalizer (originalSeedAction D), a ≠ 1 →
            n ≤ operatorFixedCodim (normalizerRepresentation (originalSeedAction D) a)) ∧
          (∀ a : Automizer D.fullModule, a ≠ 1 →
            n ≤ operatorFixedCodim (automizerRepresentation D.fullModule a)) ∧
          n ≤ localM D.fullModule ∧
          (n : ℕ∞) ≤ globalR D.fullModule ∧
          (∀ U : Subgroup G, U ≤ D.fullModule → subgroupCorank D.fullModule U < n →
            centralizer (U : Set G) ≤ D.maximalLocal) ∧
          OriginalEvenThompsonAnalysis D H ht n e := by
  rcases original_hall_conclusion_or_natural_tensor_ambient D c with hh |
    ⟨t,ht,htn,n,hn,e,hs,ha,hdet,hm,hdisp,hfull,hl,hr,hcent⟩
  · exact Or.inl hh
  · exact Or.inr ⟨t,ht,htn,n,hn,e,hs,ha,hdet,hm,hdisp,hfull,hl,hr,hcent,
      original_even_thompson_analysis D c n hn e ht htn hs⟩

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
