module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks.Overgroup
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport
public import Stellmacher.ElementaryAbelianMaxJ

/-!
# Conjugating the complete solvable E.6.7 decomposition

An automorphism preserving Q, M, V and H transports every block, its
relative subnormality, the set product and the Thompson commutator identity.
The actual alternating quotient and conjugation module are transported along
induced isomorphisms; relative indices preserve both action coranks and
intersection indices. Solvability excludes the even-field rank-one types.
Thus a selected block can be conjugated without dropping any E.6.7 clause.

The private module transport is adapted from
`Hyperplanes/Enlargement/BlockInspection/Transport.lean`; keeping the small
construction here avoids importing that later assembly into the E.6.8 proof.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7,
C.1.12 and E.6.7–8, printed pp.123–124 and 246–248.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks
open ChapterC InvariantSubspaces.BlockSelection
variable {A B : Type*} [Group A] [Group B]

private theorem transport_blockU (e : A ≃* B) :
    (blockU A).map e.toMonoidHom = blockU B := by
  rw [blockU, map_commutator, pCore_map_iso,
    map_top_of_surjective _ e.surjective, blockU]

private def blockUEquiv (e : A ≃* B) : blockU A ≃* blockU B :=
  (e.subgroupMap (blockU A)).trans (MulEquiv.subgroupCongr (transport_blockU e))

private theorem transport_blockFixed (e : A ≃* B) :
    (blockFixed A).map (blockUEquiv e).toMonoidHom = blockFixed B := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.centerCongr e ⟨x, hx⟩).property
  · intro x hx
    exact ⟨(blockUEquiv e).symm x,
      (Subgroup.centerCongr e).symm ⟨x, hx⟩ |>.property,
      (blockUEquiv e).apply_symm_apply x⟩

private def coreQuotientEquiv (e : A ≃* B) :
    (A ⧸ pCore 2 A) ≃* (B ⧸ pCore 2 B) :=
  QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

private def blockModuleEquiv (e : A ≃* B) : BlockModule A ≃* BlockModule B :=
  QuotientGroup.congr _ _ (blockUEquiv e) (transport_blockFixed e)

private theorem blockUEquiv_conjugate (e : A ≃* B) (a : A) (u : blockU A) :
    blockUEquiv e (blockConjugate A a u) =
      blockConjugate B (e a) (blockUEquiv e u) := by
  apply Subtype.ext
  change e (a * (u : A) * a⁻¹) = e a * e (u : A) * (e a)⁻¹
  simp only [map_mul, map_inv]

/-- Pull back the actual core quotient and conjugation module along an isomorphism. -/
private def pullbackModel {X V : Type*} [Group X] [Group V]
    {rho : X →* MulAut V} (model : BlockModuleModel A rho) (e : B ≃* A) :
    BlockModuleModel B rho where
  quotientIso := (coreQuotientEquiv e).trans model.quotientIso
  moduleIso := (blockModuleEquiv e).trans model.moduleIso
  intertwining b u := by
    change model.moduleIso (QuotientGroup.mk' (blockFixed A)
      (blockUEquiv e (blockConjugate B b u))) =
      rho (model.quotientIso (QuotientGroup.mk' (pCore 2 A) (e b)))
        (model.moduleIso (QuotientGroup.mk' (blockFixed A) (blockUEquiv e u)))
    rw [blockUEquiv_conjugate]
    exact model.intertwining (e b) (blockUEquiv e u)

/-- The full equivariant linear model is invariant under group isomorphism. -/
private theorem linearModel_of_equiv {X V k : Type*} [Group X]
    [AddCommGroup V] [Semiring k] [Module k V]
    {pi : Representation k X V} (h : IsLinearBlockModel A pi) (e : A ≃* B) :
    IsLinearBlockModel B pi := by
  obtain ⟨rho, ⟨model⟩, hpi⟩ := h
  exact ⟨rho, ⟨pullbackModel model e.symm⟩, hpi⟩

private theorem alternating_of_equiv {m : ℕ} (h : IsAlternatingBlock A m)
    (e : A ≃* B) : IsAlternatingBlock B m :=
  ⟨h.1, h.2.1.of_mulEquiv e, linearModel_of_equiv h.2.2 e⟩

private theorem not_rankOne_of_solvable {X : Type*} [Group X]
    [Group.IsSolvable X] {n : ℕ} (hx : IsL2EvenBlock X n) : False := by
  obtain ⟨hn, hshort, F, _, _, hF, hpsl, _⟩ := hx
  obtain ⟨E, _, _, hE, ⟨e⟩⟩ := hpsl
  let : Finite X := hshort.finite
  let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three E (by
      rw [hE]
      have hh : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      omega)
  let : Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact Group.IsPerfect.not_isSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E)
    inferInstance

variable {G : Type*} [Group G]

/-- Transport a selected block together with the complete solvable E.6.7
family under an automorphism preserving the ambient parameters. -/
theorem exists_conjugate_decomposition {Q M V W H : Subgroup G}
    [Group.IsSolvable H] (d : E67Decomposition Q M V W H)
    (hthree : ∀ i, IsAlternatingBlock (d.block i) 3)
    (e : G ≃* G) (hQ : Q.map e.toMonoidHom = Q)
    (hM : M.map e.toMonoidHom = M) (hV : V.map e.toMonoidHom = V)
    (hH : H.map e.toMonoidHom = H) (i : Fin d.count) :
    ∃ d' : E67Decomposition Q M V W H, ∃ j : Fin d'.count,
      d'.block j = (d.block i).map e.toMonoidHom := by
  let b := fun i => (d.block i).map e.toMonoidHom
  have hle (i) : b i ≤ H := hH ▸ map_mono (d.le i)
  have htype (i) : IsAlternatingBlock (b i) 3 :=
    alternating_of_equiv (hthree i) (e.subgroupMap _)
  have hsub (i) : ((b i).subgroupOf H).IsSubnormal := by
    let f : H ≃* H := (e.subgroupMap H).trans (MulEquiv.subgroupCongr hH)
    have hf : ((d.block i).subgroupOf H).map f.toMonoidHom = (b i).subgroupOf H := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, heq⟩
        exact ⟨⟨y, d.le i hy⟩, hy, Subtype.ext heq⟩
    exact hf ▸ (d.subnormal i).map f.surjective
  have hinter (D : Subgroup G) :
      (D ⊓ M).map e.toMonoidHom = D.map e.toMonoidHom ⊓ M := by
    rw [map_inf _ _ _ e.injective, hM]
  have hfixed (D : Subgroup G) :
      (V ⊓ centralizer (D : Set G)).map e.toMonoidHom =
        V ⊓ centralizer (D.map e.toMonoidHom : Set G) := by
    rw [map_inf _ _ _ e.injective, hV, Theory.Quasithin.map_centralizer]
  have hgen : H = (H ⊓ M) ⊔ ⨆ i, b i := by
    have hh := congrArg (fun D : Subgroup G => D.map e.toMonoidHom) d.generated
    rwa [Subgroup.map_sup, hinter, hH, Subgroup.map_iSup] at hh
  have hprod : (H : Set G) = (H ⊓ M : Subgroup G) * (⨆ i, b i : Subgroup G) := by
    have hh := congrArg (fun D : Set G => e '' D) d.product
    rw [Set.image_mul] at hh
    change (H.map e.toMonoidHom : Set G) =
      ((H ⊓ M).map e.toMonoidHom : Set G) *
        ((⨆ i, d.block i).map e.toMonoidHom : Set G) at hh
    rwa [hinter, hH, Subgroup.map_iSup] at hh
  refine ⟨{
    count := d.count
    count_le_two := d.count_le_two
    block := b
    le := hle
    type := fun i => Or.inr (Or.inl (htype i))
    subnormal := hsub
    commuting := ?_
    generated := hgen
    product := hprod
    thompson := ?_
    alternating := ?_
    rankOne := ?_
  }, i, rfl⟩
  · intro i j hij
    have hh := map_mono (f := e.toMonoidHom) (d.commuting i j hij)
    rwa [Theory.Quasithin.map_centralizer] at hh
  · intro i
    have hj : (Stellmacher.elementaryAbelianMaxJ Q).map e.toMonoidHom =
        Stellmacher.elementaryAbelianMaxJ Q := by
      rw [← Stellmacher.elementaryAbelianMaxJ_map_equiv, hQ]
    have hh := congrArg (fun D : Subgroup G => D.map e.toMonoidHom) (d.thompson i)
    rwa [map_commutator, hj] at hh
  · intro i n hn
    have ha := d.alternating i n (alternating_of_equiv hn (e.subgroupMap _).symm)
    refine ⟨?_, ?_, ha.2.2⟩
    · have hi := relIndex_map_map_of_injective (f := e.toMonoidHom)
        (V ⊓ centralizer (d.block i : Set G)) V e.injective
      rw [hfixed, hV] at hi
      exact (congrArg (Nat.log 2) hi).trans ha.1
    · rw [← hinter, relIndex_map_map_of_injective _ _ e.injective]
      exact ha.2.1
  · intro i n hn
    let : Group.IsSolvable (b i) :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective (hle i))
    exact (not_rankOne_of_solvable hn).elim

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks
