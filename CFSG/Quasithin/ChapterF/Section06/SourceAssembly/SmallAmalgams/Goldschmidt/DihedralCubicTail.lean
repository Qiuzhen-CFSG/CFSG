module

public import Theory.GroupTheory.PGroup.DihedralCubeAutomorphisms
public import Mathlib.GroupTheory.Sylow

/-!
# Excluding the symmetric-four product in Goldschmidt §2.15

The standard Sylow of S₄ × D₈^I × E is D₈^(Option I) × E. The distinguished
coordinate is the square Sylow in S₄. The invariant cube vertex supplied by
the dihedral cube theorem uses the normal Klein four at that coordinate;
its image is consequently ambient-normal and nontrivial. Conjugating an
arbitrary original Sylow into this standard Sylow transports the contradiction
through the supplied actual group isomorphism.

Source: Goldschmidt, Automorphisms of trivalent graphs (1980), §2.15, p.385.
-/

@[expose] public section
open Subgroup SymmetricFourWreath
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
namespace DihedralCubicTail

abbrev Ambient (I E : Type*) := S4 × ((I → D8) × E)
abbrev SylowModel (I E : Type*) := DihedralCubeAutomorphisms.Model (Option I) E

variable {I E : Type*} [Group E]

def embedding : SylowModel I E →* Ambient I E where
  toFun x := (square (x.1 none), (fun i => x.1 (some i), x.2))
  map_one' := by ext <;> simp
  map_mul' _ _ := by ext <;> simp

theorem embedding_injective : Function.Injective (embedding (I := I) (E := E)) := by
  intro x y h
  apply Prod.ext
  · funext i
    cases i with
    | none => exact square_injective (congrArg Prod.fst h)
    | some i => exact congrArg (fun z : Ambient I E => z.2.1 i) h
  · exact congrArg (fun z : Ambient I E => z.2.2) h

private instance mapped_plane_decidable (b : Bool) :
    DecidablePred (· ∈ (plane b).map square) := fun x =>
  inferInstanceAs (Decidable (∃ a, a ∈ plane b ∧ square a = x))

private theorem normal_plane : ((plane true).map square).Normal := by
  have hc : ∀ g : S4, ∀ a : D8, a ∈ plane true →
      ∃ b ∈ plane true, square b = g * square a * g⁻¹ := by decide +kernel
  constructor
  rintro _ ⟨a, ha, rfl⟩ g
  exact hc g a ha

private theorem family_image_normal [IsElementaryAbelian 2 E]
    (b : Option I → Bool) (hb : b none = true) :
    ((DihedralCubeAutomorphisms.family b).map
      (embedding (I := I) (E := E))).Normal := by
  have hc : ∀ (b : Bool) (a x : D8), x ∈ plane b → a * x * a⁻¹ ∈ plane b := by
    decide +kernel
  constructor
  rintro _ ⟨x, hx, rfl⟩ g
  obtain ⟨u, hu, he⟩ := normal_plane.conj_mem
    (square (x.1 none)) ⟨x.1 none, hb ▸ hx none, rfl⟩ g.1
  refine ⟨(fun i => match i with
    | none => u
    | some j => g.2.1 j * x.1 (some j) * (g.2.1 j)⁻¹, x.2), ?_, ?_⟩
  · intro i
    cases i with
    | none => change u ∈ plane (b none); rw [hb]; exact hu
    | some j => exact hc _ _ _ (hx _)
  · apply Prod.ext he
    change (fun j => g.2.1 j * x.1 (some j) * (g.2.1 j)⁻¹, x.2) =
      (g.2.1 * (fun j => x.1 (some j)) * g.2.1⁻¹, g.2.2 * x.2 * g.2.2⁻¹)
    apply Prod.ext
    · funext j; rfl
    · change x.2 = g.2.2 * x.2 * (g.2.2)⁻¹
      rw [IsMulCommutative.is_comm.comm (g.2.2) x.2, mul_assoc, mul_inv_cancel, mul_one]

private theorem family_ne_bot (b : Option I → Bool) :
    DihedralCubeAutomorphisms.family (E := E) b ≠ ⊥ := by
  classical
  let x : SylowModel I E := (Function.update 1 none (DihedralGroup.r 2), 1)
  have hx : x ∈ DihedralCubeAutomorphisms.family b := by
    intro i
    cases i with
    | none =>
        change DihedralGroup.r 2 ∈ plane (b none)
        cases b none <;> decide +kernel
    | some i =>
        change Function.update (1 : Option I → D8) none (DihedralGroup.r 2) (some i) ∈ _
        rw [Function.update_of_ne (by simp : some i ≠ (none : Option I))]
        change (1 : D8) ∈ _
        exact one_mem _
  intro he
  have hh : x = 1 := he.le hx
  have hh' : (DihedralGroup.r (2 : ZMod 4) : D8) = 1 := by
    simpa only [x, Function.update_self, Prod.fst_one, Pi.one_apply] using
      congrArg (fun z : SylowModel I E => z.1 none) hh
  exact (by decide +kernel : (DihedralGroup.r (2 : ZMod 4) : D8) ≠ 1) hh'

variable [Fintype I] [Finite E] [IsElementaryAbelian 2 E]

omit [IsElementaryAbelian 2 E] in
private theorem embedding_index : (embedding (I := I) (E := E)).range.index = 3 := by
  have hsize : Nat.card (Ambient I E) = 3 * Nat.card (SylowModel I E) := by
    simp only [Ambient, SylowModel, DihedralCubeAutomorphisms.Model,
      Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := S4),
      Fintype.card_perm, Fintype.card_fin, DihedralGroup.nat_card,
      Nat.card_eq_fintype_card (α := Option I), Fintype.card_option, pow_succ]
    norm_num [Nat.factorial]
    ring
  have hc : Nat.card (embedding (I := I) (E := E)).range = Nat.card (SylowModel I E) :=
    (Nat.card_congr (MonoidHom.ofInjective embedding_injective).toEquiv).symm
  have hh := (embedding (I := I) (E := E)).range.card_mul_index
  rw [hc, hsize] at hh
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := SylowModel I E))
    (hh.trans (mul_comm _ _))

private theorem model_isPGroup : IsPGroup 2 (SylowModel I E) := by
  obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  apply IsPGroup.of_card (n := 3 * (Fintype.card I + 1) + m)
  simp only [SylowModel, DihedralCubeAutomorphisms.Model, Nat.card_prod, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Option I), Fintype.card_option, DihedralGroup.nat_card,
    hm, show 2 * 4 = (2 : ℕ) ^ 3 by decide, ← pow_mul]
  rw [pow_add]

private noncomputable def standardSylow : Sylow 2 (Ambient I E) :=
  ((model_isPGroup (I := I) (E := E)).of_equiv
    (MonoidHom.ofInjective embedding_injective)).toSylow
    (by rw [embedding_index]; decide)

private theorem placement {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (e : G ≃* Ambient I E) :
    ∃ f : G ≃* Ambient I E,
      (P : Subgroup G).map f.toMonoidHom = (embedding (I := I) (E := E)).range := by
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Ambient I E) P' (standardSylow (I := I) (E := E))
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have hh := congrArg (fun Q : Sylow 2 (Ambient I E) => (Q : Subgroup (Ambient I E))) hg
  change ((P : Subgroup G).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at hh
  rw [map_map] at hh
  exact hh

/-- The symmetric-four product supplied by §2.14 is incompatible with the
original cubic automorphism and absence of invariant ambient-normal subgroups. -/
theorem exclude_model {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (e : G ≃* Ambient I E) (a : MulAut P) (ha : a ^ 3 = 1)
    (hno : ∀ K : Subgroup P, K.map a.toMonoidHom = K →
      (K.map (P : Subgroup G).subtype).Normal → K = ⊥) : False := by
  classical
  obtain ⟨f, hf⟩ := placement P e
  let ep : P ≃* SylowModel I E :=
    ((P : Subgroup G).equivMapOfInjective f.toMonoidHom f.injective).trans
      ((MulEquiv.subgroupCongr hf).trans
        (MonoidHom.ofInjective (embedding_injective (I := I) (E := E))).symm)
  have hep (x : P) : embedding (ep x) = f x := by
    change embedding ((MonoidHom.ofInjective embedding_injective).symm _) = _
    exact MonoidHom.apply_ofInjective_symm embedding_injective _
  let am : MulAut (SylowModel I E) := MulAut.congr ep a
  have ham : am ^ 3 = 1 := by
    dsimp only [am]
    rw [← map_pow, ha, map_one]
  obtain ⟨b, hb, hfix⟩ := DihedralCubeAutomorphisms.exists_invariant_family am ham none true
  let A : Subgroup (SylowModel I E) := DihedralCubeAutomorphisms.family b
  let K : Subgroup P := A.map ep.symm.toMonoidHom
  have hKA : K.map ep.toMonoidHom = A := by
    rw [map_map]
    have hh : ep.toMonoidHom.comp ep.symm.toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      exact ep.apply_symm_apply x
    rw [hh, map_id]
  have hKi : K.map a.toMonoidHom = K := by
    apply map_injective (f := ep.toMonoidHom) ep.injective
    rw [map_map, hKA]
    have hc : ep.toMonoidHom.comp a.toMonoidHom = am.toMonoidHom.comp ep.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      change ep (a x) = ep (a (ep.symm (ep x)))
      rw [ep.symm_apply_apply]
    rw [hc, ← map_map, hKA]
    exact hfix
  have himage : (K.map (P : Subgroup G).subtype).map f.toMonoidHom = A.map embedding := by
    have hc : f.toMonoidHom.comp (P : Subgroup G).subtype = embedding.comp ep.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact (hep x).symm
    rw [map_map, hc, ← map_map, hKA]
  have hn : (K.map (P : Subgroup G).subtype).Normal := by
    apply (MulEquiv.normal_map_iff (f := f)).mp
    change ((K.map (P : Subgroup G).subtype).map f.toMonoidHom).Normal
    rw [himage]
    exact family_image_normal b hb
  have he := hno K hKi hn
  have hA : A = ⊥ := by rw [← hKA, he, Subgroup.map_bot]
  exact family_ne_bot b hA

end DihedralCubicTail
end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
