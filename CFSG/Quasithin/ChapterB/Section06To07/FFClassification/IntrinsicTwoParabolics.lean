module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.IntrinsicParabolics
/-!
# Two-power invariant parabolics in the original normal supplement

Only automorphisms induced by the original Sylow are used in the intrinsic
parabolic lift. Those automorphisms have two-power order. Retaining this
fact allows the actual Ree parabolic theorem to supply both invariant proper
overgroups, without assuming invariance under all automorphisms.

Source: Aschbacher–Smith E.2.2, printed pp.215–216. The literal Sylow
intersection, normal subgroup, and two embedded parabolics are retained.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterB
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]
/-- The same marked pair is invariant under the original ambient Sylow. -/
theorem exists_sylow_invariant_twoPower_parabolics
    (T : Sylow 2 G) (L : Subgroup G) [L.Normal] (e₀ : L ≃* D)
    (U : Sylow 2 D) (P₀ Q₀ : Subgroup D)
    (hjoin : P₀ ⊔ Q₀ = ⊤) (hp : P₀ ≠ ⊤) (hq : Q₀ ≠ ⊤)
    (hUP : (U : Subgroup D) ≤ P₀) (hUQ : (U : Subgroup D) ≤ Q₀)
    (hinvariant : ∀ a : MulAut D, (∃ n : ℕ, a^(2^n)=1) →
      (U : Subgroup D).map a.toMonoidHom = U →
      P₀.map a.toMonoidHom = P₀ ∧ Q₀.map a.toMonoidHom = Q₀) :
    ∃ P Q : Subgroup G, P ⊔ Q = L ∧ P ≠ L ∧ Q ≠ L ∧
      (T : Subgroup G) ≤ normalizer (P : Set G) ∧
      (T : Subgroup G) ≤ normalizer (Q : Set G) ∧
      L ⊓ (T : Subgroup G) ≤ P ∧ L ⊓ (T : Subgroup G) ≤ Q := by
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_normal L
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq D U (S.mapSurjective (f := e₀.toMonoidHom) e₀.surjective)
  have hg := congrArg Sylow.toSubgroup hg
  change (U : Subgroup D).map (MulAut.conj g).toMonoidHom =
    (S : Subgroup L).map e₀.toMonoidHom at hg
  let e := e₀.trans (MulAut.conj g).symm
  have hmark : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom = U := by
    rw [← hS]
    change (S : Subgroup L).map ((MulAut.conj g).symm.toMonoidHom.comp e₀.toMonoidHom) = _
    rw [← map_map, ← hg]
    exact (MulAut.conj g).mapSubgroup.symm_apply_apply _
  have hacts (t : T) :
      (U : Subgroup D).map
        (MulAut.congr e (MulAut.conjNormal (t : G))).toMonoidHom = (U : Subgroup D) := by
    have ht : ((T : Subgroup G).subgroupOf L).map (MulAut.conjNormal (t : G)).toMonoidHom =
        (T : Subgroup G).subgroupOf L := by
      apply le_antisymm
      · rintro x ⟨y,hy,rfl⟩
        change (t : G) * (y : G) * (t : G)⁻¹ ∈ (T : Subgroup G)
        exact T.mul_mem (T.mul_mem t.property hy) (T.inv_mem t.property)
      · intro x hx
        refine ⟨MulAut.conjNormal ((t : G)⁻¹) x, ?_, ?_⟩
        · change (((MulAut.conjNormal ((t : G)⁻¹)) x : L) : G) ∈ (T : Subgroup G)
          rw [MulAut.conjNormal_apply, inv_inv]
          exact T.mul_mem (T.mul_mem (T.inv_mem t.property) hx) t.property
        · apply Subtype.ext
          change (((MulAut.conjNormal (t : G))
            ((MulAut.conjNormal ((t : G)⁻¹)) x) : L) : G) = x
          simp only [MulAut.conjNormal_apply, inv_inv]
          group
    have he : (MulAut.congr e (MulAut.conjNormal (t : G))).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp (MulAut.conjNormal (t : G)).toMonoidHom := by
      ext x
      simp [MulAut.congr_apply]
    rw [← hmark, map_map, he, ← map_map, ht]
  let f : D →* G := L.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
  have hftop : (⊤ : Subgroup D).map f = L := by
    rw [show f = L.subtype.comp e.symm.toMonoidHom from rfl, ← map_map,
      map_top_of_surjective _ e.symm.surjective, ← MonoidHom.range_eq_map, range_subtype]
  let P := P₀.map f
  let Q := Q₀.map f
  have hPQ : P ⊔ Q = L := by
    rw [show P = P₀.map f from rfl,
      show Q = Q₀.map f from rfl, ← Subgroup.map_sup,
      hjoin, hftop]
  have hP : P ≠ L := by
    intro he
    exact hp (map_injective hf (he.trans hftop.symm))
  have hQ : Q ≠ L := by
    intro he
    exact hq (map_injective hf (he.trans hftop.symm))
  have hnorm (D : Subgroup D)
      (hd : ∀ t : T, D.map (MulAut.congr e (MulAut.conjNormal (t : G))).toMonoidHom = D) :
      (T : Subgroup G) ≤ normalizer ((D.map f) : Set G) := by
    apply le_normalizer_iff.mpr
    intro t ht x hx
    obtain ⟨y,hy,rfl⟩ := hx
    let a := MulAut.congr e (MulAut.conjNormal t)
    have hay : a y ∈ D := by
      rw [← hd ⟨t,ht⟩]
      exact mem_map_of_mem _ hy
    refine ⟨a y,hay,?_⟩
    simp [f,a,MulAut.congr_apply,MulAut.conjNormal_apply]
  have hpower (t : T) : ∃ n : ℕ,
      (MulAut.congr e (MulAut.conjNormal (t : G)))^(2^n)=1 := by
    obtain ⟨n,hn⟩ := T.isPGroup' t
    refine ⟨n,?_⟩
    rw [←map_pow,←map_pow,show (t : G)^(2^n)=1 from congrArg Subtype.val hn,map_one,map_one]
  have hflags (t : T) := hinvariant (MulAut.congr e (MulAut.conjNormal (t : G)))
    (hpower t) (hacts t)
  have hint (R : Subgroup D) (hd : (U : Subgroup D) ≤ R) :
      L ⊓ (T : Subgroup G) ≤ R.map f := by
    rintro x ⟨hxL,hxT⟩
    have hx : e ⟨x,hxL⟩ ∈ (U : Subgroup D) := by
      rw [← hmark]
      exact mem_map_of_mem _ hxT
    refine ⟨e ⟨x,hxL⟩, hd hx, ?_⟩
    simp [f]
  exact ⟨P,Q,hPQ,hP,hQ,
    (hnorm _ fun t => (hflags t).1), (hnorm _ fun t => (hflags t).2),
    (hint _ hUP),
    (hint _ hUQ)⟩

/-- An intrinsic invariant parabolic pair excludes minimal parabolicity upstairs. -/
theorem not_minimalParabolic_of_twoPower_parabolics
    (T : Sylow 2 G) (L : Subgroup G) [L.Normal] (e : L ≃* D)
    (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (U : Sylow 2 D) (P Q : Subgroup D)
    (hjoin : P ⊔ Q = ⊤) (hp : P ≠ ⊤) (hq : Q ≠ ⊤)
    (hUP : (U : Subgroup D) ≤ P) (hUQ : (U : Subgroup D) ≤ Q)
    (hinvariant : ∀ a : MulAut D, (∃ n : ℕ, a^(2^n)=1) →
      (U : Subgroup D).map a.toMonoidHom = U →
      P.map a.toMonoidHom = P ∧ Q.map a.toMonoidHom = Q) :
    ¬ IsMinimalParabolicOver T ⊤ := by
  obtain ⟨A,B,hAB,hA,hB,hnA,hnB,hiA,hiB⟩ :=
    exists_sylow_invariant_twoPower_parabolics T L e U P Q hjoin hp hq hUP hUQ hinvariant
  exact not_minimalParabolic_of_two_overgroups T L A B hgen hAB hA hB hnA hnB hiA hiB
end CFSG.Quasithin.ChapterB
