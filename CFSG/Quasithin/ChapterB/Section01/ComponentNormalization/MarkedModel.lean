module

public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.QuadraticSource

public import Theory.GroupTheory.GeneralizedFitting.TwoSimpleFactors

/-!
# Marking the original component in the quadratic quotient

Conjugating the actual quotient model marks the original component as its first
factor. The component calculus then proves that its four-group orbit has exactly
two members. These are the literal quotient and orbit conventions used by the
normalizer-action and odd-commutator arguments in GLS2, Theorem 26.24.
-/

public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.ChapterB.ComponentNormalization.QuadraticSource
open Representation.QuadraticFourGroup
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}

theorem exists_marked_model (h : Hypotheses ρ L B a) :
    ∃ M : TwoFactorModel (componentOrbit L B),
      ∃ f : L →* Factor M.n, Function.Surjective f ∧ f.ker = center L ∧
        ∀ l : L, M.projection ⟨l,le_componentOrbit L B l.property⟩ = (f l,1) := by
  classical
  obtain ⟨M₀⟩ := twoFactorModel h
  obtain ⟨b,hb⟩ := SectionReduction.exists_model_component_marking h M₀
  let E := componentOrbit L B
  let α := h.orbitConjugation b
  let αq : E ⧸ pCore 2 E ≃* E ⧸ pCore 2 E :=
    QuotientGroup.congr _ _ α (pCore_map_iso 2 α)
  let M : TwoFactorModel E := {
    n := M₀.n
    one_lt := M₀.one_lt
    quotientEquiv := αq.trans M₀.quotientEquiv }
  have hπ (x : E) : M.projection x = M₀.projection (α x) := by
    rfl
  let ι : L →* E := inclusion (le_componentOrbit L B)
  let f : L →* Factor M.n := (MonoidHom.fst _ _).comp (M.projection.comp ι)
  have hpair (l : L) : M.projection (ι l) = (f l,1) := by
    have hx : α (ι l) ∈ (L.map (MulAut.conj (b : G)).toMonoidHom).subgroupOf E :=
      mem_map_of_mem _ l.property
    have hy := mem_map_of_mem M₀.projection hx
    rw [hb] at hy
    obtain ⟨z,hz⟩ := hy
    rw [← hπ] at hz
    apply Prod.ext
    · rfl
    · simpa only [MonoidHom.inl_apply] using congrArg Prod.snd hz.symm
  have hf : Function.Surjective f := by
    intro z
    have hz : (z,1) ∈ (MonoidHom.inl (Factor M₀.n) (Factor M₀.n)).range := ⟨z,rfl⟩
    rw [← hb] at hz
    obtain ⟨x,hx,hxz⟩ := hz
    obtain ⟨l,hl,hlx⟩ := hx
    have hlx' : α (ι ⟨l,hl⟩) = x := Subtype.ext hlx
    refine ⟨⟨l,hl⟩, ?_⟩
    change (M.projection (ι ⟨l,hl⟩)).1 = z
    rw [hπ, hlx', hxz]
  let := h.component.2
  let : Group.IsPerfect (Factor M.n) := Group.IsPerfect.ofSurjective hf
  let : IsSimpleGroup (Factor M.n) := by
    apply Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
    rw [GaloisField.card 2 M.n (by have := M.one_lt; omega)]
    exact (show 4 = 2 ^ 2 by rfl).le.trans
      (Nat.pow_le_pow_right (by decide) (by have := M.one_lt; omega))
  have hz : center (Factor M.n) = ⊥ := by
    rcases (inferInstance : (center (Factor M.n)).Normal).eq_bot_or_eq_top with hh | hh
    · exact hh
    · exact (Group.IsPerfect.not_isMulCommutative (Factor M.n)
        (center_eq_top_iff.mp hh)).elim
  have hk : f.ker = center L := by
    apply le_antisymm
    · rcases IsQuasisimple.normal_le_center_or_eq_top f.ker with hh | hh
      · exact hh
      · obtain ⟨z,hz1⟩ := exists_ne (1 : Factor M.n)
        obtain ⟨l,rfl⟩ := hf z
        have hl : l ∈ f.ker := hh.symm ▸ mem_top l
        exact (hz1 (MonoidHom.mem_ker.mp hl)).elim
    · intro l hl
      have hfc : f l ∈ center (Factor M.n) := by
        apply mem_center_iff.mpr
        intro z
        obtain ⟨k,rfl⟩ := hf z
        simpa only [map_mul] using congrArg f (mem_center_iff.mp hl k)
      apply MonoidHom.mem_ker.mpr
      simpa only [hz,mem_bot] using hfc
  exact ⟨M,f,hf,hk,hpair⟩

omit [FiniteDimensional (ZMod 2) V] in
lemma orbit_conjugate_cases (h : Hypotheses ρ L B a)
    (M : TwoFactorModel (componentOrbit L B)) (b : B) :
    L.map (MulAut.conj (b : G)).toMonoidHom = L ∨
      L.map (MulAut.conj (b : G)).toMonoidHom = L.map (MulAut.conj a).toMonoidHom := by
  let E := componentOrbit L B
  let C : B → Subgroup E := fun b =>
    (L.map (MulAut.conj (b : G)).toMonoidHom).subgroupOf E
  have hce (b : B) : L.map (MulAut.conj (b : G)).toMonoidHom ≤ E :=
    le_iSup (fun c : B => L.map (MulAut.conj (c : G)).toMonoidHom) b
  have hC (b : B) : IsComponent E (C b) :=
    (h.component.map_conj b).subgroupOf (hce b)
  have hker : IsPGroup 2 M.projection.ker := M.ker_projection ▸ pCore_isPGroup
  have hne (b : B) : (C b).map M.projection ≠ ⊥ :=
    (hC b).map_ne_bot_of_twoGroup_kernel M.projection hker
  have hI (b : B) : IsComponent (Factor M.n × Factor M.n) ((C b).map M.projection) :=
    ((hC b).map_surjective M.projection M.projection_surjective).resolve_left (hne b)
  let : Group.IsPerfect E := h.orbit_properties.1
  let : Group.IsPerfect (Factor M.n) := Group.IsPerfect.ofSurjective
    (f := (MonoidHom.fst _ _).comp M.projection)
    (Prod.fst_surjective.comp M.projection_surjective)
  let : IsSimpleGroup (Factor M.n) := by
    apply Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
    rw [GaloisField.card 2 M.n (by have := M.one_lt; omega)]
    exact (show 4 = 2 ^ 2 by rfl).le.trans
      (Nat.pow_le_pow_right (by decide) (by have := M.one_lt; omega))
  have hz : center (Factor M.n) = ⊥ := by
    rcases (inferInstance : (center (Factor M.n)).Normal).eq_bot_or_eq_top with hh | hh
    · exact hh
    · exact (Group.IsPerfect.not_isMulCommutative (Factor M.n)
        (center_eq_top_iff.mp hh)).elim
  let : IsQuasisimple (Factor M.n) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hreflect {b c : B} (he : (C b).map M.projection = (C c).map M.projection) :
      L.map (MulAut.conj (b : G)).toMonoidHom = L.map (MulAut.conj (c : G)).toMonoidHom := by
    have hh := (hC b).eq_of_map_eq (hC c) M.projection he (hne b)
    have hm := congrArg (Subgroup.map E.subtype) hh
    simpa only [C, map_subgroupOf_eq_of_le (hce b), map_subgroupOf_eq_of_le (hce c)] using hm
  have hone : L.map (MulAut.conj ((1 : B) : G)).toMonoidHom = L := by
    convert L.map_id using 1
    ext x
    simp
  have hdistinct : (C (1 : B)).map M.projection ≠ (C ⟨a,h.mem⟩).map M.projection := by
    intro he
    apply h.moves
    have hh := hreflect he
    simpa only [hone] using hh.symm
  have hc0 := (hI (1 : B)).prod_cases hz
  have hc1 := (hI ⟨a,h.mem⟩).prod_cases hz
  have hcb := (hI b).prod_cases hz
  have heq : (C b).map M.projection = (C (1 : B)).map M.projection ∨
      (C b).map M.projection = (C ⟨a,h.mem⟩).map M.projection := by
    rcases hc0 with h0 | h0 <;> rcases hc1 with h1 | h1 <;> rcases hcb with hb | hb
    all_goals first | exact False.elim (hdistinct (h0.trans h1.symm)) | exact Or.inl (hb.trans h0.symm) | exact Or.inr (hb.trans h1.symm)
  rcases heq with he | he
  · left
    simpa only [hone] using hreflect he
  · exact Or.inr (hreflect he)
end CFSG.Quasithin.ChapterB.ComponentNormalization.QuadraticSource
