module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.CubicModels
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.CubicFactors
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.SpecificGroups.BinaryLinear.SylowCubicDegree
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# The exact S3-or-S7 comparison for the G.6.4 conclusion

The actual Sylow-normalized cubic excludes the two-factor case. On the
remaining marked factor, the linear normalizer calculation forces GL(2,2),
and the permutation normalizer calculation forces S7. All original actor
and module maps are transported; the result is an isomorphism of the same
acting group. Both permutation-core rows are excluded by their actors.

This is the use of G.6.4 in C.5.12, Aschbacher–Smith, printed p.163.
It is a proved consequence of the explicit G.6.4 conclusion, not a producer
of that conclusion. The source-classification obligation remains separate.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterG.Section06
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {a : G}

theorem conclusion_models_of_normalized_inverted_cubic
    (h : Conclusion ρ a) (S : Sylow 2 G) (c : G)
    (hc : c ^ 3 = 1) (hcne : c ≠ 1)
    (hn : (S : Subgroup G) ≤ normalizer (zpowers c : Set G))
    (ha : a ^ 2 = 1) (hi : a * c = c ^ 2 * a)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (G ≃* Equiv.Perm (Fin 7)) := by
  have hone : OneFactor ρ a := by
    have hmain : OneFactor ρ a ∨ Nonempty (TwoFactors ρ a) := h.1
    rcases hmain with ho | hd
    · exact ho
    · obtain ⟨d⟩ := hd
      exact (d.toTwoFactorModules.not_sylow_normalizes_inverted_cubic S c hcne hi hn).elim
  have hm : FactorModel ρ ⊤ ⊤ := hone.2.2 ▸ hone.2.1
  rcases hm with ⟨n, _, _, e, E, stable, hE⟩ | ⟨n, hnlo, hnhi, e, E, stable, hE⟩ |
    ⟨n, hn6, e, E, stable, hE⟩
  · let eg : G ≃* BinaryLinear.GL (Fin n → ZMod 2) := (topEquiv.symm).trans e
    let ev : V ≃ₗ[ZMod 2] (Fin n → ZMod 2) := (Submodule.topEquiv).symm.trans E
    have hev : ∀ g v, ev (ρ g v) = eg g (ev v) := by
      intro g v
      exact hE ⟨g, mem_top g⟩ ⟨v, Submodule.mem_top⟩
    have hn := binary_model_degree_of_normalized_cubic ρ S c a hc hcne hn ha hi ht eg ev hev
    subst n
    exact Or.inl ⟨eg.trans ((BinaryLinear.OuterCyclic.slEquivLinear 2).symm.trans
      (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three))⟩
  · let eg : G ≃* Equiv.Perm (Fin n) := (topEquiv.symm).trans e
    have hn := symmetric_model_degree_of_normalized_cubic S c hc hcne hn hnlo hnhi eg
    obtain ⟨rfl, _⟩ := hn
    exact Or.inr ⟨eg⟩
  · let eg : G ≃* Equiv.Perm (Fin n) := (topEquiv.symm).trans e
    have hlo : 5 ≤ n := by omega
    have hhi : n ≤ 8 := by omega
    have hn := (symmetric_model_degree_of_normalized_cubic S c hc hcne hn hlo hhi eg).1
    omega
/-- The actor alone excludes higher binary degrees, independently of its
particular natural, repeated, or dual representation. -/
theorem binary_actor_degree_of_normalized_cubic
    (S : Sylow 2 G) (c : G) (hc : c ^ 3 = 1) (hcne : c ≠ 1)
    (hn : (S : Subgroup G) ≤ normalizer (zpowers c : Set G))
    {n : ℕ} (hnd : 2 ≤ n) (e : G ≃* BinaryLinear.GL (Fin n → ZMod 2)) : n = 2 := by
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hn' : (P : Subgroup (BinaryLinear.GL (Fin n → ZMod 2))) ≤
      normalizer (zpowers (e c) : Set (BinaryLinear.GL (Fin n → ZMod 2))) := by
    change (S : Subgroup G).map e.toMonoidHom ≤ _
    have heq : (zpowers c).map e.toMonoidHom = zpowers (e c) := by
      simpa only [MulEquiv.coe_toMonoidHom] using MonoidHom.map_zpowers e.toMonoidHom c
    rw [← heq, ← map_equiv_normalizer_eq]
    exact map_mono hn
  have hd := BinaryLinear.finrank_eq_two_of_sylow_normalizes_cubic
    (by simpa using (show 1 < n by omega)) P (e c)
    (by rw [← map_pow, hc, map_one])
    (fun he => hcne (e.injective (he.trans e.map_one.symm))) hn'
  simpa using hd
end CFSG.Quasithin.ChapterG.Section06
